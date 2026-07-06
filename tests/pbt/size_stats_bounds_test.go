package pbt

import (
	"math/bits"
	"sync"
	"sync/atomic"
	"testing"

	"github.com/jeremiah-masters/dlht"

	"pgregory.net/rapid"
)

// Size/Stats relations, kept honest to the documented contract. Size()
// is approximate during activity (per-bin atomic, not snapshot), so the only
// sound claims are quiescent exactness and monotone sandwich bounds. The
// tempting "Size during activity equals live count" is not a valid relation
// and is deliberately absent.

// Quiescent exactness plus Stats internal consistency after a random
// sequential workload.
func TestPBTStatsQuiescentConsistency(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		initialSize := rapid.SampledFrom(initialSizeAxis).Draw(t, "initialSize")
		keyspace := rapid.IntRange(1, 64).Draw(t, "keyspace")
		opsLen := rapid.IntRange(0, 512).Draw(t, "opsLen")
		keyGen := GenUint64Key(keyspace)
		valGen := rapid.IntRange(-1_000_000, 1_000_000)
		ops := GenOpSequence(keyGen, valGen, MixChurn, opsLen, opsLen).Draw(t, "ops")

		m := dlht.New[uint64, int](dlht.Options{InitialSize: initialSize})
		model := make(map[uint64]int)
		for _, o := range ops {
			res := execOp(m, o)
			switch o.Kind {
			case OpInsert:
				if res.Found {
					model[o.Key] = o.Value
				}
			case OpPut:
				if res.Updated {
					model[o.Key] = o.Value
				}
			case OpDelete:
				if res.Found {
					delete(model, o.Key)
				}
			}
		}

		if got := m.Size(); got != uint64(len(model)) {
			t.Fatalf("quiescent Size()=%d, model has %d", got, len(model))
		}
		stats := m.Stats()
		if stats.Size != uint64(len(model)) {
			t.Fatalf("quiescent Stats().Size=%d, model has %d", stats.Size, len(model))
		}
		if stats.Resizing {
			t.Fatalf("Stats().Resizing=true at quiescence")
		}
		if bits.OnesCount64(stats.Bins) != 1 {
			t.Fatalf("Stats().Bins=%d is not a power of two", stats.Bins)
		}
		if stats.Capacity != stats.Bins*15 {
			t.Fatalf("Stats().Capacity=%d, want Bins*15=%d", stats.Capacity, stats.Bins*15)
		}
		if stats.Size > stats.Capacity {
			t.Fatalf("Stats().Size=%d exceeds Capacity=%d", stats.Size, stats.Capacity)
		}
		if stats.Links > stats.LinkCapacity {
			t.Fatalf("Stats().Links=%d exceeds LinkCapacity=%d", stats.Links, stats.LinkCapacity)
		}
		if wantLF := float64(stats.Size) / float64(stats.Capacity); stats.LoadFactor != wantLF {
			t.Fatalf("Stats().LoadFactor=%v, want Size/Capacity=%v", stats.LoadFactor, wantLF)
		}
	})
}

// Monotone sandwich: under an insert-only phase every concurrent Size()
// sample lies in [size_before, size_after]; under a delete-only phase (which
// never triggers a resize) in [size_after, size_before]. Sound because
// per-bin Valid-slot counts move monotonically in these phases and a stale
// index walk only freezes, never invents, counts.
func TestPBTSizeMonotonicSandwich(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		initialSize := rapid.SampledFrom([]uint64{1, 8, 64}).Draw(t, "initialSize")
		prefill := rapid.IntRange(0, 300).Draw(t, "prefill")
		inserters := rapid.IntRange(1, 4).Draw(t, "inserters")
		insertsPerG := rapid.IntRange(50, 400).Draw(t, "insertsPerG")
		gomaxprocs := rapid.SampledFrom(gomaxprocsAxis()).Draw(t, "gomaxprocs")

		defer setGOMAXPROCS(gomaxprocs)()

		m := dlht.New[uint64, uint64](dlht.Options{InitialSize: initialSize})
		for k := 0; k < prefill; k++ {
			m.Insert(uint64(k), uint64(k)<<32|1)
		}
		before := m.Size()
		if before != uint64(prefill) {
			t.Fatalf("prefill Size()=%d, want %d", before, prefill)
		}

		// Insert-only phase with concurrent sampling.
		samples := runPhaseWithSampling(m, inserters, func(g int) []Op[uint64, uint64] {
			ops := make([]Op[uint64, uint64], insertsPerG)
			for i := range ops {
				k := uint64(prefill + g*insertsPerG + i)
				ops[i] = Op[uint64, uint64]{Kind: OpInsert, Key: k, Value: k<<32 | 1}
			}
			return ops
		})
		after := m.Size()
		wantAfter := uint64(prefill + inserters*insertsPerG)
		if after != wantAfter {
			t.Fatalf("post-insert Size()=%d, want %d", after, wantAfter)
		}
		for _, s := range samples {
			if s < before || s > after {
				t.Fatalf("insert-only phase: Size() sample %d outside [%d, %d]", s, before, after)
			}
		}

		// Delete-only phase: partitioned so each key is deleted exactly once.
		total := int(wantAfter)
		deleters := inserters
		samples = runPhaseWithSampling(m, deleters, func(g int) []Op[uint64, uint64] {
			var ops []Op[uint64, uint64]
			for k := g; k < total; k += deleters {
				ops = append(ops, Op[uint64, uint64]{Kind: OpDelete, Key: uint64(k)})
			}
			return ops
		})
		final := m.Size()
		if final != 0 {
			t.Fatalf("post-delete Size()=%d, want 0", final)
		}
		for _, s := range samples {
			if s > after {
				t.Fatalf("delete-only phase: Size() sample %d exceeds starting size %d", s, after)
			}
		}
	})
}

// runPhaseWithSampling runs the per-goroutine ops while the caller goroutine
// samples Size() in a tight loop, returning the samples.
func runPhaseWithSampling(m *dlht.Map[uint64, uint64], goroutines int, opsFor func(g int) []Op[uint64, uint64]) []uint64 {
	var done atomic.Bool
	var wg sync.WaitGroup
	for g := range goroutines {
		wg.Add(1)
		go func(g int) {
			defer wg.Done()
			for _, op := range opsFor(g) {
				execOp(m, op)
			}
		}(g)
	}
	go func() {
		wg.Wait()
		done.Store(true)
	}()

	// Do-while shape: at least one sample is always taken, so the sandwich
	// assertions can never pass vacuously on an empty slice. The final sample
	// may land after the workers joined; it still satisfies the bounds.
	var samples []uint64
	for {
		samples = append(samples, m.Size())
		if done.Load() {
			break
		}
	}
	wg.Wait()
	return samples
}
