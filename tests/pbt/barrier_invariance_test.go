package pbt

import (
	"fmt"
	"maps"
	"slices"
	"sync"
	"testing"

	"github.com/jeremiah-masters/dlht"

	"pgregory.net/rapid"
)

// Barrier-insertion invariance (refinement direction only).
//
// A determinate workload is cut into phases at rapid-drawn boundaries with a
// full join between phases. Adding synchronization can only shrink the
// behavior set, so the outcome must be unchanged by any barrier placement,
// and at each barrier the map is quiescent: Size(), the Range dump, and
// Stats().Resizing are exactly checkable against the model. Barrier
// placement drags resize points and quiescent windows across the workload;
// state left dirty across a boundary (a leaked Trying slot, an uncleared
// resize context, miscounted slots) surfaces at the next barrier check.
// The reverse relation, removing synchronization, is not valid and is
// deliberately absent.
func TestPBTBarrierInvariance(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		initialSize := rapid.SampledFrom(initialSizeAxis).Draw(t, "initialSize")
		goroutines := rapid.IntRange(2, 6).Draw(t, "goroutines")
		gomaxprocs := rapid.SampledFrom(gomaxprocsAxis()).Draw(t, "gomaxprocs")
		phases := rapid.IntRange(1, 5).Draw(t, "phases")
		insertsPerPhase := rapid.IntRange(1, 200).Draw(t, "insertsPerPhase")

		defer setGOMAXPROCS(gomaxprocs)()

		m := dlht.New[uint64, uint64](dlht.Options{InitialSize: initialSize})
		model := make(map[uint64]uint64)
		nextKey := uint64(0)

		for phase := 0; phase < phases; phase++ {
			// Phase workload, determinate by construction: fresh-key inserts
			// (each key touched by exactly one goroutine) plus deletions of a
			// drawn subset of previously settled keys (each key deleted by
			// exactly one goroutine, no concurrent re-insert).
			inserts := make([]Op[uint64, uint64], insertsPerPhase)
			for i := range inserts {
				k := nextKey
				nextKey++
				inserts[i] = Op[uint64, uint64]{Kind: OpInsert, Key: k, Value: k<<32 | 1}
			}

			// Draw in sorted-key order: rapid replays a recorded bitstream in
			// draw order, and Go map iteration order changes per run, so
			// drawing inside `range model` would consume the stream against
			// different keys on replay/shrink and derail reproduction.
			var deletes []Op[uint64, uint64]
			for _, k := range slices.Sorted(maps.Keys(model)) {
				if rapid.IntRange(0, 3).Draw(t, fmt.Sprintf("del_%d_%d", phase, k)) == 0 {
					deletes = append(deletes, Op[uint64, uint64]{Kind: OpDelete, Key: k})
				}
			}

			ops := append(inserts, deletes...)
			perG := make([][]Op[uint64, uint64], goroutines)
			for i, op := range ops {
				g := rapid.IntRange(0, goroutines-1).Draw(t, fmt.Sprintf("assign_%d_%d", phase, i))
				perG[g] = append(perG[g], op)
			}

			var wg sync.WaitGroup
			errs := newErrSlots(goroutines)
			for g := range goroutines {
				wg.Add(1)
				go func(g int) {
					defer wg.Done()
					for _, op := range perG[g] {
						res := execOp(m, op)
						switch op.Kind {
						case OpInsert:
							if !res.Found {
								errs.set(g, fmt.Errorf("phase %d: Insert(%d) failed on a fresh key", phase, op.Key))
								return
							}
						case OpDelete:
							if !res.Found || res.Value != op.Key<<32|1 {
								errs.set(g, fmt.Errorf("phase %d: Delete(%d) = (%#x, %v), want (%#x, true)",
									phase, op.Key, res.Value, res.Found, op.Key<<32|1))
								return
							}
						}
					}
				}(g)
			}
			wg.Wait() // the barrier
			if err := errs.first(); err != nil {
				t.Fatalf("%v", err)
			}

			for _, op := range inserts {
				model[op.Key] = op.Value
			}
			for _, op := range deletes {
				delete(model, op.Key)
			}

			// Quiescent checks at the barrier.
			if got := m.Size(); got != uint64(len(model)) {
				t.Fatalf("phase %d barrier: Size()=%d, model has %d", phase, got, len(model))
			}
			if m.Stats().Resizing {
				t.Fatalf("phase %d barrier: Stats().Resizing=true at quiescence", phase)
			}
			dump, dupErr := quiescentDump(m)
			if dupErr != nil {
				t.Fatalf("phase %d barrier: %v", phase, dupErr)
			}
			if len(dump) != len(model) {
				t.Fatalf("phase %d barrier: dump has %d keys, model has %d", phase, len(dump), len(model))
			}
			for k, want := range model {
				if got, ok := dump[k]; !ok || got != want {
					t.Fatalf("phase %d barrier: key %d dump=(%#x,%v) model=%#x", phase, k, got, ok, want)
				}
			}
		}
	})
}
