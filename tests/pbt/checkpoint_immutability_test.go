package pbt

import (
	"fmt"
	"runtime"
	"runtime/debug"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/jeremiah-masters/dlht"
)

// Checkpoint immutability under resize churn and GC pressure.
//
// A settled key set S is snapshotted at quiescence, then epochs of hostile
// activity run on a disjoint fresh key space: insert/delete churn plus a
// persistent flood that forces resize generations (so every member of S is
// physically moved by transfers), while one goroutine cycles runtime.GC()
// with heap ballast and readers hammer S. After each epoch the dump must be
// exactly snapshot plus every flood key ever kept: settled projection
// bit-identical, no churned key resurrected, nothing lost.
//
// Epochs end on evidence, not op counts: churn keeps running until the
// runtime has completed several GC cycles on top of a wall-clock floor, so
// the storm actually overlaps live transfers and reader traffic. An
// op-bounded epoch finishes in about a millisecond, before a single forced
// GC lands, and the GC/rotated-layout interaction this test exists for
// would go unexercised.
//
// Key disjointness is what makes the relation exact. The InitialSize sweep
// pins each aligned-allocation path and the storm runs at SetGCPercent(1).
func TestPBTCheckpointImmutability(t *testing.T) {
	// 1..3 have zero-link arenas, 8/64 take the small-object (possibly
	// rotated) path, 512 forces the large-object path for the bin array.
	for _, initialSize := range []uint64{1, 8, 64, 512} {
		t.Run(fmt.Sprintf("InitialSize=%d", initialSize), func(t *testing.T) {
			runCheckpointImmutability(t, initialSize)
		})
	}
}

func runCheckpointImmutability(t *testing.T, initialSize uint64) {
	prevGC := debug.SetGCPercent(1)
	defer debug.SetGCPercent(prevGC)

	const (
		settledKeys  = 400
		epochs       = 3
		churnWorkers = 2
		minGCs       = 4                     // forced-GC cycles per epoch, on top of...
		minEpoch     = 50 * time.Millisecond // ...a wall-clock floor
		maxEpoch     = 2 * time.Second       // hard cap so a stuck GC can't hang the test
		workerSpan   = uint64(1) << 24       // disjoint key range per (epoch, worker)
		churnBase    = uint64(1) << 20       // above settled keys, below tag-stamp limit
	)

	m := dlht.New[uint64, uint64](dlht.Options{InitialSize: initialSize})
	snapshot := make(map[uint64]uint64, settledKeys)
	for k := uint64(0); k < settledKeys; k++ {
		v := k<<32 | 1
		if _, ok := m.Insert(k, v); !ok {
			t.Fatalf("settle Insert(%d) failed", k)
		}
		snapshot[k] = v
	}

	// Flood keys kept across ALL epochs; the dump check below verifies every
	// one of them every epoch, so corruption of an earlier epoch's keys by a
	// later epoch's churn is caught (delayed-corruption coverage).
	expectedFlood := make(map[uint64]uint64)

	for epoch := 0; epoch < epochs; epoch++ {
		errs := newErrSlots(churnWorkers + 2)
		var stopChurn, stopAux atomic.Bool
		var wgChurn, wgAux sync.WaitGroup
		iters := make([]uint64, churnWorkers) // published before wgChurn.Done

		// Unbounded churn + flood on keys disjoint from S and from every
		// other (epoch, worker) range. Iteration i touches base+2i (churned:
		// insert then delete) and, every 4th iteration, keeps base+2i+1.
		for w := range churnWorkers {
			base := churnBase + uint64(epoch*churnWorkers+w)*workerSpan
			wgChurn.Add(1)
			go func(w int, base uint64) {
				defer wgChurn.Done()
				var i uint64
				for !stopChurn.Load() {
					ck := base + 2*i
					if _, ok := m.Insert(ck, ck<<32|1); !ok {
						errs.set(w, fmt.Errorf("churn Insert(%d) failed", ck))
						break
					}
					if _, ok := m.Delete(ck); !ok {
						errs.set(w, fmt.Errorf("churn Delete(%d) failed", ck))
						break
					}
					if i%4 == 0 {
						fk := base + 2*i + 1
						if _, ok := m.Insert(fk, fk<<32|1); !ok {
							errs.set(w, fmt.Errorf("flood Insert(%d) failed", fk))
							break
						}
					}
					i++
				}
				iters[w] = i
			}(w, base)
		}

		// GC storm: force collections with ballast turnover so entry pointers
		// must survive tracing through the rotated layouts while transfers
		// and readers are live.
		wgAux.Add(1)
		go func() {
			defer wgAux.Done()
			for !stopAux.Load() {
				ballast := make([][]byte, 8)
				for i := range ballast {
					ballast[i] = make([]byte, 64<<10)
				}
				runtime.GC()
				_ = ballast
			}
		}()

		// Readers hammer the settled set during the storm.
		wgAux.Add(1)
		go func() {
			defer wgAux.Done()
			for !stopAux.Load() {
				for k := uint64(0); k < settledKeys; k++ {
					v, ok := m.Get(k)
					if !ok || v != snapshot[k] {
						errs.set(churnWorkers+1, fmt.Errorf("epoch %d: settled key %d read (%#x, %v), snapshot %#x",
							epoch, k, v, ok, snapshot[k]))
						return
					}
				}
			}
		}()

		// Evidence-based epoch length: wait for forced-GC cycles + the floor.
		var ms runtime.MemStats
		runtime.ReadMemStats(&ms)
		startGC := ms.NumGC
		epochStart := time.Now()
		for {
			time.Sleep(5 * time.Millisecond)
			runtime.ReadMemStats(&ms)
			gcDone := ms.NumGC >= startGC+minGCs && time.Since(epochStart) >= minEpoch
			if gcDone || time.Since(epochStart) >= maxEpoch || errs.first() != nil {
				break
			}
		}
		stopChurn.Store(true)
		wgChurn.Wait()
		stopAux.Store(true)
		wgAux.Wait()

		if err := errs.first(); err != nil {
			t.Fatalf("%v", err)
		}

		// Record this epoch's kept flood keys (iteration i complete for all
		// i < iters[w], and i%4==0 iterations kept base+2i+1).
		for w := range churnWorkers {
			base := churnBase + uint64(epoch*churnWorkers+w)*workerSpan
			for i := uint64(0); i < iters[w]; i += 4 {
				fk := base + 2*i + 1
				expectedFlood[fk] = fk<<32 | 1
			}
		}

		// Quiescent: the dump must hold exactly snapshot plus expectedFlood.
		// Settled projection bit-identical, every flood key from every epoch
		// intact, and nothing else (no resurrected churn keys, no strays).
		dump, dupErr := quiescentDump(m)
		if dupErr != nil {
			t.Fatalf("epoch %d: %v", epoch, dupErr)
		}
		if want := len(snapshot) + len(expectedFlood); len(dump) != want {
			t.Fatalf("epoch %d: dump has %d keys, want %d (settled %d + flood %d)",
				epoch, len(dump), want, len(snapshot), len(expectedFlood))
		}
		for k, want := range snapshot {
			if got, ok := dump[k]; !ok || got != want {
				t.Fatalf("epoch %d: settled key %d = (%#x, %v) after churn, snapshot %#x",
					epoch, k, got, ok, want)
			}
		}
		for k, want := range expectedFlood {
			if got, ok := dump[k]; !ok || got != want {
				t.Fatalf("epoch %d: flood key %d = (%#x, %v), want (%#x, true)", epoch, k, got, ok, want)
			}
		}
	}
}
