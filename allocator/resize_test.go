package allocator

import (
	"fmt"
	"hash/maphash"
	"sync"
	"sync/atomic"
	"testing"
)

// Hash-aware adversarial geometry. These tests live in package allocator
// because the per-instance seed is
// unexported; with it we can brute-force key cohorts with chosen bin
// placement and steer the workload to the structural tipping points: the
// bin-overflow resize trigger, the link-arena-exhaustion trigger, and
// split-bit cohorts that a doubling must separate while operations race the
// transfer.
//
// Race-detector note: the concurrent tests here (readers racing a
// resize-triggering insert, Put/Delete racing a transfer) trip `go test
// -race` on a correct implementation, because the seqlock mixes plain and
// atomic accesses by design. The package's existing concurrent tests (e.g.
// TestRange_NoLossWhenStable) already do the same. Don't run these under
// -race; the tests/pbt oracles and Porcupine cover them instead.

// keysForBinDiverse returns count keys landing in binIdx under mask whose
// next `spreadBits` hash bits (the shard selector after a resize) take at
// least minShards distinct values. nil if the probe budget runs out.
func keysForBinDiverse(seed maphash.Seed, mask, binIdx uint64, spreadBits uint, minShards, count int, maxProbe uint64) []uint64 {
	out := make([]uint64, 0, count)
	shards := map[uint64]struct{}{}
	bins := uint(0)
	for m := mask; m > 0; m >>= 1 {
		bins++
	}
	for k := uint64(1); k < maxProbe && len(out) < count; k++ {
		h := maphash.Comparable(seed, k)
		if h&mask != binIdx {
			continue
		}
		out = append(out, k)
		shards[(h>>bins)&((1<<spreadBits)-1)] = struct{}{}
	}
	if len(out) < count || len(shards) < minShards {
		return nil
	}
	return out
}

// Fill one bin through its whole slot ladder (3 primary -> single link -> link
// pair = 15 slots) and push it over: the 16th colliding insert finds no free
// slot and must trigger a resize. Every key must survive the migration with
// its exact value, under concurrent readers on the same cohort.
//
// InitialSize 128 gives the bin a 16-bucket link arena, so the trigger is bin
// overflow, not arena exhaustion (covered separately below).
func TestGeometry_BinOverflowTriggersResize(t *testing.T) {
	const numBins = 128
	m := newWithSeed[uint64, uint64](Options{InitialSize: numBins}, testSeed)
	mask := uint64(numBins - 1)

	keys := keysForBin(testSeed, mask, 3, 16, 1<<24)
	if keys == nil {
		t.Skip("could not find 16 colliding keys within probe budget")
	}

	binsBefore := m.Stats().Bins

	// Readers hammer the cohort while it piles up and while the overflow
	// insert drives the migration. They report via channel: goroutines other
	// than the test's own must not call Fatalf.
	readerErr := make(chan string, 1)
	var stop sync.WaitGroup
	stopCh := make(chan struct{})
	for r := 0; r < 4; r++ {
		stop.Add(1)
		go func() {
			defer stop.Done()
			for {
				select {
				case <-stopCh:
					return
				default:
				}
				for _, k := range keys {
					if v, ok := m.Get(k); ok && v != k*10 {
						select {
						case readerErr <- fmt.Sprintf("Get(%d)=%d during pileup, want %d", k, v, k*10):
						default:
						}
						return
					}
				}
			}
		}()
	}

	for _, k := range keys {
		if _, ok := m.Insert(k, k*10); !ok {
			t.Fatalf("Insert(%d) failed on fresh colliding key", k)
		}
	}
	close(stopCh)
	stop.Wait()
	select {
	case msg := <-readerErr:
		t.Fatal(msg)
	default:
	}

	if bins := m.Stats().Bins; bins <= binsBefore {
		t.Fatalf("expected bin-overflow resize: bins before=%d after=%d", binsBefore, bins)
	}
	for _, k := range keys {
		if v, ok := m.Get(k); !ok || v != k*10 {
			t.Fatalf("post-resize Get(%d) = (%d, %v), want (%d, true)", k, v, ok, k*10)
		}
	}
	assertDumpMatches(t, m, keys)
}

// Exhaust the link arena as the resize trigger: at InitialSize 8 the arena
// has exactly one link bucket, so the second bin needing a link finds the
// arena empty and must trigger a resize even though its own ladder has room.
func TestGeometry_ArenaExhaustionTriggersResize(t *testing.T) {
	const numBins = 8
	m := newWithSeed[uint64, uint64](Options{InitialSize: numBins}, testSeed)
	mask := uint64(numBins - 1)

	binA := keysForBin(testSeed, mask, 0, 6, 1<<24)
	binB := keysForBin(testSeed, mask, 5, 6, 1<<24)
	if binA == nil || binB == nil {
		t.Skip("could not find colliding cohorts within probe budget")
	}

	binsBefore := m.Stats().Bins
	for _, k := range binA { // 4th insert attaches the arena's only link
		if _, ok := m.Insert(k, k*10); !ok {
			t.Fatalf("Insert(%d) failed", k)
		}
	}
	for _, k := range binB { // 4th insert finds the arena empty -> resize
		if _, ok := m.Insert(k, k*10); !ok {
			t.Fatalf("Insert(%d) failed", k)
		}
	}
	if bins := m.Stats().Bins; bins <= binsBefore {
		t.Fatalf("expected arena-exhaustion resize: bins before=%d after=%d", binsBefore, bins)
	}
	assertDumpMatches(t, m, append(append([]uint64{}, binA...), binB...))
}

// Split-bit cohort racing a migration: keys share their bin at the old size
// but spread across the shard-selector bits a resize uses, so the transfer
// must separate previously colliding keys while Puts and Deletes race it.
// The final state is checked exactly: every cohort key must carry the last
// value its own single mutator wrote (one goroutine per key keeps each key
// order-determinate).
func TestGeometry_SplitBitCohortRacesTransfer(t *testing.T) {
	const numBins = 64
	m := newWithSeed[uint64, uint64](Options{InitialSize: numBins}, testSeed)
	mask := uint64(numBins - 1)

	// 64 bins is < 4K, so growth is 8x: 3 shard-selector bits.
	cohort := keysForBinDiverse(testSeed, mask, 9, 3, 4, 12, 1<<24)
	if cohort == nil {
		t.Skip("could not find a shard-diverse cohort within probe budget")
	}

	for _, k := range cohort {
		if _, ok := m.Insert(k, k<<8|1); !ok {
			t.Fatalf("Insert(%d) failed", k)
		}
	}

	// One mutator goroutine per cohort key (order-determinate), plus a flood
	// that forces the resize the cohort must survive.
	const rounds = 64
	const floodKeys = 4096
	binsBefore := m.Stats().Bins
	var floodFails atomic.Uint64
	var wg sync.WaitGroup
	for _, k := range cohort {
		wg.Add(1)
		go func(k uint64) {
			defer wg.Done()
			for r := uint64(2); r <= rounds; r++ {
				if r%8 == 0 {
					m.Delete(k)
					m.Insert(k, k<<8|r)
					continue
				}
				m.Put(k, k<<8|r)
			}
		}(k)
	}
	wg.Add(1)
	go func() {
		defer wg.Done()
		for i := uint64(0); i < floodKeys; i++ {
			if _, ok := m.Insert(1<<32+i, i); !ok {
				floodFails.Add(1)
			}
		}
	}()
	wg.Wait()

	// The race this test claims to exercise only exists if the flood landed
	// and actually drove a migration.
	if n := floodFails.Load(); n != 0 {
		t.Fatalf("%d flood inserts failed on fresh keys", n)
	}
	if bins := m.Stats().Bins; bins <= binsBefore {
		t.Fatalf("expected the flood to force a resize: bins before=%d after=%d", binsBefore, bins)
	}
	for i := uint64(0); i < floodKeys; i++ {
		if v, ok := m.Get(1<<32 + i); !ok || v != i {
			t.Fatalf("flood key %d = (%d, %v) after transfer, want (%d, true)", 1<<32+i, v, ok, i)
		}
	}
	for _, k := range cohort {
		want := uint64(k<<8 | rounds)
		if v, ok := m.Get(k); !ok || v != want {
			t.Fatalf("cohort key %d = (%#x, %v) after racing transfer, want (%#x, true)", k, v, ok, want)
		}
	}
}

// assertDumpMatches verifies every key is present exactly once with value
// k*10 via a full Range walk.
func assertDumpMatches(t *testing.T, m *Map[uint64, uint64], keys []uint64) {
	t.Helper()
	dump := collectRange(t, m)
	for _, k := range keys {
		if v, ok := dump[k]; !ok || v != k*10 {
			t.Fatalf("dump[%d] = (%d, %v), want (%d, true)", k, v, ok, k*10)
		}
	}
}
