package pbt

import (
	"fmt"
	"runtime"
	"sync"
	"sync/atomic"
	"testing"

	"github.com/jeremiah-masters/dlht"

	"pgregory.net/rapid"
)

// Session guarantees under single-writer keys: a cheap real-time-order
// check with no history recording.
//
// Each key is owned by exactly one writer goroutine that writes strictly
// increasing sequence tags (Insert seq=1, then Puts seq=2..N). Linearizability
// plus per-goroutine program order forces:
//
//   - monotonic reads: per (reader, key), the observed seq never decreases,
//     and once a reader has seen the key it never sees it absent again
//     (owners never delete in this test);
//   - read-your-writes: an owner's own Get returns exactly its latest write,
//     since nobody else writes the key.
//
// A flood goroutine stacks resize generations under the readers (InitialSize
// is drawn as low as 1), so a reader that consults a stale generation after
// having observed a newer one fails immediately with a decreasing seq. That
// is the indexNext chain-walk discipline under test.
func TestPBTSessionMonotonicReads(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		initialSize := rapid.SampledFrom([]uint64{1, 2, 8, 64}).Draw(t, "initialSize")
		writers := rapid.IntRange(1, 4).Draw(t, "writers")
		readers := rapid.IntRange(1, 4).Draw(t, "readers")
		keys := rapid.IntRange(1, 24).Draw(t, "keys")
		writesPerKey := rapid.IntRange(2, 60).Draw(t, "writesPerKey")
		floodOps := rapid.SampledFrom([]int{0, 300, 900}).Draw(t, "floodOps")
		gomaxprocs := rapid.SampledFrom(gomaxprocsAxis()).Draw(t, "gomaxprocs")

		defer setGOMAXPROCS(gomaxprocs)()
		for rep := 0; rep < 2; rep++ {
			runSessionCase(t, rep, initialSize, writers, readers, keys, writesPerKey, floodOps)
		}
	})
}

// The soak variant hunts generation lag. A Get can only be "behind" within a
// single call (it reloads m.active on entry), so catching a stale redirect
// takes a reader descheduled mid-Get while two resizes complete underneath
// it. Oversubscription (readers well past GOMAXPROCS) makes those windows
// long, and fresh-map rounds keep resize events frequent; a growing table
// resizes less and less often at 8x growth.
func TestPBTSessionMonotonicSoak(t *testing.T) {
	rounds := 12
	if testing.Short() {
		rounds = 2
	}
	const (
		writers      = 4
		readers      = 32
		keys         = 16
		writesPerKey = 300 // keeps owners writing through the late, slow transfers
		floodOps     = 50_000
	)
	defer setGOMAXPROCS(2)()
	for round := 0; round < rounds; round++ {
		runSessionRound(t, round, 1, writers, readers, keys, writesPerKey, floodOps)
	}
}

func runSessionCase(t *rapid.T, rep int, initialSize uint64, writers, readers, keys, writesPerKey, floodOps int) {
	runSessionRound(t, rep, initialSize, writers, readers, keys, writesPerKey, floodOps)
}

func runSessionRound(t fataler, rep int, initialSize uint64, writers, readers, keys, writesPerKey, floodOps int) {
	m := dlht.New[uint64, uint64](dlht.Options{InitialSize: initialSize})
	tag := func(k uint64, seq int) uint64 { return k<<32 | uint64(seq) }

	var writersDone atomic.Bool
	errs := newErrSlots(writers + readers + 1)
	var wgWriters, wgAll sync.WaitGroup

	for w := range writers {
		wgWriters.Add(1)
		wgAll.Add(1)
		go func(w int) {
			defer wgWriters.Done()
			defer wgAll.Done()
			for seq := 1; seq <= writesPerKey; seq++ {
				for k := w; k < keys; k += writers {
					key := uint64(k)
					if seq == 1 {
						if _, ok := m.Insert(key, tag(key, 1)); !ok {
							errs.set(w, fmt.Errorf("owner Insert(%d) failed", key))
							return
						}
					} else {
						if _, ok := m.Put(key, tag(key, seq)); !ok {
							errs.set(w, fmt.Errorf("owner Put(%d, seq=%d) failed: key vanished", key, seq))
							return
						}
					}
					// Read-your-writes: sole writer, so the latest write is
					// the only legal result.
					got, ok := m.Get(key)
					if !ok || got != tag(key, seq) {
						errs.set(w, fmt.Errorf("read-your-writes: owner of key %d wrote seq=%d, Get returned (%#x, %v)",
							key, seq, got, ok))
						return
					}
				}
			}
		}(w)
	}

	for r := range readers {
		wgAll.Add(1)
		go func(r int) {
			defer wgAll.Done()
			lastSeen := make([]uint64, keys)
			everSeen := make([]bool, keys)
			for {
				finalPass := writersDone.Load()
				for k := range keys {
					key := uint64(k)
					v, ok := m.Get(key)
					if !ok {
						if everSeen[k] {
							errs.set(writers+r, fmt.Errorf("monotonic reads: reader %d saw key %d then later missed it (no deletes in workload)", r, key))
							return
						}
						continue
					}
					if v>>32 != key {
						errs.set(writers+r, fmt.Errorf("cross-key leakage: Get(%d) returned %#x stamped for key %d", key, v, v>>32))
						return
					}
					seq := v & 0xFFFFFFFF
					if seq < lastSeen[k] {
						errs.set(writers+r, fmt.Errorf("monotonic reads violated: reader %d key %d saw seq %d after seq %d",
							r, key, seq, lastSeen[k]))
						return
					}
					lastSeen[k] = seq
					everSeen[k] = true
				}
				if finalPass {
					return
				}
				runtime.Gosched()
			}
		}(r)
	}

	wgWriters.Add(1)
	wgAll.Add(1)
	go func() {
		defer wgWriters.Done()
		defer wgAll.Done()
		for i := 0; i < floodOps; i++ {
			k := uint64(1<<20 + i)
			if _, ok := m.Insert(k, k<<32|1); !ok {
				errs.set(writers+readers, fmt.Errorf("flood Insert(%d) failed on fresh key", k))
				return
			}
		}
	}()

	// Readers keep polling until every writer (owners and flood) is done, then
	// run one final pass so they observe the settled state.
	go func() {
		wgWriters.Wait()
		writersDone.Store(true)
	}()

	wgAll.Wait()
	if err := errs.first(); err != nil {
		t.Fatalf("rep %d: %v", rep, err)
	}

	// Quiescent: every owned key holds exactly its final seq.
	for k := range keys {
		key := uint64(k)
		got, ok := m.Get(key)
		if !ok || got != tag(key, writesPerKey) {
			t.Fatalf("rep %d: final state of key %d = (%#x, %v), want (%#x, true)",
				rep, key, got, ok, tag(key, writesPerKey))
		}
	}
}
