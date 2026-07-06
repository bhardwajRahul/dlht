package pbt

import (
	"fmt"
	"testing"

	"github.com/jeremiah-masters/dlht"

	"pgregory.net/rapid"
)

// Orbit invariance on order-determinate workloads.
//
// The workload is built so every key's update multiset is order-determinate:
// solo keys run a fixed per-key script on one goroutine (program order),
// raced keys receive identical-value Inserts from many goroutines, and no-op
// pairs insert then delete a fresh key on one goroutine. For such workloads
// the final state and every mutator's return value are fixed functions of
// the workload, independent of InitialSize, goroutine count, partition,
// GOMAXPROCS, and the per-instance hash seed. One reference certifies every
// grid point, and a fresh map per repetition sweeps seeds for free.
//
// The per-op assertions are exact: solo scripts return deterministic values,
// racing identical-value Inserts produce exactly one winner with every loser
// returning the raced value, pair ops both succeed, and Put/Delete on virgin
// keys fail with zero values.

type soloScript uint8

const (
	scriptI     soloScript = iota // Insert          -> final: v1
	scriptIP                      // Insert;Put      -> final: v2
	scriptID                      // Insert;Delete   -> final: absent
	scriptIPD                     // Insert;Put;Del  -> final: absent
	scriptPFail                   // Put on virgin   -> final: absent
	scriptDFail                   // Delete on virgin-> final: absent
	numSoloScripts
)

// orbitUnit is a run of program-ordered ops executed by one goroutine, with
// exact expected results (nil expect for raced units, resolved after the run).
type orbitUnit struct {
	ops    []Op[uint64, uint64]
	expect []OpResult[uint64]
	raced  bool // identical-value Insert race; winner resolved post-join
}

func soloVal(k uint64, n uint64) uint64 { return k<<32 | n }

// buildSoloUnit returns the unit and the key's expected final value (present
// reports whether the key ends up in the map).
func buildSoloUnit(k uint64, script soloScript) (u orbitUnit, final uint64, present bool) {
	v1, v2 := soloVal(k, 1), soloVal(k, 2)
	switch script {
	case scriptI:
		u.ops = []Op[uint64, uint64]{{Kind: OpInsert, Key: k, Value: v1}}
		u.expect = []OpResult[uint64]{{Found: true}}
		return u, v1, true
	case scriptIP:
		u.ops = []Op[uint64, uint64]{{Kind: OpInsert, Key: k, Value: v1}, {Kind: OpPut, Key: k, Value: v2}}
		u.expect = []OpResult[uint64]{{Found: true}, {Updated: true, Value: v1}}
		return u, v2, true
	case scriptID:
		u.ops = []Op[uint64, uint64]{{Kind: OpInsert, Key: k, Value: v1}, {Kind: OpDelete, Key: k}}
		u.expect = []OpResult[uint64]{{Found: true}, {Found: true, Value: v1}}
		return u, 0, false
	case scriptIPD:
		u.ops = []Op[uint64, uint64]{{Kind: OpInsert, Key: k, Value: v1}, {Kind: OpPut, Key: k, Value: v2}, {Kind: OpDelete, Key: k}}
		u.expect = []OpResult[uint64]{{Found: true}, {Updated: true, Value: v1}, {Found: true, Value: v2}}
		return u, 0, false
	case scriptPFail:
		u.ops = []Op[uint64, uint64]{{Kind: OpPut, Key: k, Value: v1}}
		u.expect = []OpResult[uint64]{{}}
		return u, 0, false
	case scriptDFail:
		u.ops = []Op[uint64, uint64]{{Kind: OpDelete, Key: k}}
		u.expect = []OpResult[uint64]{{}}
		return u, 0, false
	default:
		panic("unknown solo script")
	}
}

func TestPBTOrbitInvariance(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		initialSize := rapid.SampledFrom(initialSizeAxis).Draw(t, "initialSize")
		goroutines := rapid.IntRange(1, 8).Draw(t, "goroutines") // 1 doubles as the sequential reference
		gomaxprocs := rapid.SampledFrom(gomaxprocsAxis()).Draw(t, "gomaxprocs")
		soloKeys := rapid.IntRange(0, 60).Draw(t, "soloKeys")
		racedKeys := rapid.IntRange(0, 8).Draw(t, "racedKeys")
		pairKeys := rapid.IntRange(0, 40).Draw(t, "pairKeys")
		gets := rapid.IntRange(0, 120).Draw(t, "gets")

		// Key space layout: [0,soloKeys) solo, then raced, then pairs.
		racedBase := uint64(soloKeys)
		pairBase := racedBase + uint64(racedKeys)
		totalKeys := pairBase + uint64(pairKeys)

		reference := make(map[uint64]uint64)
		var units []orbitUnit

		soloAllowed := make(map[uint64][]uint64) // values a Get may observe
		for i := range soloKeys {
			k := uint64(i)
			script := soloScript(rapid.IntRange(0, int(numSoloScripts)-1).Draw(t, fmt.Sprintf("script_%d", i)))
			u, final, present := buildSoloUnit(k, script)
			units = append(units, u)
			if present {
				reference[k] = final
			}
			switch script {
			case scriptI:
				soloAllowed[k] = []uint64{soloVal(k, 1)}
			case scriptIP, scriptIPD:
				soloAllowed[k] = []uint64{soloVal(k, 1), soloVal(k, 2)}
			case scriptID:
				soloAllowed[k] = []uint64{soloVal(k, 1)}
			default:
				soloAllowed[k] = nil
			}
		}

		for i := range racedKeys {
			k := racedBase + uint64(i)
			reference[k] = soloVal(k, 1)
			for range goroutines { // one racing Insert per goroutine
				units = append(units, orbitUnit{
					ops:   []Op[uint64, uint64]{{Kind: OpInsert, Key: k, Value: soloVal(k, 1)}},
					raced: true,
				})
			}
		}

		for i := range pairKeys {
			k := pairBase + uint64(i)
			u, _, _ := buildSoloUnit(k, scriptID) // insert+delete no-op pair, same goroutine
			units = append(units, u)
		}

		for range gets {
			k := uint64(rapid.IntRange(0, max(int(totalKeys)-1, 0)).Draw(t, "getKey"))
			units = append(units, orbitUnit{ops: []Op[uint64, uint64]{{Kind: OpGet, Key: k}}})
		}

		// Partition: assign each unit to a goroutine (per-key multisets are
		// preserved because units never split).
		assignment := make([]int, len(units))
		for i := range units {
			assignment[i] = rapid.IntRange(0, goroutines-1).Draw(t, fmt.Sprintf("assign_%d", i))
		}

		defer setGOMAXPROCS(gomaxprocs)()
		for rep := 0; rep < 3; rep++ {
			runOrbitCase(t, rep, initialSize, goroutines, units, assignment, reference, soloAllowed, racedBase, uint64(racedKeys))
		}
	})
}

func runOrbitCase(
	t *rapid.T,
	rep int,
	initialSize uint64,
	goroutines int,
	units []orbitUnit,
	assignment []int,
	reference map[uint64]uint64,
	soloAllowed map[uint64][]uint64,
	racedBase, racedKeys uint64,
) {
	m := dlht.New[uint64, uint64](dlht.Options{InitialSize: initialSize})

	perG := make([][]int, goroutines)
	for i, g := range assignment {
		perG[g] = append(perG[g], i)
	}

	// Start gate: without one, small unit lists finish before contention
	// forms and the raced-Insert units rarely actually race.
	results := make([][][]OpResult[uint64], goroutines)
	done := make(chan struct{})
	gate := make(chan struct{})
	for g := range goroutines {
		go func(g int) {
			defer func() { done <- struct{}{} }()
			<-gate
			out := make([][]OpResult[uint64], 0, len(perG[g]))
			for _, ui := range perG[g] {
				u := units[ui]
				rs := make([]OpResult[uint64], len(u.ops))
				for oi, op := range u.ops {
					rs[oi] = execOp(m, op)
				}
				out = append(out, rs)
			}
			results[g] = out
		}(g)
	}
	close(gate)
	for range goroutines {
		<-done
	}

	// Exact per-op assertions for deterministic units; winner accounting for
	// raced units; allowed-value checks for Gets.
	racedWins := make(map[uint64]int)
	for g := range goroutines {
		for slot, ui := range perG[g] {
			u := units[ui]
			rs := results[g][slot]
			switch {
			case u.raced:
				k := u.ops[0].Key
				if rs[0].Found {
					racedWins[k]++
				} else if rs[0].Value != soloVal(k, 1) {
					t.Fatalf("rep %d: losing Insert on raced key %d returned %#x, want %#x",
						rep, k, rs[0].Value, soloVal(k, 1))
				}
			case u.ops[0].Kind == OpGet:
				k := u.ops[0].Key
				if rs[0].Found {
					allowed := soloAllowed[k]
					if k >= racedBase && k < racedBase+racedKeys {
						allowed = []uint64{soloVal(k, 1)}
					}
					if k >= racedBase+racedKeys { // pair keys
						allowed = []uint64{soloVal(k, 1)}
					}
					okVal := false
					for _, v := range allowed {
						if rs[0].Value == v {
							okVal = true
							break
						}
					}
					if !okVal {
						t.Fatalf("rep %d: Get(%d) observed %#x, not among values ever written %v",
							rep, k, rs[0].Value, allowed)
					}
				}
			default:
				for oi := range u.ops {
					if rs[oi] != u.expect[oi] {
						t.Fatalf("rep %d: unit key=%d op %d (%s) returned %+v, determinate expectation %+v",
							rep, u.ops[oi].Key, oi, u.ops[oi].Kind, rs[oi], u.expect[oi])
					}
				}
			}
		}
	}
	for i := range racedKeys {
		k := racedBase + i
		if racedWins[k] != 1 {
			t.Fatalf("rep %d: raced key %d had %d winning Inserts, want exactly 1", rep, k, racedWins[k])
		}
	}

	// Quiescent dump equals the sequentially computed reference.
	dump, dupErr := quiescentDump(m)
	if dupErr != nil {
		t.Fatalf("rep %d: %v", rep, dupErr)
	}
	if len(dump) != len(reference) {
		t.Fatalf("rep %d: dump has %d keys, reference has %d", rep, len(dump), len(reference))
	}
	for k, want := range reference {
		if got, ok := dump[k]; !ok || got != want {
			t.Fatalf("rep %d: key %d: dump=(%#x,%v), reference=%#x", rep, k, got, ok, want)
		}
	}
	if got := m.Size(); got != uint64(len(reference)) {
		t.Fatalf("rep %d: quiescent Size()=%d, want %d", rep, got, len(reference))
	}
	if m.Stats().Resizing {
		t.Fatalf("rep %d: Stats().Resizing=true at quiescence", rep)
	}
}
