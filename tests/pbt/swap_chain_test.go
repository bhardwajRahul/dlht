package pbt

import (
	"fmt"
	"runtime"
	"testing"

	"github.com/jeremiah-masters/dlht"

	"pgregory.net/rapid"
)

// Swap-chain conservation.
//
// Put and Delete return the value they displace. With every written value
// globally unique, linearizability orders each key's successful mutators
// into a chain (insert, updates, maybe a delete, insert again, ...), and
// each written value is consumed exactly once: by the next successful Put,
// by the next successful Delete, or by surviving as the final value. So at
// quiescence, per key:
//
//	written(k):  values written by successful Insert/Put
//	consumed(k): old values returned by successful Put/Delete,
//	             plus the final value if the key is present
//
// and the two must match as multisets. Successful inserts minus successful
// deletes must also equal presence (0 or 1). The relation is exact under any
// op mix at any contention level, which is where lost updates, double
// applies, and phantom old values (the TOCTOU class Put's inner seqlock
// defends against) live. A violation names the offending value.

type swapOp struct {
	kind OpKind
	key  uint64
}

type chainRec struct {
	kind OpKind
	key  uint64
	val  uint64 // value written (successful Insert/Put)
	old  uint64 // old/existing value returned
	ok   bool
}

type swapChainConfig struct {
	initialSize uint64
	hotKeys     int
	floodOps    int // fresh-key inserts on one extra goroutine; forces resizes
	yieldEvery  int // if >0, workers Gosched every N ops (interleaving diversity)
}

// executeSwapChain runs the plan concurrently and returns per-goroutine
// records. Workers start behind a gate; without one, a short plan on a fresh
// map can finish before any two goroutines overlap. Tag violations observed
// on the fly (cross-key stamps, ghosts) are reported through errs.
func executeSwapChain(m *dlht.Map[uint64, uint64], cfg swapChainConfig, plan [][]swapOp, tags *tagStore, errs *errSlots) [][]chainRec {
	recs := make([][]chainRec, len(plan))
	done := make(chan int, len(plan)+1)
	gate := make(chan struct{})

	for g := range plan {
		go func(g int) {
			defer func() { done <- g }()
			<-gate
			out := make([]chainRec, 0, len(plan[g]))
			for i, op := range plan[g] {
				if cfg.yieldEvery > 0 && i%cfg.yieldEvery == 0 {
					runtime.Gosched()
				}
				switch op.kind {
				case OpGet:
					if v, ok := m.Get(op.key); ok {
						if err := tags.validate(op.key, v); err != nil {
							errs.set(g, fmt.Errorf("Get: %w", err))
						}
					}
				case OpInsert:
					v := tags.next(op.key)
					old, ok := m.Insert(op.key, v)
					if !ok {
						if err := tags.validate(op.key, old); err != nil {
							errs.set(g, fmt.Errorf("failed Insert existing value: %w", err))
						}
					}
					out = append(out, chainRec{kind: OpInsert, key: op.key, val: v, old: old, ok: ok})
				case OpPut:
					v := tags.next(op.key)
					old, ok := m.Put(op.key, v)
					if ok {
						if err := tags.validate(op.key, old); err != nil {
							errs.set(g, fmt.Errorf("Put old value: %w", err))
						}
					}
					out = append(out, chainRec{kind: OpPut, key: op.key, val: v, old: old, ok: ok})
				case OpDelete:
					old, ok := m.Delete(op.key)
					if ok {
						if err := tags.validate(op.key, old); err != nil {
							errs.set(g, fmt.Errorf("Delete old value: %w", err))
						}
					}
					out = append(out, chainRec{kind: OpDelete, key: op.key, old: old, ok: ok})
				}
			}
			recs[g] = out
		}(g)
	}

	// Flood goroutine: unique fresh keys, inserted once, never deleted. Their
	// chain is W={tag}, R={final}, checked by the same accounting below.
	go func() {
		defer func() { done <- len(plan) }()
		<-gate
		for i := 0; i < cfg.floodOps; i++ {
			k := uint64(cfg.hotKeys + i)
			v := tags.next(k)
			if _, ok := m.Insert(k, v); !ok {
				errs.set(len(plan), fmt.Errorf("flood Insert(%d) failed on a fresh key", k))
				return
			}
		}
	}()

	close(gate)
	for i := 0; i < len(plan)+1; i++ {
		<-done
	}
	return recs
}

type fataler interface {
	Fatalf(format string, args ...any)
}

// checkSwapChain verifies the conservation relations against the quiescent
// dump. Runs on the test goroutine after all workers joined.
func checkSwapChain(t fataler, m *dlht.Map[uint64, uint64], cfg swapChainConfig, recs [][]chainRec, tags *tagStore) {
	dump, dupErr := quiescentDump(m)
	if dupErr != nil {
		t.Fatalf("%v", dupErr)
	}

	numKeys := cfg.hotKeys + cfg.floodOps
	written := make([]map[uint64]int, numKeys)  // W(k)
	consumed := make([]map[uint64]int, numKeys) // R(k)
	succIns := make([]int, numKeys)
	succDel := make([]int, numKeys)
	for k := range numKeys {
		written[k] = map[uint64]int{}
		consumed[k] = map[uint64]int{}
	}

	var failedInsertOlds []chainRec
	for _, rs := range recs {
		for _, r := range rs {
			switch r.kind {
			case OpInsert:
				if r.ok {
					written[r.key][r.val]++
					succIns[r.key]++
				} else {
					failedInsertOlds = append(failedInsertOlds, r)
				}
			case OpPut:
				if r.ok {
					written[r.key][r.val]++
					consumed[r.key][r.old]++
				}
			case OpDelete:
				if r.ok {
					consumed[r.key][r.old]++
					succDel[r.key]++
				}
			}
		}
	}
	// The flood goroutine records nothing; reconstruct its writes from issued
	// tags: each flood key has exactly one issued tag and one successful insert.
	for i := 0; i < cfg.floodOps; i++ {
		k := uint64(cfg.hotKeys + i)
		written[k][k<<32|1]++
		succIns[k]++
	}

	for k := range numKeys {
		key := uint64(k)
		if final, present := dump[key]; present {
			if err := tags.validate(key, final); err != nil {
				t.Fatalf("final value: %v", err)
			}
			consumed[key][final]++
		}

		presence := 0
		if _, ok := dump[key]; ok {
			presence = 1
		}
		if succIns[key]-succDel[key] != presence {
			t.Fatalf("key %d: %d successful inserts - %d successful deletes != presence %d",
				key, succIns[key], succDel[key], presence)
		}

		for v, n := range written[key] {
			if consumed[key][v] != n {
				t.Fatalf("key %d: value %#x written %d time(s) but consumed %d time(s) (lost or duplicated update)",
					key, v, n, consumed[key][v])
			}
		}
		for v, n := range consumed[key] {
			if written[key][v] != n {
				t.Fatalf("key %d: value %#x consumed %d time(s) but written %d time(s) (phantom old value)",
					key, v, n, written[key][v])
			}
		}
	}

	for _, r := range failedInsertOlds {
		if written[r.key][r.old] == 0 {
			t.Fatalf("key %d: failed Insert returned existing value %#x that no successful op wrote", r.key, r.old)
		}
	}

	// Keys outside the planned space must not exist.
	for k := range dump {
		if k >= uint64(numKeys) {
			t.Fatalf("dump contains unplanned key %d", k)
		}
	}
	if got := m.Size(); got != uint64(len(dump)) {
		t.Fatalf("quiescent Size()=%d != dump size %d", got, len(dump))
	}
}

func TestPBTSwapChainConservation(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		cfg := swapChainConfig{
			initialSize: rapid.SampledFrom([]uint64{1, 2, 8, 64}).Draw(t, "initialSize"),
			hotKeys:     rapid.IntRange(1, 8).Draw(t, "hotKeys"),
			floodOps:    rapid.SampledFrom([]int{0, 200, 600}).Draw(t, "floodOps"),
		}
		goroutines := rapid.IntRange(2, 8).Draw(t, "goroutines")
		opsPerG := rapid.IntRange(50, 250).Draw(t, "opsPerG")
		gomaxprocs := rapid.SampledFrom(gomaxprocsAxis()).Draw(t, "gomaxprocs")

		mix := OpMix{Get: 15, Insert: 30, Put: 25, Delete: 30}
		plan := make([][]swapOp, goroutines)
		for g := range plan {
			plan[g] = make([]swapOp, opsPerG)
			for i := range plan[g] {
				plan[g][i] = swapOp{
					kind: DrawOpKind(t, mix),
					key:  uint64(rapid.IntRange(0, cfg.hotKeys-1).Draw(t, "key")),
				}
			}
		}

		defer setGOMAXPROCS(gomaxprocs)()
		// Repeat the same drawn case a few times: schedule nondeterminism means
		// one quiet run proves little, and shrinking needs violations to
		// reproduce with reasonable probability.
		for rep := 0; rep < 3; rep++ {
			m := dlht.New[uint64, uint64](dlht.Options{InitialSize: cfg.initialSize})
			tags := newTagStore(cfg.hotKeys + cfg.floodOps)
			errs := newErrSlots(goroutines + 1)
			recs := executeSwapChain(m, cfg, plan, tags, errs)
			if err := errs.first(); err != nil {
				t.Fatalf("rep %d: %v", rep, err)
			}
			checkSwapChain(t, m, cfg, recs, tags)
		}
	})
}

// The soak variants run the conservation relation at volumes where the rare
// races have realistic hit probability. Deterministic plans, no rapid.
//
// The single-hot-key rounds target slot recycling: a Put retry racing a
// Delete-then-Insert reuse of the same slot needs sustained cycling on a
// small fresh table, and many short rounds hit that window far more often
// than one long run does. The multi-key round with a resize flood targets
// migration races.
func TestPBTSwapChainSoak(t *testing.T) {
	// Keep the full round count even under -short: 40 rounds missed a
	// hand-seeded bug in Put's inner seqlock in 4 of 5 runs, 400 caught it
	// every time, and the whole soak takes about a quarter second.
	const rounds = 400
	opsPerG := 300
	goroutines := max(runtime.NumCPU(), 4)

	// Round-robin Delete->Insert->Put per worker, offset so phases collide.
	hotCfg := swapChainConfig{initialSize: 4, hotKeys: 1, floodOps: 0, yieldEvery: 7}
	kinds := [...]OpKind{OpDelete, OpInsert, OpPut}
	hotPlan := make([][]swapOp, goroutines)
	for g := range hotPlan {
		hotPlan[g] = make([]swapOp, opsPerG)
		for i := range hotPlan[g] {
			hotPlan[g][i] = swapOp{kind: kinds[(i+g)%len(kinds)], key: 0}
		}
	}
	for round := 0; round < rounds; round++ {
		m := dlht.New[uint64, uint64](dlht.Options{InitialSize: hotCfg.initialSize})
		tags := newTagStore(1)
		errs := newErrSlots(goroutines + 1)
		recs := executeSwapChain(m, hotCfg, hotPlan, tags, errs)
		if err := errs.first(); err != nil {
			t.Fatalf("round %d: %v", round, err)
		}
		checkSwapChain(t, m, hotCfg, recs, tags)
	}

	// Migration round: multi-key churn racing a fresh-key flood across
	// several resize generations.
	const (
		hotKeys    = 16
		bigOpsPerG = 20_000
		floodOps   = 20_000
	)
	bigCfg := swapChainConfig{initialSize: 2, hotKeys: hotKeys, floodOps: floodOps}
	bigKinds := [...]OpKind{OpInsert, OpDelete, OpPut, OpInsert, OpGet, OpDelete, OpPut, OpDelete}
	plan := make([][]swapOp, 2*runtime.NumCPU())
	for g := range plan {
		plan[g] = make([]swapOp, bigOpsPerG)
		for i := range plan[g] {
			plan[g][i] = swapOp{
				kind: bigKinds[(i+g)%len(bigKinds)],
				key:  uint64((i*7 + g*3) % hotKeys),
			}
		}
	}
	m := dlht.New[uint64, uint64](dlht.Options{InitialSize: bigCfg.initialSize})
	tags := newTagStore(hotKeys + floodOps)
	errs := newErrSlots(len(plan) + 1)
	recs := executeSwapChain(m, bigCfg, plan, tags, errs)
	if err := errs.first(); err != nil {
		t.Fatalf("%v", err)
	}
	checkSwapChain(t, m, bigCfg, recs, tags)
}
