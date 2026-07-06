package pbt

import (
	"maps"
	"testing"

	"github.com/jeremiah-masters/dlht"

	"pgregory.net/rapid"
)

// initialSizeAxis sweeps resize counts (a fixed workload undergoes 0..many
// 8x/4x/2x growths depending on the starting size) and, as a side effect, the
// three aligned-allocation layout paths in the allocator (natural, rotated,
// large-object). 1..3 also cover the zero-link-arena edge (numBins/8 == 0).
var initialSizeAxis = []uint64{1, 2, 3, 8, 64, 512, 4096}

// Sequential model-based state machine. Every return value of every op
// is checked against map[K]int, and the final Range dump, Size, and Stats
// must agree with the model exactly (sequential execution is quiescent).
func runSequentialModelCheck[K dlht.Key](t *rapid.T, keyGen *rapid.Generator[K]) {
	initialSize := rapid.SampledFrom(initialSizeAxis).Draw(t, "initialSize")
	opsLen := rapid.IntRange(1, 512).Draw(t, "opsLen")
	valGen := rapid.IntRange(-1_000_000, 1_000_000)
	ops := GenOpSequence(keyGen, valGen, MixBalanced, opsLen, opsLen).Draw(t, "ops")

	m := dlht.New[K, int](dlht.Options{InitialSize: initialSize})
	model := make(map[K]int)
	var zero int

	for i, o := range ops {
		switch o.Kind {
		case OpGet:
			mv, mok := model[o.Key]
			v, ok := m.Get(o.Key)
			if ok != mok || (ok && v != mv) || (!ok && v != zero) {
				t.Fatalf("get mismatch key=%v model_found=%v map_found=%v model_val=%v map_val=%v",
					o.Key, mok, ok, mv, v)
			}
			if m.Contains(o.Key) != mok {
				t.Fatalf("contains mismatch key=%v model_found=%v", o.Key, mok)
			}
		case OpInsert:
			_, existed := model[o.Key]
			prev, ok := m.Insert(o.Key, o.Value)
			if existed {
				if ok || prev != model[o.Key] {
					t.Fatalf("insert mismatch key=%v existed=true ok=%v prev=%v model=%v",
						o.Key, ok, prev, model[o.Key])
				}
			} else {
				if !ok || prev != zero {
					t.Fatalf("insert mismatch key=%v existed=false ok=%v prev=%v expected_prev=%v",
						o.Key, ok, prev, zero)
				}
				model[o.Key] = o.Value
			}
		case OpPut:
			_, existed := model[o.Key]
			old, ok := m.Put(o.Key, o.Value)
			if existed {
				if !ok || old != model[o.Key] {
					t.Fatalf("put mismatch key=%v existed=true ok=%v old=%v model=%v",
						o.Key, ok, old, model[o.Key])
				}
				model[o.Key] = o.Value
			} else {
				if ok || old != zero {
					t.Fatalf("put mismatch key=%v existed=false ok=%v old=%v expected_old=%v",
						o.Key, ok, old, zero)
				}
			}
		case OpDelete:
			val, existed := model[o.Key]
			deleted, ok := m.Delete(o.Key)
			if existed {
				if !ok || deleted != val {
					t.Fatalf("delete mismatch key=%v existed=true ok=%v deleted=%v model=%v",
						o.Key, ok, deleted, val)
				}
				delete(model, o.Key)
			} else {
				if ok || deleted != zero {
					t.Fatalf("delete mismatch key=%v existed=false ok=%v deleted=%v expected_deleted=%v",
						o.Key, ok, deleted, zero)
				}
			}
		}
		// Periodic whole-table checks; cheap relative to the op loop and they
		// catch state damage close to the op that caused it.
		if i%64 == 63 {
			checkSequentialWholeTable(t, m, model)
		}
	}
	checkSequentialWholeTable(t, m, model)
}

func checkSequentialWholeTable[K dlht.Key](t *rapid.T, m *dlht.Map[K, int], model map[K]int) {
	if got := m.Size(); got != uint64(len(model)) {
		t.Fatalf("Size()=%d, model has %d entries", got, len(model))
	}
	dump := make(map[K]int, len(model))
	m.Range(func(k K, v int) bool {
		if _, seen := dump[k]; seen {
			t.Fatalf("Range emitted key %v twice", k)
		}
		dump[k] = v
		return true
	})
	if !maps.Equal(dump, model) {
		t.Fatalf("Range dump != model:\n  dump:  %v\n  model: %v", dump, model)
	}
	stats := m.Stats()
	if stats.Size != uint64(len(model)) {
		t.Fatalf("Stats().Size=%d, model has %d entries", stats.Size, len(model))
	}
	if stats.Resizing {
		t.Fatalf("Stats().Resizing=true at quiescence")
	}
	if stats.Size > stats.Capacity {
		t.Fatalf("Stats().Size=%d exceeds Capacity=%d", stats.Size, stats.Capacity)
	}
}

func TestPBTSequentialModel(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		keyspace := rapid.IntRange(1, 32).Draw(t, "keyspace")
		runSequentialModelCheck(t, GenStringKey(keyspace))
	})
}

func TestPBTSequentialModelUint64(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		keyspace := rapid.IntRange(1, 32).Draw(t, "keyspace")
		runSequentialModelCheck(t, GenUint64Key(keyspace))
	})
}

// structKey exercises maphash.Comparable over a composite comparable type.
type structKey struct {
	A uint32
	B int16
	C bool
}

func TestPBTSequentialModelStructKey(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		keyGen := rapid.Custom(func(t *rapid.T) structKey {
			return structKey{
				A: rapid.Uint32Range(0, 8).Draw(t, "a"),
				B: rapid.Int16Range(-2, 2).Draw(t, "b"),
				C: rapid.Bool().Draw(t, "c"),
			}
		})
		runSequentialModelCheck(t, keyGen)
	})
}

// Sequential cross-configuration differential, the deterministic form
// of orbit invariance. One op sequence runs against several maps that differ
// in InitialSize (and, implicitly, hash seed, since every instance draws its
// own) plus the model. Sequential execution is deterministic at the spec
// level, so every return value must be identical across all instances, op by
// op. A divergence convicts layout-, seed-, or resize-count-dependent logic
// and pins it to the exact op that exposed it.
func TestPBTSequentialCrossConfigDifferential(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		keyspace := rapid.IntRange(1, 48).Draw(t, "keyspace")
		opsLen := rapid.IntRange(1, 768).Draw(t, "opsLen")
		keyGen := GenUint64Key(keyspace)
		valGen := rapid.IntRange(-1_000_000, 1_000_000)
		ops := GenOpSequence(keyGen, valGen, MixChurn, opsLen, opsLen).Draw(t, "ops")

		instances := make([]*dlht.Map[uint64, int], len(initialSizeAxis))
		for i, size := range initialSizeAxis {
			instances[i] = dlht.New[uint64, int](dlht.Options{InitialSize: size})
		}
		model := make(map[uint64]int)

		for opIdx, o := range ops {
			wantRes, wantModel := applyToModel(model, o)
			model = wantModel
			for i, m := range instances {
				got := execOp(m, o)
				if got != wantRes {
					t.Fatalf("op %d %s(%d,%d): instance InitialSize=%d returned %+v, model expects %+v",
						opIdx, o.Kind, o.Key, o.Value, initialSizeAxis[i], got, wantRes)
				}
			}
		}

		want := make(map[uint64]int, len(model))
		maps.Copy(want, model)
		for i, m := range instances {
			dump := make(map[uint64]int, len(want))
			m.Range(func(k uint64, v int) bool {
				dump[k] = v
				return true
			})
			if !maps.Equal(dump, want) {
				t.Fatalf("final dump mismatch for InitialSize=%d:\n  dump:  %v\n  model: %v",
					initialSizeAxis[i], dump, want)
			}
			if got := m.Size(); got != uint64(len(want)) {
				t.Fatalf("Size mismatch for InitialSize=%d: got %d want %d", initialSizeAxis[i], got, len(want))
			}
		}
	})
}

// applyToModel computes the spec result of o against the model and the
// resulting model state.
func applyToModel(model map[uint64]int, o Op[uint64, int]) (OpResult[int], map[uint64]int) {
	cur, exists := model[o.Key]
	switch o.Kind {
	case OpGet:
		if exists {
			return OpResult[int]{Found: true, Value: cur}, model
		}
		return OpResult[int]{}, model
	case OpInsert:
		if exists {
			return OpResult[int]{Found: false, Value: cur}, model
		}
		model[o.Key] = o.Value
		return OpResult[int]{Found: true}, model
	case OpPut:
		if exists {
			model[o.Key] = o.Value
			return OpResult[int]{Updated: true, Value: cur}, model
		}
		return OpResult[int]{}, model
	case OpDelete:
		if exists {
			delete(model, o.Key)
			return OpResult[int]{Found: true, Value: cur}, model
		}
		return OpResult[int]{}, model
	default:
		panic("unknown op kind")
	}
}
