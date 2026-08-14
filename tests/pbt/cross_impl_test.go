package pbt

import (
	"maps"
	"testing"

	"github.com/jeremiah-masters/dlht"
	"github.com/jeremiah-masters/dlht/inline"

	"pgregory.net/rapid"
)

// Cross-implementation equivalence. The allocator-backed map and the
// inline map implement the same table, so two independent implementations
// are each other's oracle. One sequential op stream runs against both plus
// the model; every comparable return value must agree op by op, and the
// final dumps must be identical. The inline Delete returns only success, so
// its old value is checked on the allocator side alone.
func TestPBTCrossImplementationEquivalence(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		initialSize := rapid.SampledFrom(initialSizeAxis).Draw(t, "initialSize")
		keyspace := rapid.IntRange(1, 48).Draw(t, "keyspace")
		opsLen := rapid.IntRange(1, 512).Draw(t, "opsLen")

		ma := dlht.New[uint64, uint64](dlht.Options{InitialSize: initialSize})
		mi := inline.New[uint64](inline.Options{InitialSize: initialSize})
		model := make(map[uint64]uint64)

		for i := 0; i < opsLen; i++ {
			kind := DrawOpKind(t, MixChurn)
			key := uint64(rapid.IntRange(0, keyspace-1).Draw(t, "key"))
			val := rapid.Uint64().Draw(t, "val")

			cur, exists := model[key]
			switch kind {
			case OpGet:
				av, aok := ma.Get(key)
				iv, iok := mi.Get(key)
				if aok != exists || iok != exists || (exists && (av != cur || iv != cur)) {
					t.Fatalf("op %d Get(%d): allocator=(%d,%v) inline=(%d,%v) model=(%d,%v)",
						i, key, av, aok, iv, iok, cur, exists)
				}
			case OpInsert:
				aprev, aok := ma.Insert(key, val)
				iprev, iok := mi.Insert(key, val)
				wantOK := !exists
				if aok != wantOK || iok != wantOK {
					t.Fatalf("op %d Insert(%d): allocator ok=%v inline ok=%v model expects %v",
						i, key, aok, iok, wantOK)
				}
				if exists && (aprev != cur || iprev != cur) {
					t.Fatalf("op %d Insert(%d) existing: allocator prev=%d inline prev=%d model=%d",
						i, key, aprev, iprev, cur)
				}
				if !exists {
					model[key] = val
				}
			case OpPut:
				aold, aok := ma.Put(key, val)
				iold, iok := mi.Put(key, val)
				if aok != exists || iok != exists {
					t.Fatalf("op %d Put(%d): allocator ok=%v inline ok=%v model expects %v",
						i, key, aok, iok, exists)
				}
				if exists && (aold != cur || iold != cur) {
					t.Fatalf("op %d Put(%d): allocator old=%d inline old=%d model=%d",
						i, key, aold, iold, cur)
				}
				if exists {
					model[key] = val
				}
			case OpDelete:
				aold, aok := ma.Delete(key)
				iok := mi.Delete(key)
				if aok != exists || iok != exists {
					t.Fatalf("op %d Delete(%d): allocator ok=%v inline ok=%v model expects %v",
						i, key, aok, iok, exists)
				}
				if exists && aold != cur {
					t.Fatalf("op %d Delete(%d): allocator old=%d model=%d", i, key, aold, cur)
				}
				delete(model, key)
			}
		}

		wantSize := uint64(len(model))
		if got := ma.Size(); got != wantSize {
			t.Fatalf("allocator Size()=%d, model %d", got, wantSize)
		}
		if got := mi.Size(); got != wantSize {
			t.Fatalf("inline Size()=%d, model %d", got, wantSize)
		}

		aDump := make(map[uint64]uint64, len(model))
		ma.Range(func(k, v uint64) bool { aDump[k] = v; return true })
		iDump := make(map[uint64]uint64, len(model))
		mi.Range(func(k, v uint64) bool { iDump[k] = v; return true })
		if !maps.Equal(aDump, model) {
			t.Fatalf("allocator dump != model:\n  dump:  %v\n  model: %v", aDump, model)
		}
		if !maps.Equal(iDump, model) {
			t.Fatalf("inline dump != model:\n  dump:  %v\n  model: %v", iDump, model)
		}
	})
}
