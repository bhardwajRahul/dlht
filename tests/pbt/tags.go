package pbt

import (
	"fmt"
	"sync/atomic"

	"github.com/jeremiah-masters/dlht"
)

// Tagged values.
//
// Every value written to the table under test is a unique uint64 tag that
// embeds the key it was written for: tag = key<<32 | seq, with seq drawn from
// a per-key atomic counter starting at 1. Uniqueness makes histories
// unambiguous (cheap to check) and makes two corruption classes detectable in
// O(1) at every observation point:
//
//   - cross-key leakage: a value observed via key k whose embedded key != k
//     (transfer writing into the wrong shard bin, out-of-bounds link writes,
//     GC reclaiming a live entry under the rotated layouts);
//   - ghost values: a value whose seq was never issued for that key.
//
// Tags cap the usable key space at 2^32 keys and 2^32 writes per key, far
// beyond anything these tests draw.

// tagStore issues and validates tagged values for keys in [0, numKeys).
type tagStore struct {
	issued []atomic.Uint64
}

func newTagStore(numKeys int) *tagStore {
	return &tagStore{issued: make([]atomic.Uint64, numKeys)}
}

// next returns a fresh unique tag for key.
func (s *tagStore) next(key uint64) uint64 {
	return key<<32 | s.issued[key].Add(1)
}

// validate checks an observed value against the tag invariants. The value
// must have been observed for key (via Get, a failed Insert's existing value,
// or a successful Put/Delete old value). Returns nil if the tag is well
// formed.
func (s *tagStore) validate(key, v uint64) error {
	if v>>32 != key {
		return fmt.Errorf("cross-key leakage: key %d returned value %#x stamped for key %d", key, v, v>>32)
	}
	seq := v & 0xFFFFFFFF
	if seq == 0 || seq > s.issued[key].Load() {
		return fmt.Errorf("ghost value: key %d returned value %#x with seq %d, issued up to %d",
			key, v, seq, s.issued[key].Load())
	}
	return nil
}

// quiescentDump collects the map contents via Range once all workers have
// joined. It reports an error on any duplicate key emission, which the Range
// contract forbids for a quiescent map.
func quiescentDump(m *dlht.Map[uint64, uint64]) (map[uint64]uint64, error) {
	out := make(map[uint64]uint64)
	var dup error
	m.Range(func(k, v uint64) bool {
		if _, seen := out[k]; seen && dup == nil {
			dup = fmt.Errorf("quiescent Range emitted key %d twice", k)
		}
		out[k] = v
		return true
	})
	return out, dup
}
