// Package pbt holds the metamorphic and property-based test suite for DLHT.
//
// What lives where:
//
//	sequential_property_test.go      model-based state machine; cross-config differential
//	orbit_grid_test.go               schedule invariance on order-determinate workloads
//	swap_chain_test.go               per-key conservation of displaced values, plus the soak
//	tags.go                          self-describing tagged values (used by most oracles)
//	checkpoint_immutability_test.go  checkpoint stability under resize churn and GC storms
//	iter_property_test.go            iterator guarantees under churn and resize
//	session_monotonic_test.go        monotonic reads / read-your-writes on single-writer keys
//	barrier_invariance_test.go       barrier-insertion invariance (refinement direction only)
//	size_stats_bounds_test.go        Size/Stats bounds and quiescent exactness
//	cross_impl_test.go               allocator vs inline map differential
//	liveness_smoke_test.go           progress canary under oversubscription
//
// Hash-aware geometry tests (bin pileups, arena exhaustion, split-bit
// cohorts) live in package allocator (allocator/resize_test.go) because they
// need the per-instance hash seed.
//
// Ground rules:
//
//   - Concurrent tests here must NOT run under -race: the seqlock's plain
//     slot loads race with the transfer's sentinel stores by design, and the
//     detector flags them on a correct implementation. Sequential tests are
//     race-clean.
//   - rapid.T is not goroutine-safe: draw the full workload first, execute
//     with plain goroutines, assert after joining (draw-then-run). Worker
//     goroutines report failures through errSlots, never t.Fatalf.
//   - Contention-heavy concurrent properties re-execute each drawn case a few
//     times (repeat-R): schedule nondeterminism means one quiet run proves
//     little and shrinking needs reproducibility. Phase-quiescent tests
//     (barrier, sandwich) and tests with internal repetition (iterator,
//     soaks) intentionally skip it.
//   - GOMAXPROCS is a per-test sweep axis (gomaxprocsAxis), not a package
//     pin: 1 exercises cooperative-yield paths, NumCPU buys real races.
//
// Known gaps:
//
//   - The cross-implementation differential is sequential only; a
//     determinate concurrent comparison against the inline map is future
//     work.
//   - The orbit grid's goroutine axis tops out at 8; oversubscription beyond
//     NumCPU is left to the liveness canary and the session soak.
//   - The split-bit geometry test asserts exact final state but does not run
//     the conservation or tag oracles alongside.
//   - A reader parked across two consecutive resizes (skipping a generation
//     in the indexNext chain) is only probabilistically exercised by the
//     session soak; hitting that window deterministically needs scheduler
//     control Go does not offer.
package pbt
