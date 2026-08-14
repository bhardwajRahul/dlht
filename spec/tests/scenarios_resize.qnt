// Directed resize interleavings (design §8; plan 1a Task 12). Instance
// `sys` is the 1gen tier (one resize, 3 bins, keys collide at gen0 and
// split across gen1's bins 2/3); `sys2` is the 2gen chain-walk tier (two
// resizes, 7 bins, keys collide at gen0 AND gen1, split at gen2).
//
// Daemon actions pick their bin via `nondet b = binDomain.oneOf()`: the
// evaluator resolves the choice against the guards (probe-confirmed), so a
// chain step is deterministic whenever exactly one bin is enabled, and the
// paired rsBegin/rsDone steps in the 2gen scenarios are order-insensitive
// by construction (no expect discriminates which bin went first).
module scenarios_resize {
  import types(
    procSet = Set("p1", "p2"),
    keyDomain = Set("k1", "k2"),
    valDomain = Set("v1", "v2"),
  ).* from "../types"

  import system(
    procSet = Set("p1", "p2"),
    keyDomain = Set("k1", "k2"),
    valDomain = Set("v1", "v2"),
    maxGen = 1,
    slotsPerBin = 2,
    hashRaw = Map("k1" -> 0, "k2" -> 1),
  ) as sys from "../system"

  import system(
    procSet = Set("p1", "p2"),
    keyDomain = Set("k1", "k2"),
    valDomain = Set("v1", "v2"),
    maxGen = 2,
    slotsPerBin = 2,
    hashRaw = Map("k1" -> 0, "k2" -> 2),
  ) as sys2 from "../system"

  // ------------------------- 1gen helpers ---------------------------------

  def retIs(p, okExpected, valExpected) = {
    match sys::ret.get(p) {
      | Some(r) => r.ok == okExpected and r.resVal == valExpected
      | _ => false
    }
  }

  // Invoke helpers mirror protocol::invokeLine EXACTLY, including the gen
  // reset to activeGen (Go's m.getActiveIndex() at op entry) — a scenario
  // that wants a LAGGARD op invokes it before the resize, then holds it.
  action invokeGet(p, k) = all {
    sys::pc.get(p) == sys::PcIdle,
    sys::pc' = sys::pc.set(p, sys::PcG1),
    sys::op' = sys::op.set(p, Some(Get)),
    sys::arg' = sys::arg.set(p, Some(KeyArg(k))),
    sys::ret' = sys::ret.set(p, None),
    sys::unchanged_shared,
    sys::local' = sys::local.set(p, sys::withGen(sys::local.get(p), sys::activeGen)),
    sys::unchanged_resize,
  }

  action invokeInsert(p, k, v) = all {
    sys::pc.get(p) == sys::PcIdle,
    sys::pc' = sys::pc.set(p, sys::PcI1),
    sys::op' = sys::op.set(p, Some(Insert)),
    sys::arg' = sys::arg.set(p, Some(KeyValArg((k, v)))),
    sys::ret' = sys::ret.set(p, None),
    sys::unchanged_shared,
    sys::local' = sys::local.set(p, sys::withGen(sys::local.get(p), sys::activeGen)),
    sys::unchanged_resize,
  }

  action invokePut(p, k, v) = all {
    sys::pc.get(p) == sys::PcIdle,
    sys::pc' = sys::pc.set(p, sys::PcP1),
    sys::op' = sys::op.set(p, Some(Put)),
    sys::arg' = sys::arg.set(p, Some(KeyValArg((k, v)))),
    sys::ret' = sys::ret.set(p, None),
    sys::unchanged_shared,
    sys::local' = sys::local.set(p, sys::withGen(sys::local.get(p), sys::activeGen)),
    sys::unchanged_resize,
  }

  action invokeDelete(p, k) = all {
    sys::pc.get(p) == sys::PcIdle,
    sys::pc' = sys::pc.set(p, sys::PcD1),
    sys::op' = sys::op.set(p, Some(Delete)),
    sys::arg' = sys::arg.set(p, Some(KeyArg(k))),
    sys::ret' = sys::ret.set(p, None),
    sys::unchanged_shared,
    sys::local' = sys::local.set(p, sys::withGen(sys::local.get(p), sys::activeGen)),
    sys::unchanged_resize,
  }

  action invokeLoadOrCompute(p, k, v, save) = all {
    sys::pc.get(p) == sys::PcIdle,
    sys::pc' = sys::pc.set(p, sys::PcLC1),
    sys::op' = sys::op.set(p, Some(LoadOrCompute)),
    sys::arg' = sys::arg.set(p, Some(LoadComputeArg((k, v, save)))),
    sys::ret' = sys::ret.set(p, None),
    sys::unchanged_shared,
    sys::local' = sys::local.set(p, sys::withGen(sys::local.get(p), sys::activeGen)),
    sys::unchanged_resize,
  }

  // Protocol steps inside the system need the daemon frame.
  action sysStep(a) = all { a, sys::unchanged_resize }

  action insertSuccess(p, k, v) =
    invokeInsert(p, k, v)
      .then(sysStep(sys::I1(p)))
      .then(sysStep(sys::I2(p)))
      .then(sysStep(sys::I3(p)))
      .then(sysStep(sys::I4(p)))
      .then(sysStep(sys::I5(p)))

  action deleteToD7(p, k) =
    invokeDelete(p, k)
      .then(sysStep(sys::D1(p)))
      .then(sysStep(sys::D2(p)))
      .then(sysStep(sys::D3(p)))
      .then(sysStep(sys::D4(p)))
      .then(sysStep(sys::D5(p)))
      .then(sysStep(sys::D6(p)))
      .then(sysStep(sys::D7(p)))

  action lcToShadow(p, k, v, save) =
    invokeLoadOrCompute(p, k, v, save)
      .then(sysStep(sys::LC1(p)))
      .then(sysStep(sys::LC2(p)))
      .then(sysStep(sys::LC3(p)))
      .then(sysStep(sys::LC4(p)))
      .then(sysStep(sys::LC5(p)))

  // ------------------------- 2gen helpers ---------------------------------

  def retIs2(p, okExpected, valExpected) = {
    match sys2::ret.get(p) {
      | Some(r) => r.ok == okExpected and r.resVal == valExpected
      | _ => false
    }
  }

  action invokeGet2(p, k) = all {
    sys2::pc.get(p) == sys2::PcIdle,
    sys2::pc' = sys2::pc.set(p, sys2::PcG1),
    sys2::op' = sys2::op.set(p, Some(Get)),
    sys2::arg' = sys2::arg.set(p, Some(KeyArg(k))),
    sys2::ret' = sys2::ret.set(p, None),
    sys2::unchanged_shared,
    sys2::local' = sys2::local.set(p, sys2::withGen(sys2::local.get(p), sys2::activeGen)),
    sys2::unchanged_resize,
  }

  action invokeInsert2(p, k, v) = all {
    sys2::pc.get(p) == sys2::PcIdle,
    sys2::pc' = sys2::pc.set(p, sys2::PcI1),
    sys2::op' = sys2::op.set(p, Some(Insert)),
    sys2::arg' = sys2::arg.set(p, Some(KeyValArg((k, v)))),
    sys2::ret' = sys2::ret.set(p, None),
    sys2::unchanged_shared,
    sys2::local' = sys2::local.set(p, sys2::withGen(sys2::local.get(p), sys2::activeGen)),
    sys2::unchanged_resize,
  }

  action invokeLoadOrCompute2(p, k, v, save) = all {
    sys2::pc.get(p) == sys2::PcIdle,
    sys2::pc' = sys2::pc.set(p, sys2::PcLC1),
    sys2::op' = sys2::op.set(p, Some(LoadOrCompute)),
    sys2::arg' = sys2::arg.set(p, Some(LoadComputeArg((k, v, save)))),
    sys2::ret' = sys2::ret.set(p, None),
    sys2::unchanged_shared,
    sys2::local' = sys2::local.set(p, sys2::withGen(sys2::local.get(p), sys2::activeGen)),
    sys2::unchanged_resize,
  }

  action sys2Step(a) = all { a, sys2::unchanged_resize }

  action insertSuccess2(p, k, v) =
    invokeInsert2(p, k, v)
      .then(sys2Step(sys2::I1(p)))
      .then(sys2Step(sys2::I2(p)))
      .then(sys2Step(sys2::I3(p)))
      .then(sys2Step(sys2::I4(p)))
      .then(sys2Step(sys2::I5(p)))

  action lcToShadow2(p, k, v, save) =
    invokeLoadOrCompute2(p, k, v, save)
      .then(sys2Step(sys2::LC1(p)))
      .then(sys2Step(sys2::LC2(p)))
      .then(sys2Step(sys2::LC3(p)))
      .then(sys2Step(sys2::LC4(p)))
      .then(sys2Step(sys2::LC5(p)))

  // ========================== 1gen scenarios ===============================

  // 1. Full transfer cycle; a get invoked pre-finalize chain-walks past the
  // Done gen-0 bin and reads the moved entry in gen 1.
  run resize_basic_full_cycle =
    sys::systemInit
      .then(insertSuccess("p1", "k1", "v1"))
      .expect(retIs("p1", true, None))
      .then(sys::rsTrigger)
      .then(sys::rsBegin)
      .expect(sys::inv and sys::rsInv)
      .then(sys::rsSentinel)
      .then(sys::rsMove)
      .expect(sys::inv and sys::rsInv)
      .then(sys::rsDone)
      .expect(sys::inv and sys::rsInv)
      .expect(sys::header.get(1).binState == sys::DoneTransfer)
      // invoked BEFORE finalize: starts at gen 0 and must walk
      .then(invokeGet("p1", "k1"))
      .then(sys::rsFinalize)
      .expect(sys::inv and sys::rsInv and sys::activeGen == 1)
      .then(sysStep(sys::G1("p1")))
      .expect(sys::pc.get("p1") == sys::PcG1 and sys::local.get("p1").gen == 1)
      .then(sysStep(sys::G1("p1")))
      .then(sysStep(sys::G2("p1")))
      .expect(retIs("p1", true, Some("v1")))
      .expect(sys::readVisibleByHeader(sys::header.get(2), 2, "k1") == Some("v1"))
      .expect(sys::inv and sys::rsInv)

  // 2. THE canonical carried-Put: h0/hLoop captured pre-OR, P6 fails on the
  // binState flip, P4 reloads mid-transfer (NO binState check — put.go),
  // and the DWCAS linearizes BEFORE the sentinel; rsMove carries the new
  // value.
  run resize_put_carried_pre_sentinel =
    sys::systemInit
      .then(insertSuccess("p1", "k1", "v1"))
      .then(invokePut("p1", "k1", "v2"))
      .then(sysStep(sys::P1("p1")))
      .then(sysStep(sys::P2("p1")))
      .then(sysStep(sys::P3("p1")))
      .then(sysStep(sys::P4("p1")))
      .then(sysStep(sys::P5("p1")))
      .expect(sys::pc.get("p1") == sys::PcP6)
      .then(sys::rsTrigger)
      .then(sys::rsBegin)
      // P6 fails: hLoop has NoTransfer, live is InTransfer (same version!)
      .then(sysStep(sys::P6("p1")))
      .expect(sys::pc.get("p1") == sys::PcP4)
      .then(sysStep(sys::P4("p1")))      // reload mid-transfer — legal
      .then(sysStep(sys::P5("p1")))      // slot not yet sentineled
      .then(sysStep(sys::P6("p1")))      // hLoop == live (both InTransfer)
      .expect(sys::pc.get("p1") == sys::PcP7)
      .then(sysStep(sys::P7("p1")))      // DWCAS succeeds mid-transfer
      .expect(retIs("p1", true, Some("v1")))
      .expect(sys::inv and sys::rsInv)
      .then(sys::rsSentinel)
      .then(sys::rsMove)                  // carries the POST-Put entry (v2)
      .then(sys::rsDone)
      .then(sys::rsFinalize)
      .expect(sys::inv and sys::rsInv)
      .then(invokeGet("p1", "k1"))
      .then(sysStep(sys::G1("p1")))
      .then(sysStep(sys::G2("p1")))
      .expect(retIs("p1", true, Some("v2")))
      .expect(sys::inv and sys::rsInv)

  // 3. Put arriving POST-sentinel loses the race: P1's classification spins
  // on InTransfer, walks after Done, and the update lands in gen 1.
  run resize_put_loses_post_sentinel =
    sys::systemInit
      .then(insertSuccess("p1", "k1", "v1"))
      .then(sys::rsTrigger)
      .then(sys::rsBegin)
      .then(sys::rsSentinel)
      .then(invokePut("p1", "k1", "v2"))
      .then(sysStep(sys::P1("p1")))       // InTransfer: spin (gen := activeGen = 0)
      .expect(sys::pc.get("p1") == sys::PcP1 and sys::local.get("p1").gen == 0)
      .then(sys::rsMove)
      .then(sys::rsDone)
      .then(sysStep(sys::P1("p1")))       // Done: walk to gen 1
      .expect(sys::pc.get("p1") == sys::PcP1 and sys::local.get("p1").gen == 1)
      .then(sysStep(sys::P1("p1")))
      .then(sysStep(sys::P2("p1")))       // finds the carried k1 in bin 2
      .then(sysStep(sys::P3("p1")))
      .then(sysStep(sys::P4("p1")))
      .then(sysStep(sys::P5("p1")))
      .then(sysStep(sys::P6("p1")))
      .then(sysStep(sys::P7("p1")))
      .expect(retIs("p1", true, Some("v1")))
      .then(sys::rsFinalize)
      .then(invokeGet("p1", "k1"))
      .then(sysStep(sys::G1("p1")))
      .then(sysStep(sys::G2("p1")))
      .expect(retIs("p1", true, Some("v2")))
      .expect(sys::inv and sys::rsInv)

  // 4. Open delete window carried as ABSENT: the D7-cleared entry is
  // sentineled then skipped by rsMove; rsDone resurrects the Valid bit in
  // the dead header; the straggler D8 still ANDs the dead header (faithful).
  run resize_delete_window_carried_as_absent =
    sys::systemInit
      .then(insertSuccess("p1", "k1", "v1"))
      .then(deleteToD7("p1", "k1"))
      .expect(retIs("p1", true, Some("v1")) and sys::pc.get("p1") == sys::PcD8)
      .then(sys::rsTrigger)
      .then(sys::rsBegin)
      .then(sys::rsSentinel)              // parked deleter's slot IS sentineled
      .expect(sys::slotKey.get(1).get(1) == Some(HSentinel))
      .expect(sys::inv)                    // retAtD8's sentinel arm holds here
      .then(sys::rsMove)                   // val None: skipped (deleted)
      .then(sys::rsDone)
      .expect(sys::header.get(1).slotState.get(1) == sys::Valid)  // restored
      .then(sysStep(sys::D8("p1")))        // straggler ANDs the DEAD header
      .expect(sys::header.get(1).slotState.get(1) == sys::Invalid)
      .expect(sys::header.get(1).binState == sys::DoneTransfer)
      .then(sys::rsFinalize)
      .then(invokeGet("p1", "k1"))
      .then(sysStep(sys::G1("p1")))
      .then(sysStep(sys::G2("p1")))
      .expect(retIs("p1", false, None))
      .expect(sys::inv and sys::rsInv)

  // 5. Insert abandon-and-redirect: I5 fails on the binState flip, the I6
  // unreserve REFUSES (bin InTransfer) leaving the Trying slot abandoned,
  // and the insert re-classifies into gen 1 (bin 3 for k2).
  run resize_insert_abandons_and_redirects =
    sys::systemInit
      .then(insertSuccess("p1", "k1", "v1"))
      .then(invokeInsert("p2", "k2", "v2"))
      .then(sysStep(sys::I1("p2")))
      .then(sysStep(sys::I2("p2")))
      .then(sysStep(sys::I3("p2")))        // reserve slot 2 (Trying)
      .then(sysStep(sys::I4("p2")))        // fill
      .expect(sys::pc.get("p2") == sys::PcI5)
      .then(sys::rsTrigger)
      .then(sys::rsBegin)                  // snapshot sees slot 2 Trying — skipped
      .then(sysStep(sys::I5("p2")))        // finalize CAS fails (binState changed)
      .expect(sys::pc.get("p2") == sys::PcI6)
      .then(sysStep(sys::I6("p2")))        // REFUSAL: bin InTransfer — abandoned
      .expect(
        sys::header.get(1).slotState.get(2) == sys::Trying and
          sys::pc.get("p2") == sys::PcI1 and sys::ret.get("p2") == None
      )
      .then(sysStep(sys::I1("p2")))        // InTransfer: classify-spin
      .expect(sys::pc.get("p2") == sys::PcI1 and sys::local.get("p2").gen == 0)
      .then(sys::rsSentinel)
      .then(sys::rsMove)                   // k1 -> bin 2
      .then(sys::rsDone)                   // restore: slot 2 stays Trying in the dead bin
      .then(sysStep(sys::I1("p2")))        // Done: walk to gen 1
      .expect(sys::local.get("p2").gen == 1)
      .then(sysStep(sys::I1("p2")))
      .then(sysStep(sys::I2("p2")))        // bin 3, fresh slot
      .then(sysStep(sys::I3("p2")))
      .then(sysStep(sys::I4("p2")))
      .then(sysStep(sys::I5("p2")))
      .expect(retIs("p2", true, None))
      .then(sys::rsFinalize)
      .expect(sys::header.get(1).slotState.get(2) == sys::Trying)  // abandoned forever
      .then(invokeGet("p1", "k1"))
      .then(sysStep(sys::G1("p1")))
      .then(sysStep(sys::G2("p1")))
      .expect(retIs("p1", true, Some("v1")))
      .then(invokeGet("p2", "k2"))
      .then(sysStep(sys::G1("p2")))
      .then(sysStep(sys::G2("p2")))
      .expect(retIs("p2", true, Some("v2")))
      .expect(sys::inv and sys::rsInv)

  // 5b. FILL-AFTER-OR (design §8 — distinct from scenario 5's
  // reserve-then-fill-then-OR): the reserve lands pre-OR, the snapshot
  // captures the Trying slot, and I4's UNGUARDED fill then writes key/val/
  // tag INTO the InTransfer bin. The finalize CAS still fails on the
  // binState flip, the unreserve refuses, and the redirect proceeds as in
  // scenario 5 — the mid-transfer write is harmless because snapshot-Trying
  // slots are never transferable.
  run resize_insert_fill_after_or_abandons =
    sys::systemInit
      .then(insertSuccess("p1", "k1", "v1"))
      .then(invokeInsert("p2", "k2", "v2"))
      .then(sysStep(sys::I1("p2")))
      .then(sysStep(sys::I2("p2")))
      .then(sysStep(sys::I3("p2")))        // reserve slot 2 pre-OR
      .expect(sys::pc.get("p2") == sys::PcI4)
      .then(sys::rsTrigger)
      .then(sys::rsBegin)                  // snapshot: slot 1 Valid, slot 2 Trying
      .then(sysStep(sys::I4("p2")))        // the fill lands MID-TRANSFER
      .expect(
        sys::header.get(1).binState == sys::InTransfer and
          sys::slotKey.get(1).get(2) == Some(HKey("k2")) and
          sys::slotVal.get(1).get(2) != None
      )
      .expect(sys::inv and sys::rsInv)
      .then(sysStep(sys::I5("p2")))        // finalize CAS fails (binState changed)
      .expect(sys::pc.get("p2") == sys::PcI6)
      .then(sysStep(sys::I6("p2")))        // REFUSAL: abandoned with the ghost fill
      .expect(sys::header.get(1).slotState.get(2) == sys::Trying)
      .then(sys::rsSentinel)
      .then(sys::rsMove)                   // k1 only; the Trying slot is not transferable
      .then(sys::rsDone)
      .then(sysStep(sys::I1("p2")))        // Done: walk to gen 1
      .expect(sys::local.get("p2").gen == 1)
      .then(sysStep(sys::I1("p2")))
      .then(sysStep(sys::I2("p2")))
      .then(sysStep(sys::I3("p2")))
      .then(sysStep(sys::I4("p2")))
      .then(sysStep(sys::I5("p2")))
      .expect(retIs("p2", true, None))
      .then(sys::rsFinalize)
      .then(invokeGet("p2", "k2"))
      .then(sysStep(sys::G1("p2")))
      .then(sysStep(sys::G2("p2")))
      .expect(retIs("p2", true, Some("v2")))
      .expect(sys::inv and sys::rsInv)

  // 6. LC holder relocation, commit path: the Shadow claim is carried to
  // bin 2 (claim continuity at every daemon step), the holder relocates via
  // PcLC10 and commits in gen 1.
  run resize_lc_commit_relocates =
    sys::systemInit
      .then(lcToShadow("p1", "k1", "v1", true))
      .expect(sys::pc.get("p1") == sys::PcLC6)
      .then(sys::rsTrigger)
      .then(sys::rsBegin)
      .expect(sys::inv and sys::rsInv)
      .then(sys::rsShadowCarry)            // Shadow -> bin 2 (no sentinel)
      .expect(sys::inv and sys::rsInv)     // the carry window: gen-aware ownership
      .expect(sys::header.get(2).slotState.get(1) == sys::Shadow)
      .then(sys::rsDone)
      .expect(sys::inv and sys::rsInv)
      .then(sysStep(sys::LC6("p1")))       // Done: relocate
      .expect(sys::pc.get("p1") == sys::PcLC10)
      .then(sysStep(sys::LC10("p1")))      // finds Shadow+HKey(k1) in bin 2
      .expect(
        sys::pc.get("p1") == sys::PcLC6 and
          sys::local.get("p1").gen == 1 and
          sys::local.get("p1").targetSlot == 1
      )
      .then(sysStep(sys::LC6("p1")))       // bin 2 NoTransfer: proceed
      .then(sysStep(sys::LC7("p1")))       // commit in gen 1
      .expect(retIs("p1", false, Some("v1")))
      .then(sys::rsFinalize)
      .then(invokeGet("p2", "k1"))
      .then(sysStep(sys::G1("p2")))
      .then(sysStep(sys::G2("p2")))
      .expect(retIs("p2", true, Some("v1")))
      .expect(sys::inv and sys::rsInv)

  // 7. LC holder relocation, abort path (save=false): the relocated holder
  // posts its result in gen 1 (LC7 abort) and LC9 cleans the carried ghost.
  run resize_lc_abort_relocates =
    sys::systemInit
      .then(lcToShadow("p1", "k1", "v1", false))
      .then(sys::rsTrigger)
      .then(sys::rsBegin)
      .then(sys::rsShadowCarry)
      .expect(sys::inv and sys::rsInv)
      .then(sys::rsDone)
      .then(sysStep(sys::LC6("p1")))
      .then(sysStep(sys::LC10("p1")))
      .expect(sys::pc.get("p1") == sys::PcLC6 and sys::local.get("p1").gen == 1)
      .then(sysStep(sys::LC6("p1")))
      .then(sysStep(sys::LC7("p1")))       // abort phase 1: ret posted, Shadow->Trying
      .expect(sys::pc.get("p1") == sys::PcLC9 and retIs("p1", false, Some("v1")))
      .then(sysStep(sys::LC9("p1")))       // cleanup in the NoTransfer gen-1 bin
      .expect(sys::header.get(2).slotState.get(1) == sys::Invalid)
      .then(sys::rsFinalize)
      .then(invokeGet("p2", "k1"))
      .then(sysStep(sys::G1("p2")))
      .then(sysStep(sys::G2("p2")))
      .expect(retIs("p2", false, None))
      .expect(sys::inv and sys::rsInv)

  // 9. Cross-bin isolation, re-landed POST-resize (ports the retired 2-bin
  // coverage): after one full cycle k1 lives in bin 2 and k2 in bin 3; an
  // open delete window in bin 2 leaves bin 3 reads untouched.
  run resize_cross_bin_isolated =
    sys::systemInit
      .then(insertSuccess("p1", "k1", "v1"))
      .then(insertSuccess("p2", "k2", "v2"))
      .then(sys::rsTrigger)
      .then(sys::rsBegin)
      .then(sys::rsSentinel)
      .then(sys::rsMove)                   // k1 -> bin 2
      .then(sys::rsSentinel)
      .then(sys::rsMove)                   // k2 -> bin 3
      .then(sys::rsDone)
      .then(sys::rsFinalize)
      .expect(sys::inv and sys::rsInv)
      .then(deleteToD7("p1", "k1"))        // window OPEN in bin 2
      .expect(
        sys::pc.get("p1") == sys::PcD8 and
          sys::header.get(2).slotState.get(1) == sys::Valid and
          sys::slotVal.get(2).get(1) == None
      )
      .then(invokeGet("p2", "k2"))
      .then(sysStep(sys::G1("p2")))
      .then(sysStep(sys::G2("p2")))
      .expect(retIs("p2", true, Some("v2")))   // bin 3 untouched mid-window
      .then(sysStep(sys::D8("p1")))
      .expect(sys::readVisibleByHeader(sys::header.get(2), 2, "k1") == None)
      .expect(sys::readVisibleByHeader(sys::header.get(3), 3, "k2") == Some("v2"))
      .expect(sys::inv and sys::rsInv)

  // 11. The snapStateAgrees RESURRECTION interleaving (design §8): a P4
  // hLoop captured mid-transfer AFTER a transfer-window D8 clear, vs. the
  // restored header whose Valid bit rsDone resurrected — equal versions,
  // non-clear disagreement, exempt ONLY via the NoTransfer-snapshot
  // antecedent. Pins the adjusted family.
  run resize_snapstate_resurrection =
    sys::systemInit
      .then(insertSuccess("p1", "k1", "v1"))
      .then(insertSuccess("p2", "k2", "v2"))
      .then(invokePut("p1", "k1", "v2"))
      .then(sysStep(sys::P1("p1")))
      .then(sysStep(sys::P2("p1")))
      .then(sysStep(sys::P3("p1")))
      .then(sysStep(sys::P4("p1")))
      .then(sysStep(sys::P5("p1")))        // hLoop: NoTransfer, both Valid
      .expect(sys::pc.get("p1") == sys::PcP6)
      .then(deleteToD7("p2", "k2"))        // k2's window: val/tag None, header-silent
      .expect(retIs("p2", true, Some("v2")))
      .then(sys::rsTrigger)
      .then(sys::rsBegin)                  // snapshot: slots 1,2 Valid (slot 2 val None)
      .then(sysStep(sys::P6("p1")))        // fails: binState flipped
      .expect(sys::pc.get("p1") == sys::PcP4)
      .then(sysStep(sys::D8("p2")))        // D8 on the LIVE InTransfer header
      .expect(sys::header.get(1).slotState.get(2) == sys::Invalid)
      .then(sysStep(sys::P4("p1")))        // hLoop := InTransfer header, slot 2 Invalid
      .then(sysStep(sys::P5("p1")))        // slot 1 untouched: capture again
      .expect(sys::pc.get("p1") == sys::PcP6)
      .then(sys::rsSentinel)               // slot 1
      .then(sys::rsMove)                   // {k1,v1} -> bin 2
      .then(sys::rsSentinel)               // slot 2 (snap-Valid, key still HKey)
      .then(sys::rsMove)                   // val None: skip
      .then(sys::rsDone)                   // RESURRECTS slot 2's Valid bit
      .expect(sys::header.get(1).slotState.get(2) == sys::Valid)
      .expect(sys::inv and sys::rsInv)     // hLoop straddles: exempt via InTransfer snap
      .then(sys::rsFinalize)
      .then(sysStep(sys::P6("p1")))        // hLoop (InTransfer) vs live (Done): fail
      .expect(sys::pc.get("p1") == sys::PcP4)
      .then(sysStep(sys::P4("p1")))        // dead-header hLoop (P4 has no check)
      .then(sysStep(sys::P5("p1")))        // slot 1 sentineled: RETRY
      .expect(sys::pc.get("p1") == sys::PcP1)
      .then(sysStep(sys::P1("p1")))        // Done: walk to gen 1
      .expect(sys::local.get("p1").gen == 1)
      .then(sysStep(sys::P1("p1")))
      .then(sysStep(sys::P2("p1")))
      .then(sysStep(sys::P3("p1")))
      .then(sysStep(sys::P4("p1")))
      .then(sysStep(sys::P5("p1")))
      .then(sysStep(sys::P6("p1")))
      .then(sysStep(sys::P7("p1")))        // completes the Put on the carried entry
      .expect(retIs("p1", true, Some("v1")))
      .then(invokeGet("p1", "k1"))
      .then(sysStep(sys::G1("p1")))
      .then(sysStep(sys::G2("p1")))
      .expect(retIs("p1", true, Some("v2")))
      .then(invokeGet("p2", "k2"))
      .then(sysStep(sys::G1("p2")))
      .then(sysStep(sys::G2("p2")))
      .expect(retIs("p2", false, None))
      .expect(sys::inv and sys::rsInv)

  // ========================== 2gen scenarios ===============================

  // 8. The laggard double-walk (design D3's raison d'être): a get invoked at
  // gen 0 sleeps through TWO complete resizes, then chain-walks gen0 ->
  // gen1 -> gen2, one generation per classification — never a jump.
  run resize_laggard_double_walk =
    sys2::systemInit
      .then(insertSuccess2("p1", "k1", "v1"))
      .then(invokeGet2("p2", "k1"))        // parked at PcG1, gen 0
      .expect(sys2::local.get("p2").gen == 0)
      // resize #1: gen0 (bin 1) -> gen1
      .then(sys2::rsTrigger)
      .then(sys2::rsBegin)
      .then(sys2::rsSentinel)
      .then(sys2::rsMove)                  // k1 -> bin 2
      .then(sys2::rsDone)
      .then(sys2::rsFinalize)
      .expect(sys2::inv and sys2::rsInv and sys2::activeGen == 1)
      // resize #2: gen1 (bins 2,3) -> gen2
      .then(sys2::rsTrigger)
      .then(sys2::rsBegin)
      .then(sys2::rsBegin)                 // both gen-1 bins InTransfer (either order)
      .then(sys2::rsSentinel)              // only bin 2 has content
      .then(sys2::rsMove)                  // k1 -> bin 4
      .then(sys2::rsDone)
      .then(sys2::rsDone)                  // bins 2 and 3, either order
      .then(sys2::rsFinalize)
      .expect(sys2::inv and sys2::rsInv and sys2::activeGen == 2)
      // the laggard wakes: one generation per walk step
      .then(sys2Step(sys2::G1("p2")))
      .expect(sys2::pc.get("p2") == sys2::PcG1 and sys2::local.get("p2").gen == 1)
      .then(sys2Step(sys2::G1("p2")))
      .expect(sys2::pc.get("p2") == sys2::PcG1 and sys2::local.get("p2").gen == 2)
      .then(sys2Step(sys2::G1("p2")))
      .then(sys2Step(sys2::G2("p2")))
      .expect(retIs2("p2", true, Some("v1")))
      .expect(sys2::readVisibleByHeader(sys2::header.get(4), 4, "k1") == Some("v1"))
      .expect(sys2::inv and sys2::rsInv)

  // 10. Holder DOUBLE-relocation (design §8): the claim is carried twice
  // (gen0 -> gen1 -> gen2) with the holder relocating behind it, spinning
  // through bin 2's own transfer in between.
  run resize_holder_double_relocation =
    sys2::systemInit
      .then(lcToShadow2("p1", "k1", "v1", true))
      .expect(sys2::pc.get("p1") == sys2::PcLC6)
      // resize #1 carries the claim; the holder does NOT run
      .then(sys2::rsTrigger)
      .then(sys2::rsBegin)
      .then(sys2::rsShadowCarry)           // Shadow -> bin 2
      .expect(sys2::inv and sys2::rsInv)
      .then(sys2::rsDone)
      .expect(sys2::inv and sys2::rsInv)
      .then(sys2::rsFinalize)
      .expect(sys2::inv and sys2::rsInv)
      // resize #2 begins immediately
      .then(sys2::rsTrigger)
      .then(sys2::rsBegin)
      .then(sys2::rsBegin)                 // bins 2 and 3 InTransfer
      .expect(sys2::inv and sys2::rsInv)
      // the holder finally runs: relocate once, then SPIN on InTransfer
      .then(sys2Step(sys2::LC6("p1")))     // gen-0 bin Done -> PcLC10
      .expect(sys2::pc.get("p1") == sys2::PcLC10)
      .then(sys2Step(sys2::LC10("p1")))    // finds the bin-2 claim (mid-transfer)
      .expect(sys2::pc.get("p1") == sys2::PcLC6 and sys2::local.get("p1").gen == 1)
      .then(sys2Step(sys2::LC6("p1")))     // bin 2 InTransfer: SPIN
      .expect(sys2::pc.get("p1") == sys2::PcLC6 and sys2::local.get("p1").gen == 1)
      .then(sys2::rsShadowCarry)           // claim -> bin 4 (gen 2)
      .expect(sys2::inv and sys2::rsInv)   // double-carried claim still owned
      .then(sys2::rsDone)
      .then(sys2::rsDone)                  // bins 2 and 3, either order
      .expect(sys2::inv and sys2::rsInv)
      .then(sys2Step(sys2::LC6("p1")))     // gen-1 bin Done -> PcLC10 again
      .expect(sys2::pc.get("p1") == sys2::PcLC10)
      .then(sys2Step(sys2::LC10("p1")))    // finds the bin-4 claim
      .expect(sys2::pc.get("p1") == sys2::PcLC6 and sys2::local.get("p1").gen == 2)
      .then(sys2Step(sys2::LC6("p1")))     // bin 4 NoTransfer: proceed
      .then(sys2Step(sys2::LC7("p1")))     // commit in gen 2
      .expect(retIs2("p1", false, Some("v1")))
      .then(sys2::rsFinalize)
      .expect(sys2::inv and sys2::rsInv and sys2::activeGen == 2)
      .then(invokeGet2("p2", "k1"))
      .then(sys2Step(sys2::G1("p2")))
      .then(sys2Step(sys2::G2("p2")))
      .expect(retIs2("p2", true, Some("v1")))
      .expect(sys2::readVisibleByHeader(sys2::header.get(4), 4, "k1") == Some("v1"))
      .expect(sys2::inv and sys2::rsInv)
}
