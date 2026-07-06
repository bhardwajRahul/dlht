// Daemon-var anchor-coverage control (1b) — the silent-unsoundness hazard of
// probes/undercover.qnt, extended to the resize DAEMON vars (snapshot/cursor).
//
// Stage 1b's system anchor (system_induction.qnt::systemIndInit) must
// construct snapshot over its FULL space — a per-bin present-bit AND a full
// Header (snapPresent / snapVer / snapBS / snapSS) — and cursor as a full Int.
// If it under-covered any of those dimensions, a non-inductive rsInv conjunct
// whose break needs that dimension would pass consecution VACUOUSLY.
//
// This minimal model isolates the snapshot present-bit: many rsInv conjuncts
// (R6 rsSnapshotRelation, R7 rsSentinelDiscipline, R11 rsCompleteness, R12b
// rsChildFreeSlot) and the daemon steps (rsMove/rsShadowCarry/rsDone) are
// enabled/relevant ONLY when a snapshot is present. Omitting the present-bit
// nondet would hide every break that requires snapshot.get(b) != None.
//
// Demonstrate (after the consecution tier frees Apalache; ONE verify at a time):
//   quint verify probes/undercover_daemon.qnt --init=indInitBad  --step=step --invariant=inv --max-steps=1
//       => [ok]        -- FALSE pass: the present-snapshot break is never constructed
//   quint verify probes/undercover_daemon.qnt --init=indInitGood --step=step --invariant=inv --max-steps=1
//       => [violation] -- the real break, found only when the present-bit is covered
module undercover_daemon {
  var x: int
  var snapPresent: bool   // models a bin's snapshot present-bit (Option[Header] != None)

  // UNDER-COVERING anchor: forgets to nondet the snapshot present-bit and
  // hardcodes "absent" — exactly the omission that would make rsInv's
  // snapshot-keyed conjuncts vacuously inductive.
  action indInitBad = {
    nondet c = Nat.oneOf()
    all { c <= 3, x' = c, snapPresent' = false }   // present-snapshot states NEVER constructed
  }
  // FULL anchor (what systemIndInit actually does for snapPresent): covers both.
  action indInitGood = {
    nondet c = Nat.oneOf()
    nondet sp = Bool.oneOf()
    all { c <= 3, x' = c, snapPresent' = sp }
  }

  // The hidden break fires only when a snapshot is present — like a daemon
  // step (rsMove/rsDone) or a snapshot-keyed family that is relevant only on
  // snapshot.get(b) != None.
  action step = any {
    all { snapPresent, x == 3, x' = 5, snapPresent' = snapPresent },   // the hidden break
    all { not(snapPresent and x == 3), x' = x, snapPresent' = snapPresent },
  }
  def inv = x <= 3
}
