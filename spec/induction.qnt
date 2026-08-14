module induction {
  import types.* from "./types"
  import protocol.* from "./protocol"
  import invariants.* from "./invariants"

  // ===================== Per-variable space table =========================
  // The anchor's COMPLETENESS argument: each constructed space must cover
  // every value the variable can take in ANY state satisfying inv. Review
  // this table against the var declarations in protocol.qnt on every change
  // to either. Under-coverage = silent false pass (see spec/probes/undercover.qnt).
  //
  //  var      | constructed space                          | completeness
  //  ---------+--------------------------------------------+-------------------------------
  //  header   | version: Int per bin; binState: all 3      | Int is maximal; typeOK cuts
  //           | states per bin; slotState: all 4 states    | version >= 0; genTopology +
  //           | per (bin,slot)                             | pristineFutureGens cut binState
  //  slotKey  | Option[HashKey]: HKey over full keyDomain  | full typed space (sentinel
  //           | + HSentinel + None                         | included)
  //  slotVal  | Option[Entry]: full keyDomain x valDomain  | full typed space
  //           | product + None                             |
  //  slotTag  | (bool x Int) per (bin,slot) assembled to   | Int maximal; tagMonotonic cuts
  //           | Option[int]; Int side via a flattened      | t >= 1 and t < nextTag
  //           | tuples(binDomain, slotIdx) -> Int map      |
  //  nextTag  | Int                                        | typeOK cuts >= 1
  //  pc       | all 34 PC variants (allPCs)                | full typed space — keep in
  //           |                                            | sync with the PC type!
  //           |                                            | (PcLC10 = holder relocation)
  //  op       | all OpName options + None (independent     | full typed space (typeOK pins
  //           | nondet, NOT derived from pc)               | op = opFromPC(pc); deriving
  //           |                                            | would couple to that conjunct)
  //  arg      | all Arg variants + None                    | full typed space
  //  ret      | all {ok, resVal} records + None            | full typed space
  //  local    | h0/hLoop: Int version + all 3 binStates +  | Int maximal; typeOK cuts
  //           | all slotStates; targetSlot: Int; gen: Int; | targetSlot via slotIdxExt,
  //           | expectedVal: Option[VAL];                  | versions >= 0, gen via
  //           | expectedTag: (bool x Int) -> Option[int]   | genDomain
  //  activeGen / maxAllocatedGen | Int x Int               | typeOK cuts 0 <= aG <= mAG <=
  //           |                                            | min(aG+1, maxGen)
  // ========================================================================

  pure val allPCs: Set[PC] = Set(
    PcIdle,
    PcG1, PcG2,
    PcI1, PcI2, PcI3, PcI4, PcI5, PcI6,
    PcP1, PcP2, PcP3, PcP4, PcP5, PcP6, PcP7,
    PcD1, PcD2, PcD3, PcD4, PcD5, PcD6, PcD7, PcD8,
    PcLC1, PcLC2, PcLC3, PcLC4, PcLC5, PcLC6, PcLC7, PcLC8, PcLC9, PcLC10
  )
  pure val allSlotStates: Set[SlotState] = Set(Invalid, Trying, Valid, Shadow)
  pure val allBinStates: Set[BinState] = Set(NoTransfer, InTransfer, DoneTransfer)
  pure val optHashKeys: Set[Option[HashKey]] =
    keyDomain.map(k => Some(HKey(k))).union(Set(Some(HSentinel), None))
  pure val allEntries: Set[Entry] =
    keyDomain.map(k => valDomain.map(v => { k: k, v: v })).flatten()
  pure val optEntries: Set[Option[Entry]] = allEntries.map(e => Some(e)).union(Set(None))
  pure val optVals: Set[Option[VAL]] = valDomain.map(v => Some(v)).union(Set(None))
  pure val allOps: Set[Op] = opNames.map(o => Some(o)).union(Set(None))
  pure val allArgs: Set[Arg] = keyArgs.union(keyValArgs).union(keyValSaveArgs)
  pure val optArgs: Set[Option[Arg]] = allArgs.map(a => Some(a)).union(Set(None))
  pure val allRes: Set[Res] =
    Set(true, false).map(ok => optVals.map(rv => { ok: ok, resVal: rv })).flatten()
  pure val optRes: Set[Option[Res]] = allRes.map(r => Some(r)).union(Set(None))

  action indInit = {
    nondet hVer = binDomain.setOfMaps(Int).oneOf()
    nondet hBS = binDomain.setOfMaps(allBinStates).oneOf()
    nondet hSS = binDomain.setOfMaps(slotIdx.setOfMaps(allSlotStates)).oneOf()
    nondet sKey = binDomain.setOfMaps(slotIdx.setOfMaps(optHashKeys)).oneOf()
    nondet sVal = binDomain.setOfMaps(slotIdx.setOfMaps(optEntries)).oneOf()
    nondet sTagSet = binDomain.setOfMaps(slotIdx.setOfMaps(Set(true, false))).oneOf()
    // Apalache 0.56 does not support setOfMaps(Int) nested inside setOfMaps
    // (FinFunSet[FinFunSet[InfSet]] is unimplemented). Flatten the domain
    // instead: a SINGLE-level setOfMaps from (bin, slot) pairs to Int is the
    // probe-validated shape and keeps every (bin, slot) tag value independent
    // — sharing one slot->Int map across bins would under-cover anchor states
    // the moment totalBins > 1.
    nondet sTagValFlat = tuples(binDomain, slotIdx).setOfMaps(Int).oneOf()
    nondet nt = Int.oneOf()
    nondet pcC = procSet.setOfMaps(allPCs).oneOf()
    nondet opC = procSet.setOfMaps(allOps).oneOf()
    nondet argC = procSet.setOfMaps(optArgs).oneOf()
    nondet retC = procSet.setOfMaps(optRes).oneOf()
    nondet lH0Ver = procSet.setOfMaps(Int).oneOf()
    nondet lH0BS = procSet.setOfMaps(allBinStates).oneOf()
    nondet lH0SS = procSet.setOfMaps(slotIdx.setOfMaps(allSlotStates)).oneOf()
    nondet lHlVer = procSet.setOfMaps(Int).oneOf()
    nondet lHlBS = procSet.setOfMaps(allBinStates).oneOf()
    nondet lHlSS = procSet.setOfMaps(slotIdx.setOfMaps(allSlotStates)).oneOf()
    nondet lTs = procSet.setOfMaps(Int).oneOf()
    nondet lGen = procSet.setOfMaps(Int).oneOf()
    nondet lEv = procSet.setOfMaps(optVals).oneOf()
    nondet lEtSet = procSet.setOfMaps(Set(true, false)).oneOf()
    nondet lEtVal = procSet.setOfMaps(Int).oneOf()
    nondet aG = Int.oneOf()
    nondet mAG = Int.oneOf()
    val cand: SpecState = {
      header: binDomain.mapBy(b =>
        { version: hVer.get(b), binState: hBS.get(b), slotState: hSS.get(b) }),
      slotKey: sKey,
      slotVal: sVal,
      slotTag: binDomain.mapBy(b => slotIdx.mapBy(s =>
        if (sTagSet.get(b).get(s)) Some(sTagValFlat.get((b, s))) else None)),
      nextTag: nt,
      pc: pcC,
      op: opC,
      arg: argC,
      ret: retC,
      local: procSet.mapBy(p => {
        h0: { version: lH0Ver.get(p), binState: lH0BS.get(p), slotState: lH0SS.get(p) },
        targetSlot: lTs.get(p),
        hLoop: { version: lHlVer.get(p), binState: lHlBS.get(p), slotState: lHlSS.get(p) },
        expectedVal: lEv.get(p),
        expectedTag: if (lEtSet.get(p)) Some(lEtVal.get(p)) else None,
        gen: lGen.get(p),
      }),
      activeGen: aG,
      maxAllocatedGen: mAG,
    }
    all {
      invPure(cand),
      header' = cand.header,
      slotKey' = cand.slotKey,
      slotVal' = cand.slotVal,
      slotTag' = cand.slotTag,
      nextTag' = cand.nextTag,
      pc' = cand.pc,
      op' = cand.op,
      arg' = cand.arg,
      ret' = cand.ret,
      local' = cand.local,
      activeGen' = cand.activeGen,
      maxAllocatedGen' = cand.maxAllocatedGen,
    }
  }

  // Re-exports for verify modules (star-imports are not transitive).
  action inductionStep = step
  def inductionInv = inv
  def anchorSat = true   // smoke target: empty anchor => deadlock => exit 1

  // Per-family re-exports so consecution counterexamples can be localized with
  // `--invariant=<familyName>` against the full-inv anchor (only the GOAL
  // narrows; indInit still guards with invPure). Star-imports are not
  // transitive, so each invariants-module wrapper must be surfaced explicitly.
  def f_visibleSlotsWellFormed = visibleSlotsWellFormed
  def f_hashConsistency = hashConsistency
  def f_tryingOwnedUnique = tryingOwnedUnique
  def f_shadowOwnedUnique = shadowOwnedUnique
  def f_shadowSlotKeyed = shadowSlotKeyed
  def f_tagMonotonic = tagMonotonic
  def f_tagValPaired = tagValPaired
  def f_invalidSlotClean = invalidSlotClean
  def f_liveKeyUniquePerBin = liveKeyUniquePerBin
  def f_deleteWindowOwned = deleteWindowOwned
  def f_targetSlotInRange = targetSlotInRange
  def f_ownerSlotStateConsistent = ownerSlotStateConsistent
  def f_ownerSlotFilled = ownerSlotFilled
  def f_retAtD8 = retAtD8
  def f_retAtLC9 = retAtLC9
  def f_pendingRetOnlyInRetWindow = pendingRetOnlyInRetWindow
  def f_d8WindowOwnerUnique = d8WindowOwnerUnique
  def f_reservedKeyFresh = reservedKeyFresh
  def f_reservedKeyFreshAtReserve = reservedKeyFreshAtReserve
  def f_reserveBumpedVersion = reserveBumpedVersion
  def f_reserveHeaderAgrees = reserveHeaderAgrees
  def f_loopSlotValidAtCommit = loopSlotValidAtCommit
  def f_commitTagImpliesValid = commitTagImpliesValid
  def f_versionMonotonic = versionMonotonic
  def f_snapStateAgrees = snapStateAgrees
  def f_freshReservationEmpty = freshReservationEmpty
  def f_absentReturnConsistent = absentReturnConsistent
  def f_genTopology = genTopology
  def f_pristineFutureGens = pristineFutureGens
  def f_predecessorsDone = predecessorsDone
  def f_opGenSanity = opGenSanity
  def f_entryKeyAgreement = entryKeyAgreement

  // Contract corollaries (NOT invPure conjuncts): checked as inv ⟹ corollary
  // with `--invariant=f_contract* --max-steps=0` — indInit guards with the
  // UNCHANGED invPure, so a 0-step run evaluates the corollary over all
  // inv-states. Wired in verify.sh stage 4 (2-proc tier).
  def f_contractAtMostOneComputePerKey = contractAtMostOneComputePerKey
  def f_contractHolderExclusive = contractHolderExclusive
}
