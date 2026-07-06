module system_induction {
  import types.* from "./types"
  import system.* from "./system"
  // induction.qnt's anchor space-set pure vals are the SINGLE SOURCE of
  // anchor-space truth (the undercover discipline). Reused here so the
  // protocol-var construction cannot drift from induction.qnt's. induction
  // has no `export`, so this brings only its own defs (space-set vals,
  // indInit/f_* — unused here) and cannot clash with system's exports; the
  // protocol/invariants instances are shared via Quint's import dedup (the
  // same pattern refinement.qnt relies on).
  import induction.* from "./induction"

  // ===================== Per-variable space table =========================
  // EXTENDS induction.qnt's table with the daemon vars. Under-coverage =
  // silent false pass (probes/undercover_daemon.qnt is the control).
  //
  //  var       | constructed space                          | completeness
  //  ----------+--------------------------------------------+---------------------------
  //  (protocol vars: see induction.qnt's table — same picks, reused verbatim)
  //  snapshot  | per bin: present-bit (bool) x Header        | full typed space; rsInv
  //            | {version Int, binState all 3, slotState     | (rsSnapshotRelation,
  //            | all 4 per slot}; None when bit false        | rsCursorCoherence) cuts
  //  cursor    | Int per bin                                 | rsCursorCoherence cuts
  //            |                                             | 0 <= cur <= slotsPerBin
  // ========================================================================

  action systemIndInit = {
    // --- protocol-var picks (mirror induction.qnt::indInit EXACTLY) ---
    nondet hVer = binDomain.setOfMaps(Int).oneOf()
    nondet hBS = binDomain.setOfMaps(allBinStates).oneOf()
    nondet hSS = binDomain.setOfMaps(slotIdx.setOfMaps(allSlotStates)).oneOf()
    nondet sKey = binDomain.setOfMaps(slotIdx.setOfMaps(optHashKeys)).oneOf()
    nondet sVal = binDomain.setOfMaps(slotIdx.setOfMaps(optEntries)).oneOf()
    nondet sTagSet = binDomain.setOfMaps(slotIdx.setOfMaps(Set(true, false))).oneOf()
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
    // --- daemon-var picks (NEW for 1b) ---
    nondet snapPresent = binDomain.setOfMaps(Set(true, false)).oneOf()
    nondet snapVer = binDomain.setOfMaps(Int).oneOf()
    nondet snapBS = binDomain.setOfMaps(allBinStates).oneOf()
    nondet snapSS = binDomain.setOfMaps(slotIdx.setOfMaps(allSlotStates)).oneOf()
    nondet curC = binDomain.setOfMaps(Int).oneOf()
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
    val snapCand: BinIdx -> Option[Header] = binDomain.mapBy(b =>
      if (snapPresent.get(b))
        Some({ version: snapVer.get(b), binState: snapBS.get(b), slotState: snapSS.get(b) })
      else None)
    val curCand: BinIdx -> SlotIdx = curC
    all {
      invPure(cand),
      rsInvPure(cand, snapCand, curCand),
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
      snapshot' = snapCand,
      cursor' = curCand,
    }
  }

  action systemInductionStep = systemStep
  def systemInv = inv and rsInv
  def systemSmoke = true   // smoke target: empty anchor => deadlock => exit 1

  // ===================== Per-family localization harness ==================
  // g_<family> goals: consecution counterexamples localize via
  // `--invariant=g_<family>`, and each is a smaller SMT goal under the FULL
  // anchor guard (enabling per-family 2-proc decomposition; design D4).
  // --- whole-goal localizers ---
  def g_inv = inv
  def g_rsInv = rsInv
  // --- inv-family localizers (re-export invariants.qnt's live wrappers) ---
  // typeOK is a conjunct of invPure; surfaced standalone so the per-family
  // 2-proc decomposition (design D4) is a COMPLETE discharge of `inv`.
  def g_typeOK = typeOK
  def g_visibleSlotsWellFormed = visibleSlotsWellFormed
  def g_hashConsistency = hashConsistency
  def g_tryingOwnedUnique = tryingOwnedUnique
  def g_shadowOwnedUnique = shadowOwnedUnique
  def g_shadowSlotKeyed = shadowSlotKeyed
  def g_tagMonotonic = tagMonotonic
  def g_tagValPaired = tagValPaired
  def g_invalidSlotClean = invalidSlotClean
  def g_liveKeyUniquePerBin = liveKeyUniquePerBin
  def g_deleteWindowOwned = deleteWindowOwned
  def g_targetSlotInRange = targetSlotInRange
  def g_ownerSlotStateConsistent = ownerSlotStateConsistent
  def g_ownerSlotFilled = ownerSlotFilled
  def g_retAtD8 = retAtD8
  def g_retAtLC9 = retAtLC9
  def g_pendingRetOnlyInRetWindow = pendingRetOnlyInRetWindow
  def g_d8WindowOwnerUnique = d8WindowOwnerUnique
  def g_reservedKeyFresh = reservedKeyFresh
  def g_reservedKeyFreshAtReserve = reservedKeyFreshAtReserve
  def g_reserveBumpedVersion = reserveBumpedVersion
  def g_reserveHeaderAgrees = reserveHeaderAgrees
  def g_loopSlotValidAtCommit = loopSlotValidAtCommit
  def g_commitTagImpliesValid = commitTagImpliesValid
  def g_versionMonotonic = versionMonotonic
  def g_snapStateAgrees = snapStateAgrees
  def g_freshReservationEmpty = freshReservationEmpty
  def g_absentReturnConsistent = absentReturnConsistent
  def g_genTopology = genTopology
  def g_pristineFutureGens = pristineFutureGens
  def g_predecessorsDone = predecessorsDone
  def g_opGenSanity = opGenSanity
  def g_entryKeyAgreement = entryKeyAgreement
  // --- rsInv-family localizers (parameterized pure defs on the live state) ---
  def g_rsSnapshotRelation = rsSnapshotRelationPure(currentSpecState, snapshot)
  def g_rsSentinelDiscipline = rsSentinelDisciplinePure(currentSpecState, snapshot)
  def g_rsChildUnobservable = rsChildUnobservablePure(currentSpecState)
  def g_rsCursorCoherence = rsCursorCoherencePure(currentSpecState, snapshot, cursor)
  def g_rsCompleteness = rsCompletenessPure(currentSpecState, snapshot, cursor)
  def g_rsChildFreeSlot = rsChildFreeSlotPure(currentSpecState, snapshot, cursor)
  def g_rsClaimContinuity = rsClaimContinuityPure(currentSpecState)
  def g_h0LoadedNoTransfer = h0LoadedNoTransferPure(currentSpecState)
  def g_rsChildKeyFresh = rsChildKeyFreshPure(currentSpecState, snapshot, cursor)
  def g_hLoopLoadedNoTransfer = hLoopLoadedNoTransferPure(currentSpecState)
  def g_shadowGhostForm = shadowGhostFormPure(currentSpecState)
  def g_lc10AtDone = lc10AtDonePure(currentSpecState)
  def g_tryingOwnerUnique = tryingOwnerUniquePure(currentSpecState)
  def g_carriedClaimExists = carriedClaimExistsPure(currentSpecState)
}
