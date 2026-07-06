module induction_resize_2gen_2proc {
  // Gated chain-walk config (DLHT_VERIFY_2GEN): 2 procs + the full daemon,
  // maxGen=2 (7 bins). Exercises double-resize, the gen0->gen2 laggard
  // chain-walk, and holder double-relocation in the inductive tier.
  import system_induction(
    procSet = Set("p1", "p2"),
    keyDomain = Set("k1", "k2"),
    valDomain = Set("v1", "v2"),
    maxGen = 2,
    slotsPerBin = 2,
    hashRaw = Map("k1" -> 0, "k2" -> 2),
  ) as sysi from "../system_induction"

  action init = sysi::systemIndInit
  action step = sysi::systemInductionStep
  def inv = sysi::systemInv
  def smoke = sysi::systemSmoke

  // COMPLETE g_* surface (Codex Critical 1 / Opus M1): the per-family 2-proc
  // decomposition is a sound discharge of inv ∧ rsInv ONLY if every conjunct
  // is checkable. All 47 localizers are surfaced so the fallback (Task 7/8)
  // covers the full conjunction, not a subset.
  def g_inv = sysi::g_inv
  def g_rsInv = sysi::g_rsInv
  def g_typeOK = sysi::g_typeOK
  def g_visibleSlotsWellFormed = sysi::g_visibleSlotsWellFormed
  def g_hashConsistency = sysi::g_hashConsistency
  def g_tryingOwnedUnique = sysi::g_tryingOwnedUnique
  def g_shadowOwnedUnique = sysi::g_shadowOwnedUnique
  def g_shadowSlotKeyed = sysi::g_shadowSlotKeyed
  def g_tagMonotonic = sysi::g_tagMonotonic
  def g_tagValPaired = sysi::g_tagValPaired
  def g_invalidSlotClean = sysi::g_invalidSlotClean
  def g_liveKeyUniquePerBin = sysi::g_liveKeyUniquePerBin
  def g_deleteWindowOwned = sysi::g_deleteWindowOwned
  def g_targetSlotInRange = sysi::g_targetSlotInRange
  def g_ownerSlotStateConsistent = sysi::g_ownerSlotStateConsistent
  def g_ownerSlotFilled = sysi::g_ownerSlotFilled
  def g_retAtD8 = sysi::g_retAtD8
  def g_retAtLC9 = sysi::g_retAtLC9
  def g_pendingRetOnlyInRetWindow = sysi::g_pendingRetOnlyInRetWindow
  def g_d8WindowOwnerUnique = sysi::g_d8WindowOwnerUnique
  def g_reservedKeyFresh = sysi::g_reservedKeyFresh
  def g_reservedKeyFreshAtReserve = sysi::g_reservedKeyFreshAtReserve
  def g_reserveBumpedVersion = sysi::g_reserveBumpedVersion
  def g_reserveHeaderAgrees = sysi::g_reserveHeaderAgrees
  def g_loopSlotValidAtCommit = sysi::g_loopSlotValidAtCommit
  def g_commitTagImpliesValid = sysi::g_commitTagImpliesValid
  def g_versionMonotonic = sysi::g_versionMonotonic
  def g_snapStateAgrees = sysi::g_snapStateAgrees
  def g_freshReservationEmpty = sysi::g_freshReservationEmpty
  def g_absentReturnConsistent = sysi::g_absentReturnConsistent
  def g_genTopology = sysi::g_genTopology
  def g_pristineFutureGens = sysi::g_pristineFutureGens
  def g_predecessorsDone = sysi::g_predecessorsDone
  def g_opGenSanity = sysi::g_opGenSanity
  def g_entryKeyAgreement = sysi::g_entryKeyAgreement
  def g_rsSnapshotRelation = sysi::g_rsSnapshotRelation
  def g_rsSentinelDiscipline = sysi::g_rsSentinelDiscipline
  def g_rsChildUnobservable = sysi::g_rsChildUnobservable
  def g_rsCursorCoherence = sysi::g_rsCursorCoherence
  def g_rsCompleteness = sysi::g_rsCompleteness
  def g_rsChildFreeSlot = sysi::g_rsChildFreeSlot
  def g_rsClaimContinuity = sysi::g_rsClaimContinuity
  def g_h0LoadedNoTransfer = sysi::g_h0LoadedNoTransfer
  def g_rsChildKeyFresh = sysi::g_rsChildKeyFresh
  def g_hLoopLoadedNoTransfer = sysi::g_hLoopLoadedNoTransfer
  def g_shadowGhostForm = sysi::g_shadowGhostForm
  def g_lc10AtDone = sysi::g_lc10AtDone
  def g_tryingOwnerUnique = sysi::g_tryingOwnerUnique
  def g_carriedClaimExists = sysi::g_carriedClaimExists
}
