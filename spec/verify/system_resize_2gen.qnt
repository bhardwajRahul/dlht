module system_resize_2gen {
  // Chain-walk tier (design §8, gated DLHT_VERIFY_2GEN): two resizes, 7
  // bins. hashRaw collides the keys at gen0 (bin 1) AND gen1 (bin 2), and
  // splits them at gen2 (bins 4 and 6) — exercising double-resize,
  // re-collision, and the gen0->gen2 laggard double-walk.
  // Named import (the refinement-config pattern): a star import would clash
  // on init/step, which system re-exports from protocol.
  import system(
    procSet = Set("p1", "p2"),
    keyDomain = Set("k1", "k2"),
    valDomain = Set("v1", "v2"),
    maxGen = 2,
    slotsPerBin = 2,
    hashRaw = Map("k1" -> 0, "k2" -> 2),
  ) as sys from "../system"

  action init = sys::systemInit
  action step = sys::systemStep
  def invariant_inv = sys::inv
  def invariant_rsInv = sys::rsInv

  // Protocol-family localization (sys::f_* equivalents live in induction's
  // instance, not here; surface the suspects directly).
  def invariant_shadowOwnedUnique = sys::shadowOwnedUnique
  def invariant_predecessorsDone = sys::predecessorsDone
  def invariant_genTopology = sys::genTopology

  // Per-family localization wrappers (the f_* pattern for the rsInv tier).
  def invariant_r6 = sys::rsSnapshotRelationPure(sys::currentSpecState, sys::snapshot)
  def invariant_r7 = sys::rsSentinelDisciplinePure(sys::currentSpecState, sys::snapshot)
  def invariant_r9 = sys::rsChildUnobservablePure(sys::currentSpecState)
  def invariant_r10 = sys::rsCursorCoherencePure(sys::currentSpecState, sys::snapshot, sys::cursor)
  def invariant_r11 = sys::rsCompletenessPure(sys::currentSpecState, sys::snapshot, sys::cursor)
  def invariant_r12b = sys::rsChildFreeSlotPure(sys::currentSpecState, sys::snapshot, sys::cursor)
  def invariant_r12 = sys::rsClaimContinuityPure(sys::currentSpecState)
}
