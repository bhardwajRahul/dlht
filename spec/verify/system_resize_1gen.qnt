module system_resize_1gen {
  // Default resize tier (design §8): one resize, 3 bins. hashRaw collides
  // both keys in gen0's bin 1 and splits them across gen1's bins 2/3.
  // Named import (the refinement-config pattern): a star import would clash
  // on init/step, which system re-exports from protocol.
  import system(
    procSet = Set("p1", "p2"),
    keyDomain = Set("k1", "k2"),
    valDomain = Set("v1", "v2"),
    maxGen = 1,
    slotsPerBin = 2,
    hashRaw = Map("k1" -> 0, "k2" -> 1),
  ) as sys from "../system"

  action init = sys::systemInit
  action step = sys::systemStep
  def invariant_inv = sys::inv
  def invariant_rsInv = sys::rsInv

  // Per-family localization wrappers (the f_* pattern for the rsInv tier).
  def invariant_r6 = sys::rsSnapshotRelationPure(sys::currentSpecState, sys::snapshot)
  def invariant_r7 = sys::rsSentinelDisciplinePure(sys::currentSpecState, sys::snapshot)
  def invariant_r9 = sys::rsChildUnobservablePure(sys::currentSpecState)
  def invariant_r10 = sys::rsCursorCoherencePure(sys::currentSpecState, sys::snapshot, sys::cursor)
  def invariant_r11 = sys::rsCompletenessPure(sys::currentSpecState, sys::snapshot, sys::cursor)
  def invariant_r12b = sys::rsChildFreeSlotPure(sys::currentSpecState, sys::snapshot, sys::cursor)
  def invariant_r12 = sys::rsClaimContinuityPure(sys::currentSpecState)
}
