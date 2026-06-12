module refinement_anchored_2proc {
  // 2-proc depth-independent refinement, anchored at an arbitrary inv-state.
  import refinement(
    procSet = Set("p1", "p2"),
    keyDomain = Set("k1"),
    valDomain = Set("v1", "v2"),
    maxGen = 0,
    slotsPerBin = 3,
    hashRaw = Map("k1" -> 0),
    refineBound = 2,
  ) as refine from "../refinement"

  action init = refine::refineIndInit
  action step = refine::refineNext
  def inv = refine::refinementStepOK
}
