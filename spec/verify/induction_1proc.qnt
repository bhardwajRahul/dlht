module induction_1proc {
  import induction(
    procSet = Set("p1"),
    keyDomain = Set("k1"),
    valDomain = Set("v1", "v2"),
    maxGen = 0,
    slotsPerBin = 3,
    hashRaw = Map("k1" -> 0),
  ).* from "../induction"

  action init = indInit
  action step = inductionStep
  def inv = inductionInv
  def smoke = anchorSat
}
