module invariants_2proc {
  import invariants(
    procSet = Set("p1", "p2"),
    keyDomain = Set("k1"),
    valDomain = Set("v1", "v2"),
    maxGen = 0,
    slotsPerBin = 3,
    hashRaw = Map("k1" -> 0),
  ).* from "../invariants"

  action init = invariantsInit
  action step = invariantsStep
  def typeOK = invariantsTypeOK
}
