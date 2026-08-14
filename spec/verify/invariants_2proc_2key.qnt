module invariants_2proc_2key {
  import invariants(
    procSet = Set("p1", "p2"),
    keyDomain = Set("k1", "k2"),
    valDomain = Set("v1", "v2"),
    maxGen = 0,
    slotsPerBin = 3,
    hashRaw = Map("k1" -> 0, "k2" -> 1),
  ).* from "../invariants"

  action init = invariantsInit
  action step = invariantsStep
  def typeOK = invariantsTypeOK
}
