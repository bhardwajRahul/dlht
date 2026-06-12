module protocol {
  import types.* from "./types"

  const maxGen: int            // generations 0..maxGen may exist (D3: configs use 0, 1, or 2)
  const slotsPerBin: int
  const hashRaw: KEY -> int    // abstract raw hash, >= 0

  type BinIdx = int
  type SlotIdx = int
  type GenIdx = int

  pure val genDomain: Set[GenIdx] = 0.to(maxGen)
  // gen g owns bins genBase(g) .. genBase(g)+sizeAt(g)-1; growth factor 2
  // (Go's 8x/4x tiering is a constant-factor concern, design §3).
  // pow2 is a CLOSED FORM, not a range-fold: Apalache requires constant
  // integer bounds in `a.to(b)` and does not constant-fold ApaFoldSet, so a
  // fold-defined totalBins breaks every `quint verify` stage ("Expected a
  // constant integer range"). The explicit chain is exact for the arguments
  // that occur under maxGenCap (g <= maxGen + 1 <= 3) and Apalache's
  // ConstSimplifier reduces it to a literal at preprocessing time.
  pure def pow2(g: int): int =
    if (g <= 0) 1 else if (g == 1) 2 else if (g == 2) 4 else 8
  pure def sizeAt(g: GenIdx): int = pow2(g)
  pure def genBase(g: GenIdx): int = pow2(g)            // gen0->1, gen1->2, gen2->4
  pure val totalBins: int = pow2(maxGen + 1) - 1
  pure val binDomain: Set[BinIdx] = 1.to(totalBins)
  pure val slotIdx: Set[SlotIdx] = 1.to(slotsPerBin)
  pure val slotIdxExt: Set[SlotIdx] = Set(0).union(slotIdx)
  // MAX-fold, not last-qualifier-wins: Quint set folds visit in UNSPECIFIED
  // order, so `if (b >= genBase(g)) g else acc` would be nondeterministic
  // (review finding). Taking the max of qualifying gens is order-independent.
  pure def genOfBin(b: BinIdx): GenIdx =
    genDomain.fold(0, (acc, g) => if (genBase(g) <= b and g > acc) g else acc)
  pure def binFor(k: KEY, g: GenIdx): BinIdx = genBase(g) + hashRaw.get(k) % sizeAt(g)
  pure def childrenOf(b: BinIdx): Set[BinIdx] = {
    val g = genOfBin(b)
    val off = b - genBase(g)
    Set(genBase(g + 1) + off, genBase(g + 1) + off + sizeAt(g))
  }

  type SlotState = | Invalid | Trying | Valid | Shadow
  type PC =
    | PcIdle
    | PcG1 | PcG2
    | PcI1 | PcI2 | PcI3 | PcI4 | PcI5 | PcI6
    | PcP1 | PcP2 | PcP3 | PcP4 | PcP5 | PcP6 | PcP7
    | PcD1 | PcD2 | PcD3 | PcD4 | PcD5 | PcD6 | PcD7 | PcD8
    | PcLC1 | PcLC2 | PcLC3 | PcLC4 | PcLC5 | PcLC6 | PcLC7 | PcLC8 | PcLC9 | PcLC10

  type BinState = | NoTransfer | InTransfer | DoneTransfer
  type Header = {
    version: int,
    binState: BinState,
    slotState: SlotIdx -> SlotState,
  }
  type LocalState = {
    h0: Header,
    targetSlot: SlotIdx,
    hLoop: Header,
    expectedVal: Option[VAL],
    expectedTag: Option[int],
    gen: GenIdx,
  }

  var pc: PROC -> PC
  var op: PROC -> Op
  var arg: PROC -> Option[Arg]
  var ret: PROC -> Option[Res]

  var header: BinIdx -> Header
  var slotKey: BinIdx -> (SlotIdx -> Option[HashKey])
  var slotVal: BinIdx -> (SlotIdx -> Option[Entry])
  var slotTag: BinIdx -> (SlotIdx -> Option[int])
  var nextTag: int

  var local: PROC -> LocalState

  // Generation counters (design §3): activeGen models Go's m.active;
  // maxAllocatedGen how far the indexNext chain extends. Resize-active iff
  // maxAllocatedGen == activeGen + 1 — no separate phase var.
  var activeGen: int
  var maxAllocatedGen: int

  // Snapshot of the full shared+control state. Pure invariant families take
  // this instead of reading vars, so the induction anchor (induction.qnt) can
  // evaluate them on *constructed* candidate states before assignment.
  type SpecState = {
    header: BinIdx -> Header,
    slotKey: BinIdx -> (SlotIdx -> Option[HashKey]),
    slotVal: BinIdx -> (SlotIdx -> Option[Entry]),
    slotTag: BinIdx -> (SlotIdx -> Option[int]),
    nextTag: int,
    pc: PROC -> PC,
    op: PROC -> Op,
    arg: PROC -> Option[Arg],
    ret: PROC -> Option[Res],
    local: PROC -> LocalState,
    activeGen: int,
    maxAllocatedGen: int,
  }

  def currentSpecState: SpecState = {
    header: header, slotKey: slotKey, slotVal: slotVal, slotTag: slotTag,
    nextTag: nextTag, pc: pc, op: op, arg: arg, ret: ret, local: local,
    activeGen: activeGen, maxAllocatedGen: maxAllocatedGen,
  }

  assume maxGenDef = maxGen >= 0
  // Design D3 caps configs at 2 resizes / 3 generations; pow2's closed form
  // and the refinement authority walk both rest on this cap.
  assume maxGenCap = maxGen <= 2
  assume slotsPerBinDef = slotsPerBin > 0
  assume hashRawDef = keyDomain.forall(k => hashRaw.get(k) >= 0)
  assume finiteDomains =
    procSet.isFinite() and
    keyDomain.isFinite() and
    valDomain.isFinite() and
    procSet.size() > 0 and
    keyDomain.size() > 0 and
    valDomain.size() > 0

  pure val anyKey: KEY = pickAny(keyDomain)
  pure val anyVal: VAL = pickAny(valDomain)

  pure val emptyHeader: Header = {
    version: 0,
    binState: NoTransfer,
    slotState: slotIdx.mapBy(_ => Invalid),
  }
  pure val emptyLocal: LocalState = {
    h0: emptyHeader,
    targetSlot: 0,
    hLoop: emptyHeader,
    expectedVal: None,
    expectedTag: None,
    gen: 0,
  }

  pure def keyOfArg(a: Arg): KEY = {
    match a {
      | KeyArg(k) => k
      | KeyValArg(kv) => kv._1
      | LoadComputeArg(triple) => triple._1
    }
  }

  pure def valOfArg(a: Arg): VAL = {
    match a {
      | KeyValArg(kv) => kv._2
      | LoadComputeArg(triple) => triple._2
      | _ => anyVal
    }
  }

  pure def saveOfArg(a: Arg): bool = {
    match a {
      | LoadComputeArg(triple) => triple._3
      | _ => false
    }
  }

  def keyOfProc(p: PROC): KEY = {
    match arg.get(p) {
      | Some(a) => keyOfArg(a)
      | _ => anyKey
    }
  }

  def valOfProc(p: PROC): VAL = {
    match arg.get(p) {
      | Some(a) => valOfArg(a)
      | _ => anyVal
    }
  }

  def saveOfProc(p: PROC): bool = {
    match arg.get(p) {
      | Some(a) => saveOfArg(a)
      | _ => false
    }
  }

  // ABSTRACT visibility (refinement + transfer families): the entry's own
  // key is ground truth — a sentineled slot stays visible (design §6).
  pure def visibleSlotsByHeaderFrom(h: Header, valMap: BinIdx -> (SlotIdx -> Option[Entry]),
      tagMap: BinIdx -> (SlotIdx -> Option[int]), b: BinIdx, k: KEY): Set[SlotIdx] =
    slotIdx.filter(s =>
      h.slotState.get(s) == Valid and
        tagMap.get(b).get(s) != None and
        match valMap.get(b).get(s) { | Some(e) => e.k == k | None => false }
    )

  // OPERATIONAL candidate scan (P2/D2/I2/LC2/G2): matches the slotKey hash
  // word, as Go's bitmap does — a sentineled slot is never a candidate.
  // Generation membership selects the bin; the hash word selects the slot.
  pure def candidateSlotsByHeaderFrom(h: Header, keyMap: BinIdx -> (SlotIdx -> Option[HashKey]),
      valMap: BinIdx -> (SlotIdx -> Option[Entry]), tagMap: BinIdx -> (SlotIdx -> Option[int]),
      b: BinIdx, k: KEY): Set[SlotIdx] =
    slotIdx.filter(s =>
      h.slotState.get(s) == Valid and
        keyMap.get(b).get(s) == Some(HKey(k)) and
        valMap.get(b).get(s) != None and
        tagMap.get(b).get(s) != None
    )

  // Shadow slots only carry a key (value is a placeholder until LC7), so the
  // filter is key-only.
  pure def shadowSlotsByHeaderFrom(h: Header, keyMap: BinIdx -> (SlotIdx -> Option[HashKey]),
      b: BinIdx, k: KEY): Set[SlotIdx] =
    slotIdx.filter(s =>
      h.slotState.get(s) == Shadow and
        keyMap.get(b).get(s) == Some(HKey(k))
    )

  def shadowSlotsByHeader(h: Header, b: BinIdx, k: KEY): Set[SlotIdx] =
    shadowSlotsByHeaderFrom(h, slotKey, b, k)

  pure def readVisibleByHeaderFrom(h: Header, valMap: BinIdx -> (SlotIdx -> Option[Entry]),
      tagMap: BinIdx -> (SlotIdx -> Option[int]), b: BinIdx, k: KEY): Option[VAL] = {
    val visible = visibleSlotsByHeaderFrom(h, valMap, tagMap, b, k)
    if (visible.size() == 0) None
    else match valMap.get(b).get(minOr0(visible)) { | Some(e) => Some(e.v) | None => None }
  }

  def visibleSlotsByHeader(h: Header, b: BinIdx, k: KEY): Set[SlotIdx] =
    visibleSlotsByHeaderFrom(h, slotVal, slotTag, b, k)

  def candidateSlotsByHeader(h: Header, b: BinIdx, k: KEY): Set[SlotIdx] =
    candidateSlotsByHeaderFrom(h, slotKey, slotVal, slotTag, b, k)

  def readVisibleByHeader(h: Header, b: BinIdx, k: KEY): Option[VAL] =
    readVisibleByHeaderFrom(h, slotVal, slotTag, b, k)

  // The operational slot pick (P2/D2): the CANDIDATE form — Go's bitmap scan
  // compares the hash word, so a sentineled slot is never picked (design §6).
  def slotForKeyByHeader(h: Header, b: BinIdx, k: KEY): SlotIdx = {
    minOr0(candidateSlotsByHeader(h, b, k))
  }

  // Pure snapshot-walk helpers for the resize daemon's per-bin transfer
  // (design §4): the snapshot slots rsMove/rsShadowCarry must process, in
  // order. They live HERE (not resize.qnt) because the R-family invariants
  // (invariants.qnt) need nextSlot too, and invariants must NOT import
  // resize — that would pull the daemon's vars into induction.qnt's
  // instance, where indInit does not assign them.
  pure def transferable(snap: Header): Set[SlotIdx] =
    slotIdx.filter(s =>
      snap.slotState.get(s) == Valid or snap.slotState.get(s) == Shadow)

  pure def nextSlot(snap: Header, cur: SlotIdx): SlotIdx =
    minOr0(transferable(snap).filter(s => s > cur))

  pure def opFromPC(id: PC): Op = match id {
    | PcIdle => None
    | PcG1 => Some(Get)
    | PcG2 => Some(Get)
    | PcI1 => Some(Insert)
    | PcI2 => Some(Insert)
    | PcI3 => Some(Insert)
    | PcI4 => Some(Insert)
    | PcI5 => Some(Insert)
    | PcI6 => Some(Insert)
    | PcP1 => Some(Put)
    | PcP2 => Some(Put)
    | PcP3 => Some(Put)
    | PcP4 => Some(Put)
    | PcP5 => Some(Put)
    | PcP6 => Some(Put)
    | PcP7 => Some(Put)
    | PcD1 => Some(Delete)
    | PcD2 => Some(Delete)
    | PcD3 => Some(Delete)
    | PcD4 => Some(Delete)
    | PcD5 => Some(Delete)
    | PcD6 => Some(Delete)
    | PcD7 => Some(Delete)
    | PcD8 => Some(Delete)
    | PcLC1 => Some(LoadOrCompute)
    | PcLC2 => Some(LoadOrCompute)
    | PcLC3 => Some(LoadOrCompute)
    | PcLC4 => Some(LoadOrCompute)
    | PcLC5 => Some(LoadOrCompute)
    | PcLC6 => Some(LoadOrCompute)
    | PcLC7 => Some(LoadOrCompute)
    | PcLC8 => Some(LoadOrCompute)
    | PcLC9 => Some(LoadOrCompute)
    | PcLC10 => Some(LoadOrCompute)
  }

  pure def opStartLine(opname: OpName): PC = match opname {
    | Get => PcG1
    | Insert => PcI1
    | Put => PcP1
    | Delete => PcD1
    | LoadOrCompute => PcLC1
  }

  pure def updateSlotState(h: Header, s: SlotIdx, newState: SlotState): Header = {
    { version: h.version + 1, binState: h.binState, slotState: h.slotState.set(s, newState) }
  }

  pure def clearSlotState(h: Header, s: SlotIdx, newState: SlotState): Header = {
    { ...h, slotState: h.slotState.set(s, newState) }
  }

  pure def mkResult(ok: bool, v: Option[VAL]): Option[Res] = Some({ ok: ok, resVal: v })

  pure def withH0(ls: LocalState, h: Header): LocalState = {
    ...ls,
    h0: h,
  }

  pure def withTargetSlot(ls: LocalState, s: SlotIdx): LocalState = {
    ...ls,
    targetSlot: s,
  }

  pure def withHLoop(ls: LocalState, h: Header): LocalState = {
    ...ls,
    hLoop: h,
  }

  pure def withExpected(ls: LocalState, v: Option[VAL], t: Option[int]): LocalState = {
    ...ls,
    expectedVal: v,
    expectedTag: t,
  }

  pure def withGen(ls: LocalState, g: GenIdx): LocalState = {
    ...ls,
    gen: g,
  }

  action unchanged_control = all {
    op' = op,
    arg' = arg,
    ret' = ret,
  }

  action unchanged_shared = all {
    header' = header,
    slotKey' = slotKey,
    slotVal' = slotVal,
    slotTag' = slotTag,
    nextTag' = nextTag,
    activeGen' = activeGen,
    maxAllocatedGen' = maxAllocatedGen,
  }

  action unchanged_local = all {
    local' = local,
  }

  action init = all {
    pc' = procSet.mapBy(_ => PcIdle),
    op' = procSet.mapBy(_ => None),
    arg' = procSet.mapBy(_ => None),
    ret' = procSet.mapBy(_ => None),

    header' = binDomain.mapBy(_ => emptyHeader),
    slotKey' = binDomain.mapBy(_ => slotIdx.mapBy(_ => None)),
    slotVal' = binDomain.mapBy(_ => slotIdx.mapBy(_ => None)),
    slotTag' = binDomain.mapBy(_ => slotIdx.mapBy(_ => None)),
    nextTag' = 1,

    local' = procSet.mapBy(_ => emptyLocal),
    activeGen' = 0,
    maxAllocatedGen' = 0,
  }

  action invokeLine(p) = {
    nondet newOp = opNames.oneOf()
    nondet newArg = argsOf(Some(newOp)).oneOf()
    all {
      pc.get(p) == PcIdle,
      pc' = pc.set(p, opStartLine(newOp)),
      op' = op.set(p, Some(newOp)),
      arg' = arg.set(p, Some(newArg)),
      ret' = ret.set(p, None),
      unchanged_shared,
      // The op starts at the active generation, matching Go's
      // m.getActiveIndex() at op entry.
      local' = local.set(p, withGen(local.get(p), activeGen)),
    }
  }

  // -------------------------------- Get -----------------------------------

  // Fused classification load (design §5, NORMATIVE per-site table): no
  // non-NoTransfer h0 is ever retained. Done -> chain-walk exactly ONE
  // generation (get.go:26-38; never a jump); InTransfer -> back off and
  // reload m.active (insert.go:32 — may legitimately jump several gens).
  action G1(p) = {
    val k = keyOfProc(p)
    val g = local.get(p).gen
    val b = binFor(k, g)
    val h = header.get(b)
    all {
      pc.get(p) == PcG1,
      if (h.binState == NoTransfer) all {
        // proceed: retain h0 (provably NoTransfer), stay on this gen
        local' = local.set(p, withH0(local.get(p), h)),
        pc' = pc.set(p, PcG2),
      } else if (h.binState == DoneTransfer) all {
        // chain-walk: exactly one generation forward (design §5)
        local' = local.set(p, withGen(local.get(p), g + 1)),
        pc' = pc.set(p, PcG1),
      } else all {
        // InTransfer: back off, reload m.active (may jump several gens)
        local' = local.set(p, withGen(local.get(p), activeGen)),
        pc' = pc.set(p, PcG1),
      },
      unchanged_control,
      unchanged_shared,
    }
  }

  action G2(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    all {
      pc.get(p) == PcG2,
      if (g2ReturnGuard(p)) {
        // Entry-key read: Go's Get returns the entry's value after a
        // hash-match scan — on a NoTransfer bin candidate ≡ entry-key
        // (entryKeyAgreement corollary), so the simpler form is exact here.
        val result = readVisibleByHeader(local.get(p).h0, b, k)
        all {
          ret' = ret.set(p, mkResult(result != None, result)),
          op' = op.set(p, None),
          arg' = arg.set(p, None),
          pc' = pc.set(p, PcIdle),
        }
      } else {
        all {
          pc' = pc.set(p, PcG1),
          ret' = ret,
          op' = op,
          arg' = arg,
        }
      },
      unchanged_shared,
      unchanged_local,
    }
  }

  // ------------------------------ Insert ----------------------------------

  // Fused classification load — same three-branch shape as G1 (design §5).
  action I1(p) = {
    val k = keyOfProc(p)
    val g = local.get(p).gen
    val b = binFor(k, g)
    val h = header.get(b)
    all {
      pc.get(p) == PcI1,
      if (h.binState == NoTransfer) all {
        local' = local.set(p, withH0(local.get(p), h)),
        pc' = pc.set(p, PcI2),
      } else if (h.binState == DoneTransfer) all {
        local' = local.set(p, withGen(local.get(p), g + 1)),
        pc' = pc.set(p, PcI1),
      } else all {
        local' = local.set(p, withGen(local.get(p), activeGen)),
        pc' = pc.set(p, PcI1),
      },
      unchanged_control,
      unchanged_shared,
    }
  }

  action I2(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val h = local.get(p).h0
    all {
      pc.get(p) == PcI2,
      if (header.get(b) != h) {
        all {
          pc' = pc.set(p, PcI1),
          local' = local,
          ret' = ret,
          op' = op,
          arg' = arg,
        }
      } else if (i2ReturnGuard(p)) {
        all {
          ret' = ret.set(p, mkResult(false, readVisibleByHeader(h, b, k))),
          op' = op.set(p, None),
          arg' = arg.set(p, None),
          pc' = pc.set(p, PcIdle),
          local' = local,
        }
      } else if (shadowSlotsByHeader(h, b, k).size() != 0) {
        // Shadow holder owns this key; back off until it resolves.
        all {
          pc' = pc.set(p, PcI1),
          local' = local,
          ret' = ret,
          op' = op,
          arg' = arg,
        }
      } else {
        val free = slotIdx.filter(s => h.slotState.get(s) == Invalid)
        if (free.size() != 0) {
          all {
            local' = local.set(p, withTargetSlot(local.get(p), minOr0(free))),
            pc' = pc.set(p, PcI3),
            ret' = ret,
            op' = op,
            arg' = arg,
          }
        } else {
          all {
            pc' = pc.set(p, PcI1),
            local' = local,
            ret' = ret,
            op' = op,
            arg' = arg,
          }
        }
      },
      unchanged_shared,
    }
  }

  action I3(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    all {
      pc.get(p) == PcI3,
      if (s != 0 and header.get(b) == local.get(p).h0 and header.get(b).slotState.get(s) == Invalid) {
        all {
          header' = header.set(b, updateSlotState(header.get(b), s, Trying)),
          pc' = pc.set(p, PcI4),
        }
      } else {
        all {
          header' = header,
          pc' = pc.set(p, PcI1),
        }
      },
      unchanged_control,
      slotKey' = slotKey,
      slotVal' = slotVal,
      slotTag' = slotTag,
      nextTag' = nextTag,
      activeGen' = activeGen,
      maxAllocatedGen' = maxAllocatedGen,
      unchanged_local,
    }
  }

  action I4(p) = {
    val k = keyOfProc(p)
    val v = valOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    all {
      pc.get(p) == PcI4,
      slotKey' = slotKey.set(b, slotKey.get(b).set(s, Some(HKey(k)))),
      slotVal' = slotVal.set(b, slotVal.get(b).set(s, Some({ k: k, v: v }))),
      slotTag' = slotTag.set(b, slotTag.get(b).set(s, Some(nextTag))),
      nextTag' = nextTag + 1,
      pc' = pc.set(p, PcI5),
      unchanged_control,
      header' = header,
      local' = local,
      activeGen' = activeGen,
      maxAllocatedGen' = maxAllocatedGen,
    }
  }

  action I5(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    all {
      pc.get(p) == PcI5,
      if (i5SuccessGuard(p)) {
        all {
          header' = header.set(b, updateSlotState(header.get(b), s, Valid)),
          ret' = ret.set(p, mkResult(true, None)),
          op' = op.set(p, None),
          arg' = arg.set(p, None),
          pc' = pc.set(p, PcIdle),
        }
      } else {
        all {
          header' = header,
          ret' = ret,
          op' = op,
          arg' = arg,
          pc' = pc.set(p, PcI6),
        }
      },
      slotKey' = slotKey,
      slotVal' = slotVal,
      slotTag' = slotTag,
      nextTag' = nextTag,
      activeGen' = activeGen,
      maxAllocatedGen' = maxAllocatedGen,
      unchanged_local,
    }
  }

  action I6(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    all {
      pc.get(p) == PcI6,
      // Unreserve REFUSAL (design §5, insert.go:169): the CAS requires a
      // NoTransfer bin — on a transferring/dead bin the Trying slot is
      // ABANDONED (stale key/val/tag persist) and the owner redirects via
      // the fused I1 classification.
      if (s != 0 and header.get(b).slotState.get(s) == Trying and
          slotKey.get(b).get(s) == Some(HKey(k)) and
          header.get(b).binState == NoTransfer) {
        all {
          header' = header.set(b, updateSlotState(header.get(b), s, Invalid)),
          slotVal' = slotVal.set(b, slotVal.get(b).set(s, None)),
          slotTag' = slotTag.set(b, slotTag.get(b).set(s, None)),
        }
      } else {
        all {
          header' = header,
          slotVal' = slotVal,
          slotTag' = slotTag,
        }
      },
      pc' = pc.set(p, PcI1),
      unchanged_control,
      slotKey' = slotKey,
      nextTag' = nextTag,
      activeGen' = activeGen,
      maxAllocatedGen' = maxAllocatedGen,
      unchanged_local,
    }
  }

  // -------------------------------- Put -----------------------------------

  // Fused classification load — same three-branch shape as G1 (design §5).
  action P1(p) = {
    val k = keyOfProc(p)
    val g = local.get(p).gen
    val b = binFor(k, g)
    val h = header.get(b)
    all {
      pc.get(p) == PcP1,
      if (h.binState == NoTransfer) all {
        local' = local.set(p, withH0(local.get(p), h)),
        pc' = pc.set(p, PcP2),
      } else if (h.binState == DoneTransfer) all {
        local' = local.set(p, withGen(local.get(p), g + 1)),
        pc' = pc.set(p, PcP1),
      } else all {
        local' = local.set(p, withGen(local.get(p), activeGen)),
        pc' = pc.set(p, PcP1),
      },
      unchanged_control,
      unchanged_shared,
    }
  }

  action P2(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    all {
      pc.get(p) == PcP2,
      local' = local.set(p, withTargetSlot(local.get(p), slotForKeyByHeader(local.get(p).h0, b, k))),
      pc' = pc.set(p, PcP3),
      unchanged_control,
      unchanged_shared,
    }
  }

  action P3(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    all {
      pc.get(p) == PcP3,
      if (header.get(b) != local.get(p).h0) {
        all {
          pc' = pc.set(p, PcP1),
          ret' = ret,
          op' = op,
          arg' = arg,
        }
      } else if (keyAbsentGuard(p)) {
        all {
          ret' = ret.set(p, mkResult(false, None)),
          op' = op.set(p, None),
          arg' = arg.set(p, None),
          pc' = pc.set(p, PcIdle),
        }
      } else {
        all {
          pc' = pc.set(p, PcP4),
          ret' = ret,
          op' = op,
          arg' = arg,
        }
      },
      unchanged_shared,
      unchanged_local,
    }
  }

  // NO binState check here — design §5, put.go:80-119. The pre-sentinel Put
  // must remain able to linearize mid-transfer and be carried by rsMove;
  // classifying here would erase exactly the behavior the sentinel-cut
  // scenarios verify. Put is protected by the sentinel instead: P5/P7's
  // slotKey == Some(HKey(k)) fails against HSentinel -> retry -> classify.
  action P4(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    all {
      pc.get(p) == PcP4,
      local' = local.set(p, withHLoop(local.get(p), header.get(b))),
      pc' = pc.set(p, PcP5),
      unchanged_control,
      unchanged_shared,
    }
  }

  action P5(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    val retry =
      local.get(p).hLoop.slotState.get(s) != Valid or
        slotKey.get(b).get(s) != Some(HKey(k)) or
        slotVal.get(b).get(s) == None
    all {
      pc.get(p) == PcP5,
      if (retry) {
        all {
          pc' = pc.set(p, PcP1),
          local' = local,
        }
      } else {
        all {
          pc' = pc.set(p, PcP6),
          // expectedVal stays Option[VAL] (it feeds ret): project the entry.
          local' = local.set(p, withExpected(local.get(p),
            match slotVal.get(b).get(s) { | Some(e) => Some(e.v) | None => None },
            slotTag.get(b).get(s))),
        }
      },
      unchanged_control,
      unchanged_shared,
    }
  }

  action P6(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    all {
      pc.get(p) == PcP6,
      if (header.get(b) != local.get(p).hLoop) {
        pc' = pc.set(p, PcP4)
      } else {
        pc' = pc.set(p, PcP7)
      },
      unchanged_control,
      unchanged_shared,
      unchanged_local,
    }
  }

  action P7(p) = {
    val k = keyOfProc(p)
    val v = valOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    all {
      pc.get(p) == PcP7,
      if (p7SuccessGuard(p)) {
        all {
          slotVal' = slotVal.set(b, slotVal.get(b).set(s, Some({ k: k, v: v }))),
          slotTag' = slotTag.set(b, slotTag.get(b).set(s, Some(nextTag))),
          nextTag' = nextTag + 1,
          ret' = ret.set(p, mkResult(true, local.get(p).expectedVal)),
          op' = op.set(p, None),
          arg' = arg.set(p, None),
          pc' = pc.set(p, PcIdle),
        }
      } else {
        all {
          slotVal' = slotVal,
          slotTag' = slotTag,
          nextTag' = nextTag,
          ret' = ret,
          op' = op,
          arg' = arg,
          pc' = pc.set(p, PcP4),
        }
      },
      header' = header,
      slotKey' = slotKey,
      local' = local,
      activeGen' = activeGen,
      maxAllocatedGen' = maxAllocatedGen,
    }
  }

  // ------------------------------- Delete ----------------------------------

  // Fused classification load — same three-branch shape as G1 (design §5).
  action D1(p) = {
    val k = keyOfProc(p)
    val g = local.get(p).gen
    val b = binFor(k, g)
    val h = header.get(b)
    all {
      pc.get(p) == PcD1,
      if (h.binState == NoTransfer) all {
        local' = local.set(p, withH0(local.get(p), h)),
        pc' = pc.set(p, PcD2),
      } else if (h.binState == DoneTransfer) all {
        local' = local.set(p, withGen(local.get(p), g + 1)),
        pc' = pc.set(p, PcD1),
      } else all {
        local' = local.set(p, withGen(local.get(p), activeGen)),
        pc' = pc.set(p, PcD1),
      },
      unchanged_control,
      unchanged_shared,
    }
  }

  action D2(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    all {
      pc.get(p) == PcD2,
      local' = local.set(p, withTargetSlot(local.get(p), slotForKeyByHeader(local.get(p).h0, b, k))),
      pc' = pc.set(p, PcD3),
      unchanged_control,
      unchanged_shared,
    }
  }

  action D3(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    all {
      pc.get(p) == PcD3,
      if (header.get(b) != local.get(p).h0) {
        all {
          pc' = pc.set(p, PcD1),
          ret' = ret,
          op' = op,
          arg' = arg,
        }
      } else if (keyAbsentGuard(p)) {
        all {
          ret' = ret.set(p, mkResult(false, None)),
          op' = op.set(p, None),
          arg' = arg.set(p, None),
          pc' = pc.set(p, PcIdle),
        }
      } else {
        all {
          pc' = pc.set(p, PcD4),
          ret' = ret,
          op' = op,
          arg' = arg,
        }
      },
      unchanged_shared,
      unchanged_local,
    }
  }

  // D4 classifies its hLoop load (delete.go:89's explicit in-loop recheck,
  // design §5): non-NoTransfer routes to a FULL retry through the fused D1
  // classification — Done walks one gen, InTransfer reloads m.active.
  action D4(p) = {
    val k = keyOfProc(p)
    val g = local.get(p).gen
    val b = binFor(k, g)
    val h = header.get(b)
    all {
      pc.get(p) == PcD4,
      if (h.binState == NoTransfer) all {
        local' = local.set(p, withHLoop(local.get(p), h)),
        pc' = pc.set(p, PcD5),
      } else if (h.binState == DoneTransfer) all {
        local' = local.set(p, withGen(local.get(p), g + 1)),
        pc' = pc.set(p, PcD1),
      } else all {
        local' = local.set(p, withGen(local.get(p), activeGen)),
        pc' = pc.set(p, PcD1),
      },
      unchanged_control,
      unchanged_shared,
    }
  }

  action D5(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    val retry =
      local.get(p).hLoop.slotState.get(s) != Valid or
        slotKey.get(b).get(s) != Some(HKey(k)) or
        slotVal.get(b).get(s) == None
    all {
      pc.get(p) == PcD5,
      if (retry) {
        all {
          pc' = pc.set(p, PcD1),
          local' = local,
        }
      } else {
        all {
          pc' = pc.set(p, PcD6),
          // expectedVal stays Option[VAL] (it feeds ret): project the entry.
          local' = local.set(p, withExpected(local.get(p),
            match slotVal.get(b).get(s) { | Some(e) => Some(e.v) | None => None },
            slotTag.get(b).get(s))),
        }
      },
      unchanged_control,
      unchanged_shared,
    }
  }

  action D6(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    all {
      pc.get(p) == PcD6,
      if (header.get(b) != local.get(p).hLoop) {
        pc' = pc.set(p, PcD4)
      } else {
        pc' = pc.set(p, PcD7)
      },
      unchanged_control,
      unchanged_shared,
      unchanged_local,
    }
  }

  action D7(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    all {
      pc.get(p) == PcD7,
      if (
        slotKey.get(b).get(s) == Some(HKey(k)) and
        slotTag.get(b).get(s) == local.get(p).expectedTag and
        slotTag.get(b).get(s) != None and
        slotVal.get(b).get(s) != None
      ) {
        all {
          slotVal' = slotVal.set(b, slotVal.get(b).set(s, None)),
          slotTag' = slotTag.set(b, slotTag.get(b).set(s, None)),
          ret' = ret.set(p, mkResult(true, local.get(p).expectedVal)),
          pc' = pc.set(p, PcD8),
          op' = op,
          arg' = arg,
        }
      } else {
        all {
          slotVal' = slotVal,
          slotTag' = slotTag,
          ret' = ret,
          op' = op,
          arg' = arg,
          pc' = pc.set(p, PcD4),
        }
      },
      header' = header,
      slotKey' = slotKey,
      nextTag' = nextTag,
      local' = local,
      activeGen' = activeGen,
      maxAllocatedGen' = maxAllocatedGen,
    }
  }

  action D8(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    all {
      pc.get(p) == PcD8,
      if (header.get(b).slotState.get(s) == Valid and slotVal.get(b).get(s) == None and slotTag.get(b).get(s) == None) {
        header' = header.set(b, clearSlotState(header.get(b), s, Invalid))
      } else {
        header' = header
      },
      pc' = pc.set(p, PcIdle),
      op' = op.set(p, None),
      arg' = arg.set(p, None),
      ret' = ret,
      slotKey' = slotKey,
      slotVal' = slotVal,
      slotTag' = slotTag,
      nextTag' = nextTag,
      local' = local,
      activeGen' = activeGen,
      maxAllocatedGen' = maxAllocatedGen,
    }
  }

  // --------------------------- LoadOrCompute ------------------------------
  // Mirrors Insert; publishes to Shadow at LC5, runs fn while in Shadow, then
  // commits (Shadow -> Valid with fn's value) at LC7, or aborts via a
  // TWO-PHASE path: LC7 posts the result and moves Shadow -> Trying (the
  // abort's linearization point), LC9 clears the ghost val/tag and moves
  // Trying -> Invalid. The two phases exist only because of the spec's
  // anyVal ghost placeholder (there is ghost state to clear); the Go
  // implementation keeps the entry nil through the window, has nothing to
  // clear, and aborts with a SINGLE CAS Shadow -> Invalid (see LC4's
  // implementation-contract comment).

  // Fused classification load — same three-branch shape as G1 (design §5).
  action LC1(p) = {
    val k = keyOfProc(p)
    val g = local.get(p).gen
    val b = binFor(k, g)
    val h = header.get(b)
    all {
      pc.get(p) == PcLC1,
      if (h.binState == NoTransfer) all {
        local' = local.set(p, withH0(local.get(p), h)),
        pc' = pc.set(p, PcLC2),
      } else if (h.binState == DoneTransfer) all {
        local' = local.set(p, withGen(local.get(p), g + 1)),
        pc' = pc.set(p, PcLC1),
      } else all {
        local' = local.set(p, withGen(local.get(p), activeGen)),
        pc' = pc.set(p, PcLC1),
      },
      unchanged_control,
      unchanged_shared,
    }
  }

  action LC2(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val h = local.get(p).h0
    all {
      pc.get(p) == PcLC2,
      if (header.get(b) != h) {
        all {
          pc' = pc.set(p, PcLC1),
          local' = local,
          ret' = ret,
          op' = op,
          arg' = arg,
        }
      } else if (lc2ReturnGuard(p)) {
        all {
          ret' = ret.set(p, mkResult(true, readVisibleByHeader(h, b, k))),
          op' = op.set(p, None),
          arg' = arg.set(p, None),
          pc' = pc.set(p, PcIdle),
          local' = local,
        }
      } else if (shadowSlotsByHeader(h, b, k).size() != 0) {
        // Wait for the holder.
        all {
          pc' = pc.set(p, PcLC1),
          local' = local,
          ret' = ret,
          op' = op,
          arg' = arg,
        }
      } else {
        val free = slotIdx.filter(s => h.slotState.get(s) == Invalid)
        if (free.size() != 0) {
          all {
            local' = local.set(p, withTargetSlot(local.get(p), minOr0(free))),
            pc' = pc.set(p, PcLC3),
            ret' = ret,
            op' = op,
            arg' = arg,
          }
        } else {
          all {
            pc' = pc.set(p, PcLC1),
            local' = local,
            ret' = ret,
            op' = op,
            arg' = arg,
          }
        }
      },
      unchanged_shared,
    }
  }

  action LC3(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    all {
      pc.get(p) == PcLC3,
      if (s != 0 and header.get(b) == local.get(p).h0 and header.get(b).slotState.get(s) == Invalid) {
        all {
          header' = header.set(b, updateSlotState(header.get(b), s, Trying)),
          pc' = pc.set(p, PcLC4),
        }
      } else {
        all {
          header' = header,
          pc' = pc.set(p, PcLC1),
        }
      },
      unchanged_control,
      slotKey' = slotKey,
      slotVal' = slotVal,
      slotTag' = slotTag,
      nextTag' = nextTag,
      activeGen' = activeGen,
      maxAllocatedGen' = maxAllocatedGen,
      unchanged_local,
    }
  }

  action LC4(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    all {
      pc.get(p) == PcLC4,
      // anyVal is a placeholder; LC7 overwrites it with fn's value (or clears it).
      // IMPLEMENTATION CONTRACT (Go) — the OWNERSHIP form, not an instant
      // invariant: (1) at Shadow entry the pointer is nil BY CONSTRUCTION
      // (reserve requires Invalid, and Invalid => nil per invalidSlotClean);
      // (2) while Shadow, slot.Val is OWNER-EXCLUSIVE — the same rule that
      // protects Trying; no other thread may read or act on a non-Valid
      // slot's .Val; (3) the commit is release-store(entry) THEN CAS
      // Shadow->Valid, so a transient Shadow-with-entry window physically
      // exists — unobservable by the ownership rule and harmless by
      // mechanism (the commit CAS bumps the version, so straddling seqlock
      // readers retry; a racing DWCAS compares a pointer captured under a
      // Valid window and fails); (4) in GO the abort needs no cleanup —
      // nothing was stored — a single CAS Shadow->Invalid suffices (the
      // SPEC's abort is two-phase, LC7 Shadow->Trying + LC9 cleanup, only
      // because this ghost placeholder must be cleared). Some(anyVal) here is
      // GHOST STATE: it exists so the slot carries a tag (= pointer identity)
      // through the window, and liveKeyUniquePerBin's Shadow arm leans on
      // val != None via ownerSlotFilled (F2). A Go implementation must
      // derive Shadow-uniqueness from the KEY (slotKey, written before the
      // Shadow release-CAS, hence acquire-coherent for waiters), never from
      // the entry pointer.
      slotKey' = slotKey.set(b, slotKey.get(b).set(s, Some(HKey(k)))),
      slotVal' = slotVal.set(b, slotVal.get(b).set(s, Some({ k: k, v: anyVal }))),
      slotTag' = slotTag.set(b, slotTag.get(b).set(s, Some(nextTag))),
      nextTag' = nextTag + 1,
      pc' = pc.set(p, PcLC5),
      unchanged_control,
      header' = header,
      local' = local,
      activeGen' = activeGen,
      maxAllocatedGen' = maxAllocatedGen,
    }
  }

  action LC5(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    all {
      pc.get(p) == PcLC5,
      if (lc5SuccessGuard(p)) {
        all {
          header' = header.set(b, updateSlotState(header.get(b), s, Shadow)),
          pc' = pc.set(p, PcLC6),
        }
      } else {
        // Header drifted; unreserve and retry. fn has not run yet.
        all {
          header' = header,
          pc' = pc.set(p, PcLC8),
        }
      },
      unchanged_control,
      slotKey' = slotKey,
      slotVal' = slotVal,
      slotTag' = slotTag,
      nextTag' = nextTag,
      activeGen' = activeGen,
      maxAllocatedGen' = maxAllocatedGen,
      unchanged_local,
    }
  }

  // LC6 is the §5 table's HOLDER rule: spin on InTransfer (never restart —
  // restarting would orphan the published Shadow claim), relocate on Done
  // (PcLC10), proceed to LC7 only with a NoTransfer hLoop. This is what
  // makes a mid-transfer commit impossible: an LC7 commit under a stable
  // InTransfer header would turn a slot Valid mid-transfer and rsShadowCarry
  // would copy the stale ghost — silently dropping the value at rsDone.
  action LC6(p) = {
    val k = keyOfProc(p)
    val g = local.get(p).gen
    val b = binFor(k, g)
    val h = header.get(b)
    all {
      pc.get(p) == PcLC6,
      if (h.binState == NoTransfer) all {
        // Post-fn: reload hLoop for the commit CAS.
        local' = local.set(p, withHLoop(local.get(p), h)),
        pc' = pc.set(p, PcLC7),
      } else if (h.binState == DoneTransfer) all {
        local' = local,
        pc' = pc.set(p, PcLC10),        // relocate to the carried claim
      } else all {
        local' = local,                  // InTransfer: SPIN (never restart —
        pc' = pc.set(p, PcLC6),         // restarting orphans the Shadow claim)
      },
      unchanged_control,
      unchanged_shared,
    }
  }

  // LC10: holder relocation after its bin's DoneTransfer (design §5). Finds
  // the carried claim in the child by (Shadow ∧ HKey(k)) — unique by claim
  // continuity — and refreshes ALL local snapshots (h0 too: leaving the
  // parent's h0 breaks versionMonotonic/reserveBumpedVersion/snapStateAgrees
  // at this step). Re-enters LC6: if the child is itself InTransfer/Done
  // (2-gen configs) the LC6 classification spins/walks again.
  action LC10(p) = {
    val k = keyOfProc(p)
    val g = local.get(p).gen + 1
    val b = binFor(k, g)
    val h = header.get(b)
    // DOMAIN GUARD (1b anchor-proofing; review finding): pc == PcLC10 with
    // gen == maxGen is unreachable in real runs (a maxGen bin is never
    // Done, so LC6 never routes there), but the induction anchor can
    // fabricate it — binFor(k, maxGen+1) lies outside binDomain, and an
    // unconstrained out-of-domain header read would hand Apalache a
    // spurious consecution counterexample (gen' = maxGen+1 breaking
    // typeOK). The empty shadow set routes the fabricated state to the
    // wait branch; h is never forced there (vals are lazy-on-use).
    val shadows = if (g > maxGen) Set() else slotIdx.filter(s =>
      h.slotState.get(s) == Shadow and slotKey.get(b).get(s) == Some(HKey(k)))
    all {
      pc.get(p) == PcLC10,
      if (shadows.size() != 0) all {
        local' = local.set(p, {
          ...local.get(p),
          gen: g,
          targetSlot: minOr0(shadows),
          h0: h,
          hLoop: h,
        }),
        pc' = pc.set(p, PcLC6),
      } else all {
        // Defensive totality only: in real runs a PcLC10 proc ALWAYS finds
        // a claim one generation ahead — rsDone requires every snapshot
        // Shadow carried, and LC5 cannot publish a Shadow the snapshot
        // missed (its expectedH compare fails once the bin left
        // NoTransfer); a dead child's RESTORED Shadow also matches (that is
        // the double-relocation stepping stone). This branch is reached
        // only by anchor-fabricated states (see the domain guard above).
        local' = local,
        pc' = pc.set(p, PcLC10),
      },
      unchanged_control,
      unchanged_shared,
    }
  }

  action LC7(p) = {
    val k = keyOfProc(p)
    val v = valOfProc(p)
    val save = saveOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    all {
      pc.get(p) == PcLC7,
      if (lc7SuccessGuard(p)) {
        if (save) {
          // Commit (linearization point for save=true).
          all {
            header' = header.set(b, updateSlotState(header.get(b), s, Valid)),
            slotVal' = slotVal.set(b, slotVal.get(b).set(s, Some({ k: k, v: v }))),
            slotTag' = slotTag.set(b, slotTag.get(b).set(s, Some(nextTag))),
            nextTag' = nextTag + 1,
            ret' = ret.set(p, mkResult(false, Some(v))),
            op' = op.set(p, None),
            arg' = arg.set(p, None),
            pc' = pc.set(p, PcIdle),
            local' = local,
          }
        } else {
          // Abort phase 1: Shadow -> Trying, and LINEARIZATION POINT for
          // save=false. The result (false, computed v) is fixed here, not at
          // the LC9 return: at this step the slot is still Shadow with key k,
          // so liveKeyUniquePerBin + shadowSlotKeyed guarantee k is absent from
          // the visible set, which is exactly the abstract precondition for the
          // "absent, fn ran, not saved" outcome. (Mirrors the save=true commit
          // above, which also linearizes at LC7.) LC9 is then pure cleanup.
          // The Shadow -> Trying flip keeps the slot invisible to L3/I2.5 scans,
          // so LC9 can clear slot.Val without exposing a Shadow-with-nil-entry
          // window to other LoadOrComputes.
          all {
            header' = header.set(b, updateSlotState(header.get(b), s, Trying)),
            slotVal' = slotVal,
            slotTag' = slotTag,
            nextTag' = nextTag,
            ret' = ret.set(p, mkResult(false, Some(v))),
            op' = op,
            arg' = arg,
            pc' = pc.set(p, PcLC9),
            local' = local,
          }
        }
      } else {
        // Header drifted; reload and retry.
        all {
          header' = header,
          slotVal' = slotVal,
          slotTag' = slotTag,
          nextTag' = nextTag,
          ret' = ret,
          op' = op,
          arg' = arg,
          pc' = pc.set(p, PcLC6),
          local' = local,
        }
      },
      slotKey' = slotKey,
      activeGen' = activeGen,
      maxAllocatedGen' = maxAllocatedGen,
    }
  }

  // LC8 mirrors I6: unreserve on LC5 failure, then retry from LC1.
  action LC8(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    all {
      pc.get(p) == PcLC8,
      // Unreserve REFUSAL (design §5): see I6 — abandoned on a
      // non-NoTransfer bin; the LC1 classification redirects.
      if (s != 0 and header.get(b).slotState.get(s) == Trying and
          slotKey.get(b).get(s) == Some(HKey(k)) and
          header.get(b).binState == NoTransfer) {
        all {
          header' = header.set(b, updateSlotState(header.get(b), s, Invalid)),
          slotVal' = slotVal.set(b, slotVal.get(b).set(s, None)),
          slotTag' = slotTag.set(b, slotTag.get(b).set(s, None)),
        }
      } else {
        all {
          header' = header,
          slotVal' = slotVal,
          slotTag' = slotTag,
        }
      },
      pc' = pc.set(p, PcLC1),
      unchanged_control,
      slotKey' = slotKey,
      nextTag' = nextTag,
      activeGen' = activeGen,
      maxAllocatedGen' = maxAllocatedGen,
      unchanged_local,
    }
  }

  // LC9 is abort phase 2: pure cleanup — clear slot.Val/Tag, CAS Trying ->
  // Invalid, clear op (the return). The result was already posted to ret at
  // LC7 (the linearization point), so LC9 does NOT touch ret. The slot
  // transitioned Shadow -> Trying at LC7; while Trying it's invisible to
  // L3/I2.5 scans, so clearing the entry pointer here cannot be observed.
  action LC9(p) = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    all {
      pc.get(p) == PcLC9,
      // Unreserve REFUSAL (design §5): the abort's cleanup CAS also refuses
      // on a non-NoTransfer bin — the ghost val/tag stay behind in the
      // abandoned Trying slot (daemon skips Trying slots, so they are never
      // carried); the return (posted at LC7) completes regardless.
      if (s != 0 and header.get(b).slotState.get(s) == Trying and
          slotKey.get(b).get(s) == Some(HKey(k)) and
          header.get(b).binState == NoTransfer) {
        all {
          header' = header.set(b, updateSlotState(header.get(b), s, Invalid)),
          slotVal' = slotVal.set(b, slotVal.get(b).set(s, None)),
          slotTag' = slotTag.set(b, slotTag.get(b).set(s, None)),
        }
      } else {
        all {
          header' = header,
          slotVal' = slotVal,
          slotTag' = slotTag,
        }
      },
      pc' = pc.set(p, PcIdle),
      op' = op.set(p, None),
      arg' = arg.set(p, None),
      ret' = ret,
      slotKey' = slotKey,
      nextTag' = nextTag,
      local' = local,
      activeGen' = activeGen,
      maxAllocatedGen' = maxAllocatedGen,
    }
  }

  // ------------------------------------------------------------------------
  // Keep branch predicates centralized and reuse them in both:
  // 1) operation actions (G2/I2/I5/P3/P7/D3), and
  // 2) step-classification wrappers (intermAction/returnAction).
  // This avoids duplicating branching logic in multiple places.

  def g2ReturnGuard(p: PROC): bool = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    header.get(b) == local.get(p).h0
  }

  def i2ReturnGuard(p: PROC): bool = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    header.get(b) == local.get(p).h0 and candidateSlotsByHeader(local.get(p).h0, b, k).size() != 0
  }

  def i5SuccessGuard(p: PROC): bool = {
    val k = keyOfProc(p)
    val v = valOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    val expectedH = {
      version: local.get(p).h0.version + 1,
      binState: local.get(p).h0.binState,
      slotState: local.get(p).h0.slotState.set(s, Trying),
    }
    header.get(b) == expectedH and
      slotKey.get(b).get(s) == Some(HKey(k)) and
      slotVal.get(b).get(s) == Some({ k: k, v: v }) and
      slotTag.get(b).get(s) != None
  }

  def keyAbsentGuard(p: PROC): bool = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    header.get(b) == local.get(p).h0 and local.get(p).targetSlot == 0
  }

  def p7SuccessGuard(p: PROC): bool = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    slotKey.get(b).get(s) == Some(HKey(k)) and
      slotTag.get(b).get(s) == local.get(p).expectedTag and
      slotTag.get(b).get(s) != None and
      slotVal.get(b).get(s) != None
  }

  def lc2ReturnGuard(p: PROC): bool = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val h = local.get(p).h0
    header.get(b) == h and candidateSlotsByHeader(h, b, k).size() != 0
  }

  def lc5SuccessGuard(p: PROC): bool = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    val expectedH = {
      version: local.get(p).h0.version + 1,
      binState: local.get(p).h0.binState,
      slotState: local.get(p).h0.slotState.set(s, Trying),
    }
    header.get(b) == expectedH and
      slotKey.get(b).get(s) == Some(HKey(k)) and
      slotVal.get(b).get(s) == Some({ k: k, v: anyVal }) and
      slotTag.get(b).get(s) != None
  }

  def lc7SuccessGuard(p: PROC): bool = {
    val k = keyOfProc(p)
    val b = binFor(k, local.get(p).gen)
    val s = local.get(p).targetSlot
    header.get(b) == local.get(p).hLoop and
      local.get(p).hLoop.slotState.get(s) == Shadow
  }

  // LC7 only returns on the save=true commit path; the save=false abort
  // advances to PcLC9 (still intermediate).
  def lc7CommitReturnGuard(p: PROC): bool = {
    lc7SuccessGuard(p) and saveOfProc(p)
  }

  action invokeAction = {
    nondet p = procSet.oneOf()
    invokeLine(p)
  }

  action getIntermAction = {
    nondet p = procSet.oneOf()
    any {
      G1(p),
      all {
        G2(p),
        not(g2ReturnGuard(p)),
      },
    }
  }

  action getReturnAction = {
    nondet p = procSet.oneOf()
    all {
      G2(p),
      g2ReturnGuard(p),
    }
  }

  action insertIntermAction = {
    nondet p = procSet.oneOf()
    any {
      I1(p),
      all {
        I2(p),
        not(i2ReturnGuard(p)),
      },
      I3(p),
      I4(p),
      all {
        I5(p),
        not(i5SuccessGuard(p)),
      },
      I6(p),
    }
  }

  action insertReturnAction = {
    nondet p = procSet.oneOf()
    any {
      all {
        I2(p),
        i2ReturnGuard(p),
      },
      all {
        I5(p),
        i5SuccessGuard(p),
      },
    }
  }

  action putIntermAction = {
    nondet p = procSet.oneOf()
    any {
      P1(p),
      P2(p),
      all {
        P3(p),
        not(keyAbsentGuard(p)),
      },
      P4(p),
      P5(p),
      P6(p),
      all {
        P7(p),
        not(p7SuccessGuard(p)),
      },
    }
  }

  action putReturnAction = {
    nondet p = procSet.oneOf()
    any {
      all {
        P3(p),
        keyAbsentGuard(p),
      },
      all {
        P7(p),
        p7SuccessGuard(p),
      },
    }
  }

  action deleteIntermAction = {
    nondet p = procSet.oneOf()
    any {
      D1(p),
      D2(p),
      all {
        D3(p),
        not(keyAbsentGuard(p)),
      },
      D4(p),
      D5(p),
      D6(p),
      D7(p),
    }
  }

  action deleteReturnAction = {
    nondet p = procSet.oneOf()
    any {
      all {
        D3(p),
        keyAbsentGuard(p),
      },
      D8(p),
    }
  }

  action loadComputeIntermAction = {
    nondet p = procSet.oneOf()
    any {
      LC1(p),
      all {
        LC2(p),
        not(lc2ReturnGuard(p)),
      },
      LC3(p),
      LC4(p),
      LC5(p),
      LC6(p),
      all {
        LC7(p),
        not(lc7CommitReturnGuard(p)),
      },
      LC8(p),
      LC10(p),
    }
  }

  action loadComputeReturnAction = {
    nondet p = procSet.oneOf()
    any {
      all {
        LC2(p),
        lc2ReturnGuard(p),
      },
      all {
        LC7(p),
        lc7CommitReturnGuard(p),
      },
      LC9(p),
    }
  }

  action intermAction = any {
    getIntermAction,
    insertIntermAction,
    putIntermAction,
    deleteIntermAction,
    loadComputeIntermAction,
  }

  action returnAction = any {
    getReturnAction,
    insertReturnAction,
    putReturnAction,
    deleteReturnAction,
    loadComputeReturnAction,
  }

  action step = any {
    invokeAction,
    intermAction,
    returnAction,
  }

  pure def typeOKPure(st: SpecState): bool = {
    binDomain.forall(b =>
      slotIdx.forall(s =>
        (st.slotVal.get(b).get(s) == None) iff (st.slotTag.get(b).get(s) == None)
      )
    ) and

    binDomain.forall(b => st.header.get(b).version >= 0) and
    st.nextTag >= 1 and

    // Generation-counter sanity (design §3): resize-active is
    // maxAllocatedGen == activeGen + 1; the chain never extends further.
    st.activeGen >= 0 and
    st.maxAllocatedGen >= st.activeGen and
    st.maxAllocatedGen <= maxGen and
    st.maxAllocatedGen <= st.activeGen + 1 and
    procSet.forall(p => genDomain.contains(st.local.get(p).gen)) and

    procSet.forall(p => st.op.get(p) == opFromPC(st.pc.get(p))) and
    procSet.forall(p => slotIdxExt.contains(st.local.get(p).targetSlot)) and
    procSet.forall(p => st.local.get(p).h0.version >= 0 and st.local.get(p).hLoop.version >= 0) and

    procSet.forall(p =>
      if (st.op.get(p) == None)
        st.arg.get(p) == None
      else match st.arg.get(p) {
        | Some(a) => argsOf(st.op.get(p)).contains(a)
        | _ => false
      }
    )
  }

  def typeOK: bool = typeOKPure(currentSpecState)
}
