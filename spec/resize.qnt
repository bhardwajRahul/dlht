module resize {
  import types.* from "./types"
  import protocol.* from "./protocol"

  // Daemon transfer bookkeeping (design §4). Actions here assign protocol
  // vars cross-module (the established indInit pattern). The daemon is a
  // safety over-approximation of Go's insert-triggered + FAA work-stealing
  // machinery (design D2): nondet trigger, per-bin steps in any
  // interleaving, finalize when all bins of the resizing gen are Done.
  var snapshot: BinIdx -> Option[Header]   // rsBegin's pre-OR header per bin
  var cursor: BinIdx -> SlotIdx            // 0 = not begun; counts processed slots

  action resizeInit = all {
    snapshot' = binDomain.mapBy(_ => None),
    cursor' = binDomain.mapBy(_ => 0),
  }

  action unchanged_resize = all { snapshot' = snapshot, cursor' = cursor }

  // transferable/nextSlot (the snapshot-walk helpers) live in protocol.qnt:
  // the R-family invariants need them and must not import this module.

  // rsTrigger (design §4.1): models allocate + indexNext publish + ctx
  // activation. Go's ResizeReserved placeholder window is absorbed (D2).
  action rsTrigger = all {
    maxAllocatedGen == activeGen,
    activeGen < maxGen,
    maxAllocatedGen' = activeGen + 1,
    activeGen' = activeGen,
    header' = header, slotKey' = slotKey, slotVal' = slotVal,
    slotTag' = slotTag, nextTag' = nextTag,
    pc' = pc, op' = op, arg' = arg, ret' = ret, local' = local,
    unchanged_resize,
  }

  // rsBegin (design §4.2): InTransfer WITHOUT a version bump (Go's OR), and
  // the pre-OR snapshot.
  action rsBegin = {
    nondet b = binDomain.oneOf()
    all {
      maxAllocatedGen == activeGen + 1,
      genOfBin(b) == activeGen,
      header.get(b).binState == NoTransfer,
      snapshot' = snapshot.set(b, Some(header.get(b))),
      header' = header.set(b, { ...header.get(b), binState: InTransfer }),
      cursor' = cursor,
      slotKey' = slotKey, slotVal' = slotVal, slotTag' = slotTag,
      nextTag' = nextTag, activeGen' = activeGen, maxAllocatedGen' = maxAllocatedGen,
      pc' = pc, op' = op, arg' = arg, ret' = ret, local' = local,
    }
  }

  // rsSentinel (design §4.3): its own atomic step — the StoreLoad cut.
  // Applies only to snapshot-VALID slots (Shadow slots are never sentineled).
  //
  // TOTALITY PATTERN (empirically required — Quint's effect checker rejects
  // a match whose arms assign different update sets): unwrap Options in vals
  // with never-used defaults, keep ALL guards as pure bools in the all-block,
  // and make every assignment unconditional. The `snapshot.get(b) != None`
  // guard keeps the action disabled when the default would matter (and the
  // emptyHeader default independently yields nextSlot == 0, failing s != 0).
  action rsSentinel = {
    nondet b = binDomain.oneOf()
    val snap = match snapshot.get(b) { | Some(sn) => sn | None => emptyHeader }
    val s = nextSlot(snap, cursor.get(b))
    all {
      header.get(b).binState == InTransfer,
      snapshot.get(b) != None,
      s != 0,
      snap.slotState.get(s) == Valid,
      slotKey.get(b).get(s) != Some(HSentinel),   // not yet sentineled
      slotKey' = slotKey.set(b, slotKey.get(b).set(s, Some(HSentinel))),
      header' = header, slotVal' = slotVal, slotTag' = slotTag,
      nextTag' = nextTag, activeGen' = activeGen, maxAllocatedGen' = maxAllocatedGen,
      pc' = pc, op' = op, arg' = arg, ret' = ret, local' = local,
      unchanged_resize,
    }
  }

  // rsMove (design §4.3): fused read+place (child unobservable until Done).
  // Fires only after the slot was sentineled. Skips a concurrently-deleted
  // entry (val None). Fresh tag models the fresh child entry pointer.
  //
  // VAL-DOMAIN DEFENSE (load-bearing — do not "simplify"). Probe-confirmed
  // evaluator semantics: `all` evaluates conjuncts IN ORDER with
  // short-circuit, and action vals are forced LAZILY on first use — but
  // Apalache translates every expression regardless, where an out-of-domain
  // map read is an UNCONSTRAINED value. So every potentially-out-of-domain
  // access must be gated by an internal conditional whose guard makes the
  // dangerous read unreachable/irrelevant: entryOpt's `s == 0` arm and cs's
  // `entryOpt == None` arm keep disabled tries domain-safe (a bin whose
  // snapshot is absent yields s == 0; a Done bin yields nextSlot == 0).
  // binFor is pure arithmetic and safe to compute even when unused. The
  // deleted-skip case uses if/else with IDENTICAL update sets in both
  // branches (the effect checker rejects mismatched update sets).
  //
  // 1b WIRE-ORDER NOTE (review finding): cs forces header.get(cb) with
  // cb = binFor(e.k, genOfBin(b)+1), out-of-domain for a LAST-generation b.
  // Reachably safe (snapshot present ⟹ the bin began transfer ⟹
  // genOfBin(b) < maxGen), but once stage 1b folds snapshot/cursor into the
  // induction anchor, a fabricated `snapshot(b) != None` on a maxGen bin
  // reproduces the unconstrained-read hazard inside rsMove/rsShadowCarry/
  // rsSentinel consecution. The anchor guard must include rsInv (R6 + R1 +
  // typeOK imply the needed fact) BEFORE any consecution over daemon steps.
  action rsMove = {
    nondet b = binDomain.oneOf()
    val snap = match snapshot.get(b) { | Some(sn) => sn | None => emptyHeader }
    val s = nextSlot(snap, cursor.get(b))
    val entryOpt = if (s == 0) None else slotVal.get(b).get(s)
    val e = match entryOpt { | Some(x) => x | None => { k: anyKey, v: anyVal } }  // dummy unused when None
    val cb = binFor(e.k, genOfBin(b) + 1)
    val cs = if (entryOpt == None) 0
             else minOr0(slotIdx.filter(t => header.get(cb).slotState.get(t) == Invalid))
    all {
      header.get(b).binState == InTransfer,
      snapshot.get(b) != None,
      s != 0,
      snap.slotState.get(s) == Valid,
      slotKey.get(b).get(s) == Some(HSentinel),       // sentinel step done
      (entryOpt != None).implies(cs != 0),            // child free slot exists (R12b)
      if (entryOpt != None) all {
        header' = header.set(cb, updateSlotState(header.get(cb), cs, Valid)),
        slotKey' = slotKey.set(cb, slotKey.get(cb).set(cs, Some(HKey(e.k)))),
        slotVal' = slotVal.set(cb, slotVal.get(cb).set(cs, Some(e))),
        slotTag' = slotTag.set(cb, slotTag.get(cb).set(cs, Some(nextTag))),
        nextTag' = nextTag + 1,
      } else all {                                     // concurrently deleted: skip
        header' = header, slotKey' = slotKey, slotVal' = slotVal,
        slotTag' = slotTag, nextTag' = nextTag,
      },
      cursor' = cursor.set(b, s),
      snapshot' = snapshot,
      activeGen' = activeGen, maxAllocatedGen' = maxAllocatedGen,
      pc' = pc, op' = op, arg' = arg, ret' = ret, local' = local,
    }
  }

  // rsShadowCarry (design §4.3): SPEC-PRESCRIBED extension (Go's resize has
  // no Shadow today; this is the carry-forward contract's normative home).
  // No sentinel: Put/Delete never target Shadow slots. Ghost placeholder val
  // + fresh tag carried per the spec's Shadow convention.
  action rsShadowCarry = {
    nondet b = binDomain.oneOf()
    val snap = match snapshot.get(b) { | Some(sn) => sn | None => emptyHeader }
    val s = nextSlot(snap, cursor.get(b))
    val hkOpt = if (s == 0) None else slotKey.get(b).get(s)
    val isHKey = match hkOpt {
      | Some(hk) => match hk { | HKey(_) => true | HSentinel => false }
      | None => false
    }
    val k = match hkOpt {
      | Some(hk) => match hk { | HKey(kk) => kk | HSentinel => anyKey }
      | None => anyKey
    }
    val cb = binFor(k, genOfBin(b) + 1)
    val cs = if (not(isHKey)) 0
             else minOr0(slotIdx.filter(t => header.get(cb).slotState.get(t) == Invalid))
    all {
      header.get(b).binState == InTransfer,
      snapshot.get(b) != None,
      s != 0,
      snap.slotState.get(s) == Shadow,
      isHKey,        // guaranteed by shadowSlotKeyed; Shadow is never sentineled
      cs != 0,       // child free slot exists (R12b)
      header' = header.set(cb, updateSlotState(header.get(cb), cs, Shadow)),
      slotKey' = slotKey.set(cb, slotKey.get(cb).set(cs, Some(HKey(k)))),
      slotVal' = slotVal.set(cb, slotVal.get(cb).set(cs, Some({ k: k, v: anyVal }))),
      slotTag' = slotTag.set(cb, slotTag.get(cb).set(cs, Some(nextTag))),
      nextTag' = nextTag + 1,
      cursor' = cursor.set(b, s),
      snapshot' = snapshot,
      activeGen' = activeGen, maxAllocatedGen' = maxAllocatedGen,
      pc' = pc, op' = op, arg' = arg, ret' = ret, local' = local,
    }
  }

  // rsDone (design §4.4): overwrite with the SNAPSHOT (not RMW) — discards
  // pre-Done D8 ANDs; only the header is restored (sentinels persist in the
  // dead bin's slotKeys forever); a post-Done straggler D8 may still mutate
  // the dead header (protocol's D8 has no binState check — faithful).
  action rsDone = {
    nondet b = binDomain.oneOf()
    val snap = match snapshot.get(b) { | Some(sn) => sn | None => emptyHeader }
    all {
      header.get(b).binState == InTransfer,
      snapshot.get(b) != None,
      nextSlot(snap, cursor.get(b)) == 0,   // all transferable processed
      header' = header.set(b, { ...snap, binState: DoneTransfer }),
      snapshot' = snapshot, cursor' = cursor,
      slotKey' = slotKey, slotVal' = slotVal, slotTag' = slotTag,
      nextTag' = nextTag, activeGen' = activeGen, maxAllocatedGen' = maxAllocatedGen,
      pc' = pc, op' = op, arg' = arg, ret' = ret, local' = local,
    }
  }

  // rsFinalize (design §4.5): all bins of the resizing gen Done -> m.active
  // advances. Go's active.Store + ctx teardown fuse here (review-verified).
  action rsFinalize = all {
    maxAllocatedGen == activeGen + 1,
    binDomain.forall(b =>
      (genOfBin(b) == activeGen).implies(header.get(b).binState == DoneTransfer)),
    activeGen' = activeGen + 1,
    maxAllocatedGen' = maxAllocatedGen,
    header' = header, slotKey' = slotKey, slotVal' = slotVal,
    slotTag' = slotTag, nextTag' = nextTag,
    pc' = pc, op' = op, arg' = arg, ret' = ret, local' = local,
    unchanged_resize,
  }

  action resizeStep = any { rsTrigger, rsBegin, rsSentinel, rsMove, rsShadowCarry, rsDone, rsFinalize }
}
