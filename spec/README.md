# DLHT Quint Spec — Verification Methodology

This directory formally models the DLHT lock-free hash table and verifies it with
[Quint](https://github.com/informalsystems/quint) + Apalache. Run everything with
`./verify.sh` (see [Toolchain](#toolchain) for the pinned versions).

## What is modeled

`protocol.qnt` models the DLHT operations — Get, Insert, Put, Delete, and
LoadOrCompute (with the `Shadow` slot state) — one atomic action per protocol
step (PC-indexed state machines: Get G1–G2, Insert I1–I6, Put P1–P7, Delete
D1–D8, LoadOrCompute LC1–LC10), over a **multi-generation flat bin
namespace** (design A′): generation *g* owns bins `2^g .. 2^(g+1)-1`,
`binFor(k, g)` is closed-form arithmetic, and configs pick `maxGen` ∈
{0, 1, 2} (maxGen=0 is the degenerate single-bin surface the Phase 0 results
live on).

`resize.qnt` models the **cooperative resize** as a daemon transfer machine
(design D2 — a safety over-approximation of Go's insert-triggered + FAA
work-stealing machinery): `rsTrigger` (allocate + indexNext publish),
`rsBegin` (InTransfer OR **without** a version bump + pre-OR snapshot),
`rsSentinel` (its own atomic step — the per-slot StoreLoad cut against
Put/Delete DWCAS), `rsMove` (fused read+place into the child; skips
concurrently-deleted entries), `rsShadowCarry` (the LoadOrCompute claim
carry — a spec-prescribed contract; today's Go resize has no Shadow),
`rsDone` (a snapshot **overwrite**, discarding transfer-window D8 ANDs;
sentinels persist in dead-bin slot keys forever), and `rsFinalize`
(`m.active` advances). `system.qnt` composes `systemStep = protocol step ∨
daemon step`. Ops classify `binState` per the design §5 normative table:
fused classification at every h0 load and D4 (Done → chain-walk exactly one
generation; InTransfer → reload `m.active`), **no check at P4** (the
pre-sentinel Put must remain carriable — put.go fidelity), unreserve refusal
at I6/LC8/LC9 (abandoned Trying slots), and the LC holder spin/relocate rule
(PcLC10) so a claim is never orphaned or committed mid-transfer.

Out of modeled scope (documented in the design, not silently dropped): chunk
work-stealing FAA bookkeeping and trigger timing (absorbed by the daemon
abstraction), link buckets/arena, the sentinel even/odd parity trick (the
modeled sentinel is type-distinct), Go's 8x/4x sizing tiers (growth factor 2),
`Range`/`Size`/`Stats`, weak memory (spec stays SC), liveness.

Key abstractions:
- A bin is a flat array of `slotsPerBin` slots; link buckets / the link arena /
  LinkMeta are abstracted away.
- `slotKey: Option[KEY]` models the slot's hash field; `slotVal: Option[VAL]`
  the entry pointer (`None` = nil); `slotTag: Option[int]` + a global `nextTag`
  model entry-pointer **identity**, so Put/Delete's `(hash, ptr)` DWCAS compare
  is modeled exactly.
- The `Some(anyVal)` a Shadow slot carries through LoadOrCompute's fn window is
  **spec-only ghost state** (it lets the slot bear a tag); the Go contract is
  the **ownership form**, not an instant invariant: the entry pointer is nil at
  Shadow entry (by construction: reserve requires Invalid, and Invalid ⟹ nil),
  stays owner-exclusive through the window (the same rule that protects
  Trying — no other thread may read a non-Valid slot's `.Val`), and the commit
  is release-store(entry) **then** CAS Shadow→Valid — the transient
  Shadow-with-entry window this creates is unobservable by the ownership rule
  and harmless by mechanism (the commit CAS bumps the seqlock version;
  a racing DWCAS compares a pointer captured under a Valid window and fails).
  In Go the abort therefore needs no cleanup — a single CAS Shadow→Invalid —
  whereas the **spec model's** abort is two-phase (LC7 Shadow→Trying posts the
  result; LC9 clears the ghost val/tag, Trying→Invalid) purely because the
  ghost placeholder must be cleared.
  Shadow-uniqueness must come from the key, never the pointer. The two
  contract corollaries (at-most-once fn per key, holder exclusivity) are
  checked in `verify.sh` stage 4 as `inv ⟹ contract` (0-step anchored,
  2-proc).
- Every CAS / seqlock check compares a whole `Header` record
  (`{version, binState, slotState}`), modeling the implementation's
  full-64-bit header CAS — transfer-awareness auto-threads through every
  existing guard with zero per-guard edits.
- `slotKey: Option[HashKey]` (`HKey(KEY) | HSentinel`) is the DWCAS-compare
  hash word; `slotVal: Option[Entry]` carries the entry's OWN key, the ground
  truth for **abstract** visibility (design §6). Operational scans
  (candidate sets, P2/D2 slot picks) match the hash word — a sentineled slot
  is never a candidate; the abstraction reads each key at its
  **authoritative generation** (least non-Done bin in its chain).

Resize modeling follows
`docs/superpowers/specs/2026-06-11-phase1-resize-modeling-design.md`; the
stage-1a evidence tier is described below.

## What is proved (and how)

1. **Inductive invariant** (`invariants.qnt::inv`, a conjunction of `typeOK`
   plus 32 families — the 27 Phase 0 families, several adjusted for transfer
   shapes per design §7, plus the generation-topology tier R1–R5). Proved
   *inductive*, not merely bounded, **on the maxGen=0 configs**:
   - **Base:** `init ⟹ inv`, checked as `quint verify verify/invariants_<cfg>
     --invariant=inv --max-steps=0`.
   - **Consecution:** `inv ∧ step ⟹ inv'`, checked as `quint verify
     verify/induction_<cfg> --invariant=inv --max-steps=1`, where
     `induction.qnt::indInit` constructs an *arbitrary* `inv`-satisfying state
     (the induction anchor).

   Configs: `1proc`, `2proc` (default), and `2proc_2key` (opt-in; see
   [Cost](#cost-and-tiers)). All at maxGen=0 (one gen-0 bin), 3 slots,
   valDomain {v1,v2}.

   Every family carries a `//` comment naming the protocol mechanism that
   guarantees it — `inv` *is* the protocol's written, machine-checked proof.

1b. **Resize evidence tier (stage 1a)** — for the resize machinery the
   current bar is *scenarios + simulator + base cases*, deliberately **below**
   the inductive bar (stage 1b lands consecution over the resize state;
   stage 1c the refinement/transfer-correctness theorem):
   - Simulator `[ok]` for `inv` AND `rsInv` (the daemon-state families
     R6–R12, wrapped in `system.qnt`) on `system_resize_1gen` at depths
     completing ≥1 full transfer cycle; the `system_resize_2gen` pair under
     `DLHT_VERIFY_2GEN=1` (must pass when enabled).
   - Base cases `[ok]` on both system configs (wired into verify.sh stage 4).
   - Twelve directed resize scenarios (`tests/scenarios_resize.qnt`): the
     sentinel cut from both sides (pre-sentinel Put carried / post-sentinel
     Put redirected), the delete window carried as absent + the straggler D8
     on a dead header, insert abandon-and-redirect in both orders
     (reserve+fill pre-OR, and the design-§8 fill-AFTER-OR where I4's
     unguarded write lands mid-transfer), LC relocation (commit + abort),
     the snapStateAgrees resurrection interleaving, cross-bin isolation
     post-resize, and — on the 2gen instance — the laggard double-walk and
     the holder double-relocation.
   **No consecution claims are made over the resize machinery yet**; the
   R-families are reachable-true tier.

2. **Step refinement against the atomic map** (`refinement.qnt` vs
   `types.qnt::deltaResult`). The abstraction function reads each key's visible
   value; each concrete step's witness must be reproducible by ≤ `refineBound`
   abstract moves. Checked two ways:
   - **Anchored** (`refinement_anchored_<cfg>`, via `refineIndInit`): from
     *every* `inv`-state — depth-independent. With (1), this covers every
     reachable step at these configs: the linearizability evidence.
   - **From-init bounded** (`refinement_<cfg>`): a cheaper sanity layer that
     also exercises `init`.

3. **Simulator layer**: random traces (`quint run`, depth ≥ 20, ≥ 10 000
   samples) check `typeOK` and `inv` on reachable states — the cheap
   "reachable direction" that guards against over-strengthening.

4. **Directed scenarios** (`tests/scenarios.qnt`): 32 hand-written interleavings
   (contention, delete-window, shadow hand-off, multi-key, LC5/LC7 CAS-failure
   cleanup, LC abort handoff / LC9-window overlap / D8 version-silent drift),
   17 of which also assert `inv` in their final state. Plus the 12 resize
   scenarios (`tests/scenarios_resize.qnt`, above). The former
   `tests/scenarios_2bin.qnt` is retired: A′'s gen-0 always has exactly one
   bin, so its cross-bin coverage re-landed post-resize (between gen-1's bins
   2/3, scenario `resize_cross_bin_isolated`) where it is strictly stronger.

## What is NOT proved

- **Memory model**: the spec is sequentially consistent. Fence placement, torn
  reads, and the seqlock's plain-load arguments live in `design.md` and are
  exercised empirically by the Porcupine linearizability tests (run **without**
  `-race` — see the repo's `tests/`).
- **Domain sizes**: ≤ 2 resizes (`maxGen ≤ 2`, 7 bins max), 2–3 slots per
  bin, ≤ 2 procs, ≤ 2 keys, 2 values. Bugs that need larger instances escape
  (standard small-scope hypothesis).
- **Resize, beyond the 1a tier**: the resize machinery is checked by
  scenarios + simulator + base cases only. Consecution (inductive `inv` over
  the composed system, `rsInv` anchor wiring) is stage 1b; anchored
  refinement over resize — the transfer-correctness theorem (`rsDone` is an
  abstract no-op) — is stage 1c. The Phase 0 inductive + anchored-refinement
  results continue to hold on the maxGen=0 configs, re-verified after the
  retyping.
- **Insert's keep-slot retry path**: on finalize failure, the Go implementation
  (`allocator/insert.go:102–153`, `retryWithSlot`) KEEPS its `Trying`
  reservation, re-scans under a fresh header `h2`, and re-finalizes with `h2`
  as the CAS expectation; the spec models unreserve-and-restart (I6 → I1)
  instead. This is a sound coarsening for linearizability — every keep-slot
  outcome maps to an unreserve+retry execution with identical abstract
  behavior — but the re-finalize-under-fresh-header edge itself is NOT
  machine-verified. Its correctness rests on the header's ABA-freedom:
  versions only grow, and the only version-silent header write (D8's AND)
  cannot recreate a prior bit pattern without intervening bumps. Modeling it
  (new PCs I7/I8 + anchor/`allPCs`/space-table growth + full re-verification)
  is a candidate next work item.
- **Liveness**: every check is safety; nothing is proved to terminate.

## Anchor completeness — the one thing to be paranoid about

Consecution is sound only if `indInit` ranges over **all** `inv`-states.
Under-coverage passes *silently* (a non-inductive `inv` would be reported as
verified). Three controls defend this:

1. **Int types are closed in `inv` itself** (e.g. `tagMonotonic` bounds tags to
   `[1, nextTag)`), so the anchor's `Int` codomains are provably complete.
2. The **per-variable space table** in `induction.qnt` documents each
   constructed space against its variable's declared type. *When you add a
   variable or a PC variant, update `indInit` + `allPCs` + the table in the same
   commit.*
3. **Negative controls** (recorded below) prove both the invariant wiring and
   the anchor breadth are load-bearing.

### Negative-control experiment

Two controls, run on `induction_1proc` (1-proc consecution, `--max-steps=1`),
prove the induction is neither vacuous nor anchor-blind. Both are temporary
edits, reverted afterward.

1. **Vacuity** — delete one load-bearing conjunct (`ownerSlotStateConsistent`)
   from `invPure`, keep the full anchor → consecution **`[violation]`** (the
   PcI4 fill step writes val/tag into an Invalid slot, breaking
   `invalidSlotClean`). Proves the conjunct is doing real work — the induction
   does not pass vacuously.

2. **Coverage** — keep that conjunct deleted *and* narrow the anchor by dropping
   the two fill PCs (`PcI4`, `PcLC4`) from `allPCs` → consecution **`[ok]` — a
   FALSE PASS.** The same non-inductive `inv` is now reported "verified" purely
   because the anchor can no longer construct the breaking state. This is the
   silent unsoundness the anchor-completeness controls defend against: an
   under-covered anchor turns a real counterexample invisible.

The minimal, self-contained version of control 2 lives in
`spec/probes/undercover.qnt`. Takeaway: when you add a variable or PC variant,
the anchor (`indInit` / `allPCs`) and its space-table comment MUST grow with it,
or coverage silently shrinks.

## Cost and tiers

Apalache consecution grows steeply with the config. `verify.sh` tiers it:

| Check | Wall time (observed) | Default |
|---|---|---|
| 1-proc consecution | ~1.5–9 min | always |
| 1-proc anchored refinement | ~5 min | always |
| 2-proc consecution | ~45 min – 2.8 h | `DLHT_VERIFY_2PROC=1` (default on) |
| 2-proc anchored refinement | ~21 min | `DLHT_VERIFY_2PROC=1` (default on) |
| 2-proc-2-key consecution | ~23 min (idle, 16 GB heap) | `DLHT_VERIFY_2KEY=1` (default **off**) |
| resize 1gen simulator (inv + rsInv, depth 40) | seconds–minutes | always |
| resize 2gen simulator pair | seconds–minutes | `DLHT_VERIFY_2GEN=1` (default **off**) |

The resize configs participate in the **simulator + scenario + base-case
tiers only** so far (the 1a bar); their consecution/refinement stages land
with 1b/1c.

Times vary widely with machine load (Apalache is SMT-bound; a 16 GB JVM heap is
set in `verify.sh` — an earlier 2-key attempt on a loaded machine with the
default 4 GB heap was still unfinished after ~1.5 h). The 2-proc consecution is
the dominant cost.

The 2-key check **must pass when enabled**; it is gated off by default only
because of its runtime. It was last run and **passed on 2026-06-11**
(`[ok]`, 1395626 ms ≈ 23 min, quint 0.32.0 / Apalache 0.56.1, 16 GB heap). Set
`DLHT_VERIFY_2PROC=0` for a fast (~few-minute) smoke that still runs 1-proc
induction, anchored refinement, the simulator, and all scenarios.

Full-suite wall time (observed, per stage, this machine):
- **Fast tier** (`DLHT_VERIFY_2PROC=0`): ~6–15 min (observed 372 s end-to-end)
  — typechecks + simulator + anchor smoke + 1-proc
  base/consecution/anchored/bounded + scenarios.
- **Default tier** (`DLHT_VERIFY_2PROC=1`): ~1.5–3 h, dominated by the 2-proc
  consecution (~45 min – 2.8 h alone) plus 2-proc anchored (~21 min).
- **Full assurance** (`DLHT_VERIFY_2KEY=1`): add the multi-hour 2-key
  consecution.

## A quint gotcha worth knowing

`quint test tests/scenarios.qnt` (a bare invocation) runs **zero** of the 32
scenarios: quint's default test selection only runs `run` definitions whose
*name* matches a "test" pattern, and the scenarios are descriptively named.
`verify.sh` uses `--match '_.*_'` (selects exactly the snake_case scenario runs,
excludes the single-underscore `unchanged_*` protocol actions) and asserts the
exact counts (`32 passing`, and `12 passing` for `tests/scenarios_resize.qnt`)
so coverage cannot silently shrink.

Two more, learned in stage 1a: Apalache requires **constant integer bounds**
in `a.to(b)` and does not constant-fold `ApaFoldSet` — hence `pow2` is a
closed-form if-chain, not a range fold. And the Rust evaluator resolves a
`nondet x = S.oneOf()` **against the action's guards** (it searches for a
satisfying choice), which is what makes the daemon's nondet bin picks usable
in directed `.then(...)` chains.

## Toolchain

- **quint 0.32.0** — installed from the GitHub release binary (npm lags at
  0.31.0); pinned by `verify.sh`'s version gate.
- **Apalache 0.56.1** — auto-managed by quint under `~/.quint/`.
- Two Apalache `quint verify` runs share one gRPC server and cancel each other —
  never run them concurrently. `quint test` / `quint typecheck` / `quint run`
  use the Rust evaluator and are safe to run anytime.

## Probes

`spec/probes/` holds the capability probes (P1, P1b, P2, P3, P4-export) and the
induction-semantics probes (`indsem`, `step0`, `vacuity`, `undercover`) that
validate the verification mechanisms themselves. Re-run them after any toolchain
bump.
