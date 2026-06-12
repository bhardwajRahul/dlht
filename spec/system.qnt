module system {
  import protocol.* from "./protocol"
  import invariants.* from "./invariants"
  import resize.* from "./resize"
  export protocol.*
  export invariants.*
  export resize.*

  // Every composed step must assign ALL vars: protocol steps frame the
  // daemon's bookkeeping; daemon actions already frame the protocol vars.
  action protocolStepFramed = all { step, unchanged_resize }

  action systemInit = all { init, resizeInit }
  action systemStep = any { protocolStepFramed, resizeStep }

  // Live wrapper for the resize-state families (their pure defs live in
  // invariants.qnt taking the daemon state as PARAMETERS — invariants.qnt
  // must NOT import resize, or induction.qnt's instance inherits unassigned
  // vars; see the wiring rule there). invPure/inv stay protocol-only: the
  // anchor guard is unchanged in 1a; folding the daemon state into the
  // anchor is a 1b decision.
  def rsInv = rsInvPure(currentSpecState, snapshot, cursor)
}
