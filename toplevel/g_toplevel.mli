
type vernac_toplevel =
    VernacBackTo of int
  | VernacDrop
  | VernacQuit
  | VernacControl of Vernacexpr.vernac_control
  | VernacShowGoalAt of { gid : int; sid : int; }
  | VernacShowGoal of Vernacexpr.goal_reference
  | VernacShowProofDiffs of Proof_diffs.diffOpt

val test_show_goal : unit Procq.Entry.t

val vernac_toplevel :
  Pvernac.proof_mode option -> vernac_toplevel option Procq.Entry.t
