(** {1 Plugin for Nunchaku} *)

let __coq_plugin_name = "nunchaku_coq"

TACTIC EXTEND Nunchaku
  | ["nunchaku"] -> [Nunchaku_coq_run.call ()]
END;;
