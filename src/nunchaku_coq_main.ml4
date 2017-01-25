(** {1 Plugin for Nunchaku} *)

DECLARE PLUGIN "nunchaku_coq";;

TACTIC EXTEND nunchaku1
  | ["nunchaku"] -> [Nunchaku_coq_run.call ~mode:Nunchaku_coq_run.M_fail ()]
END;;

TACTIC EXTEND nunchaku2
  | ["nunchaku" "warn"] -> [Nunchaku_coq_run.call ~mode:Nunchaku_coq_run.M_warn ()]
END;;
