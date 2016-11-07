(** {1 Plugin for Nunchaku} *)

DECLARE PLUGIN "nunchaku_coq";;

TACTIC EXTEND Nunchaku
  | ["nunchaku"] -> [Nunchaku_coq_run.call ()]
END;;
