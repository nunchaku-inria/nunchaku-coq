
(** {2 Helpers for Format} *)

module Fmt : sig
  type t = Format.formatter
  type 'a printer = t -> 'a -> unit

  val silent : 'a printer (** Prints nothing *)

  val unit : unit printer
  val int : int printer
  val string : string printer
  val bool : bool printer
  val float : float printer

  val char : char printer
  val int32 : int32 printer
  val int64 : int64 printer
  val nativeint : nativeint printer

  val string_quoted : string printer

  val list : ?start:string -> ?stop:string -> ?sep:string -> 'a printer -> 'a list printer
  val array : ?start:string -> ?stop:string -> ?sep:string -> 'a printer -> 'a array printer
  val arrayi : ?start:string -> ?stop:string -> ?sep:string ->
    (int * 'a) printer -> 'a array printer

  val range : ?sep:string -> int printer -> int printer
  (** [range pp n] prints the list [pp 0, pp 1, ... , pp (n-1)] *)

  val option : 'a printer -> 'a option printer

  val pair : ?sep:string -> 'a printer -> 'b printer -> ('a * 'b) printer
  val triple : ?sep:string -> 'a printer -> 'b printer -> 'c printer -> ('a * 'b * 'c) printer
  val quad : ?sep:string -> 'a printer -> 'b printer ->
    'c printer -> 'd printer -> ('a * 'b * 'c * 'd) printer

  val within : string -> string -> 'a printer -> 'a printer

  val map : ('a -> 'b) -> 'b printer -> 'a printer

  val vbox : ?i:int -> 'a printer -> 'a printer
  val hvbox : ?i:int -> 'a printer -> 'a printer
  val hovbox : ?i:int -> 'a printer -> 'a printer
  val hbox : 'a printer -> 'a printer
  val sprintf : ('a, t, unit, string) format4 -> 'a
  val ksprintf :
    f:(string -> 'b) ->
    ('a, Format.formatter, unit, 'b) format4 ->
    'a
end

val pp_term : Term.constr Fmt.printer

module Array : sig
  type 'a t = 'a array
  val for_all : f:('a -> bool) -> 'a t -> bool
end

val finally : h:(unit -> unit) -> (unit -> 'a) -> 'a
(** [finally ~h f] behaves like [f()], but calls [h()] before returning
    whatever happens *)

module Process : sig
  type status = int

  val popen : string -> f:(out_channel * in_channel -> 'a) -> 'a * status
  (** [popen cmd ~f] starts a subprocess executing [cmd], and calls
      [f] with the [(stdin,stdout)] of the sub-process. *)
end
