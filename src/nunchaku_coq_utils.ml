
(** {2 Helpers for Format} *)

module Fmt = struct
  type t = Format.formatter
  type 'a printer = t -> 'a -> unit

  let silent _fmt _ = ()

  let unit fmt () = Format.pp_print_string fmt "()"
  let int fmt i = Format.pp_print_string fmt (string_of_int i)
  let string = Format.pp_print_string
  let bool = Format.pp_print_bool
  let float3 fmt f = Format.fprintf fmt "%.3f" f
  let float fmt f = Format.pp_print_string fmt (string_of_float f)

  let char = Format.pp_print_char
  let int32 fmt n = Format.fprintf fmt "%ld" n
  let int64 fmt n = Format.fprintf fmt "%Ld" n
  let nativeint fmt n = Format.fprintf fmt "%nd" n
  let string_quoted fmt s = Format.fprintf fmt "\"%s\"" s

  let list ?(start="") ?(stop="") ?(sep=", ") pp fmt l =
    let rec pp_list l = match l with
      | x::((_::_) as l) ->
        pp fmt x;
        Format.pp_print_string fmt sep;
        Format.pp_print_cut fmt ();
        pp_list l
      | x::[] -> pp fmt x
      | [] -> ()
    in
    Format.pp_print_string fmt start;
    pp_list l;
    Format.pp_print_string fmt stop

  let array ?(start="") ?(stop="") ?(sep=", ") pp fmt a =
    Format.pp_print_string fmt start;
    for i = 0 to Array.length a - 1 do
      if i > 0 then (
        Format.pp_print_string fmt sep;
        Format.pp_print_cut fmt ();
      );
      pp fmt a.(i)
    done;
    Format.pp_print_string fmt stop

  let arrayi ?(start="") ?(stop="") ?(sep=", ") pp fmt a =
    Format.pp_print_string fmt start;
    for i = 0 to Array.length a - 1 do
      if i > 0 then (
        Format.pp_print_string fmt sep;
        Format.pp_print_cut fmt ();
      );
      pp fmt (i, a.(i))
    done;
    Format.pp_print_string fmt stop

  let option pp fmt x = match x with
    | None -> Format.pp_print_string fmt "none"
    | Some x -> Format.fprintf fmt "some %a" pp x

  let pair ?(sep=", ") ppa ppb fmt (a, b) =
    Format.fprintf fmt "(%a%s@,%a)" ppa a sep ppb b

  let triple ?(sep=", ") ppa ppb ppc fmt (a, b, c) =
    Format.fprintf fmt "(%a%s@,%a%s@,%a)" ppa a sep ppb b sep ppc c

  let quad ?(sep=", ") ppa ppb ppc ppd fmt (a, b, c, d) =
    Format.fprintf fmt "(%a%s@,%a%s@,%a%s@,%a)" ppa a sep ppb b sep ppc c sep ppd d

  let within a b p out x =
    string out a;
    p out x;
    string out b

  let map f pp fmt x =
    pp fmt (f x);
    ()

  let vbox ?(i=0) pp out x =
    Format.pp_open_vbox out i;
    pp out x;
    Format.pp_close_box out ()

  let hovbox ?(i=0) pp out x =
    Format.pp_open_hovbox out i;
    pp out x;
    Format.pp_close_box out ()

  let hvbox ?(i=0) pp out x =
    Format.pp_open_hvbox out i;
    pp out x;
    Format.pp_close_box out ()

  let hbox pp out x =
    Format.pp_open_hbox out ();
    pp out x;
    Format.pp_close_box out ()
end
