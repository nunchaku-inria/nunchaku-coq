
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

  let range ?(sep=", ") pp fmt n =
    let rec aux i =
      if i=n then ()
      else (
        if i > 0 then (
          Format.pp_print_string fmt sep;
          Format.pp_print_cut fmt ();
        );
        pp fmt i;
        aux (i+1)
      )
    in
    aux 0

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

  let ksprintf ~f fmt =
    let buf = Buffer.create 32 in
    let out = Format.formatter_of_buffer buf in
    Format.kfprintf
      (fun _ -> Format.pp_print_flush out (); f (Buffer.contents buf))
      out fmt

  let sprintf format =
    let buf = Buffer.create 64 in
    let fmt = Format.formatter_of_buffer buf in
    Format.kfprintf
      (fun _fmt -> Format.pp_print_flush fmt (); Buffer.contents buf)
      fmt
      format
end

let pp_term out csr =
  let open Term in
  let open Names in
  let open Format in
  let fpf = Format.fprintf in
  let rec term_display out c = match Term.kind_of_term c with
    | Rel n -> fpf out "#%d" n
    | Meta n -> fpf out "Meta(%d)" n
    | Var id -> Fmt.string out (Id.to_string id)
    | Sort s -> sort_display out s
    | Cast (c,_, t) ->
      fpf out "(@[<1>%a@ :: %a@])" term_display c term_display t
    | Prod (Name(id),t,c) ->
      fpf out "(@[<1>(%s: %a)@ %a@])" (Id.to_string id) box_display t box_display c
    | Prod (Anonymous,t,c) ->
      fpf out "(@[<1>%a@ -> %a@])" box_display t box_display c
    | Lambda (na,t,c) ->
      fpf out "[@[<2>%a:%a]@ %a@]]" name_display na box_display t box_display c
    | LetIn (na,b,t,c) ->
      fpf out "[@[<1>@[<2>%a@ = %a@:%a@]]@ %a"
        name_display na box_display b box_display t box_display c
    | App (c,l) -> fpf out "(@[<1>%a@ %a@])" box_display c (Fmt.array box_display) l
    | Evar _ -> Fmt.string out "Evar#"
    | Const (c,u) -> sp_con_display out c
    | Ind ((sp,i),u) -> fpf out "Ind(%a)" sp_display sp
    | Construct (((sp,i),j),u) ->
      fpf out "Constr(%a,%d,%d)" sp_display sp i j
    | Case (ci,p,c,bl) ->
      fpf out "@[<v2><%a>@ Case@ %a of@ %a@ end@])" box_display p box_display c
        (Fmt.array box_display) bl
    | Fix ((t,i),(lna,tl,bl)) ->
      let pp_i out i =
        fpf out "@[<v0>%a/%d@ : %a@ := %a@]@,"
          name_display lna.(i) t.(i) box_display tl.(i) box_display bl.(i)
      in
      fpf out "@[<v2>Fix(%d)@ {%a}@]" i (Fmt.range pp_i) (Array.length tl)
    | CoFix(i,(lna,tl,bl)) ->
      let pp_i out i =
        fpf out "@[<v0>%a@ : %a@ := %a@]@,"
          name_display lna.(i) box_display tl.(i) box_display bl.(i)
      in
      fpf out "@[<v2>CoFix(%d)@ {%a}@]" i (Fmt.range pp_i) (Array.length tl)
    | Proj (p, c) ->
      fpf out "Proj(@[%a,%a@])" sp_con_display (Projection.constant p) box_display c

  and box_display out c = Fmt.hovbox ~i:1 term_display out c

  and sort_display out = function
    | Prop(Pos) -> Fmt.string out"Set"
    | Prop(Null) -> Fmt.string out "Prop"
    | Type _u -> Fmt.string out "Type"

  and name_display out = function
    | Name id -> Fmt.string out (Id.to_string id)
    | Anonymous -> Fmt.string out "_"
  (* Remove the top names for library and Scratch to avoid long names *)
  and sp_display out sp =
    Fmt.string out (MutInd.debug_to_string sp)
  and sp_con_display out sp =
    Fmt.string out (Constant.debug_to_string sp)
  in
  term_display out csr

module Array = struct
  type 'a t = 'a array

  let for_all ~f a =
    let rec aux i =
      i = Array.length a || (f a.(i) && aux (i+1))
    in
    aux 0
end
