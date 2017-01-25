
(* This file is free software, part of containers. See file "license" for more details. *)

(** {1 Simple S-expression parsing/printing} *)

type t = [
  | `Atom of string
  | `List of t list
  ]
type sexp = t

let equal a b = a = b

let compare a b = Pervasives.compare a b

let hash a = Hashtbl.hash a

let of_int x = `Atom (string_of_int x)
let of_float x = `Atom (string_of_float x)
let of_bool x = `Atom (string_of_bool x)
let atom x = `Atom x
let of_unit = `List []
let of_list l = `List l
let of_rev_list l = `List (List.rev l)
let of_pair (x,y) = `List[x;y]
let of_triple (x,y,z) = `List[x;y;z]
let of_quad (x,y,z,u) = `List[x;y;z;u]

let of_variant name args = `List (`Atom name :: args)
let of_field name t = `List [`Atom name; t]
let of_record l =
  `List (List.map (fun (n,x) -> of_field n x) l)

(** {2 Printing} *)

let _with_out filename f =
  let oc = open_out filename in
  try
    let x = f oc in
    close_out oc;
    x
  with e ->
    close_out oc;
    raise e

(* shall we escape the string because of one of its chars? *)
let _must_escape s =
  try
    for i = 0 to String.length s - 1 do
      let c = String.unsafe_get s i in
      match c with
      | ' ' | ')' | '(' | '"' | ';' | '\\' | '\n' | '\t' | '\r' -> raise Exit
      | _ when Char.code c > 127 -> raise Exit  (* non-ascii *)
      | _ -> ()
    done;
    false
  with Exit -> true

let rec to_buf b t = match t with
  | `Atom s when _must_escape s -> Printf.bprintf b "\"%s\"" (String.escaped s)
  | `Atom s -> Buffer.add_string b s
  | `List [] -> Buffer.add_string b "()"
  | `List [x] -> Printf.bprintf b "(%a)" to_buf x
  | `List l ->
      Buffer.add_char b '(';
      List.iteri
        (fun i t' -> (if i > 0 then Buffer.add_char b ' '; to_buf b t'))
        l;
      Buffer.add_char b ')'

let to_string t =
  let b = Buffer.create 128 in
  to_buf b t;
  Buffer.contents b

let rec pp fmt t = match t with
  | `Atom s when _must_escape s -> Format.fprintf fmt "\"%s\"" (String.escaped s)
  | `Atom s -> Format.pp_print_string fmt s
  | `List [] -> Format.pp_print_string fmt "()"
  | `List [x] -> Format.fprintf fmt "@[<hov2>(%a)@]" pp x
  | `List l ->
      Format.fprintf fmt "@[<hov1>(";
      List.iteri
        (fun i t' -> (if i > 0 then Format.fprintf fmt "@ "; pp fmt t'))
        l;
      Format.fprintf fmt ")@]"

let rec pp_noindent fmt t = match t with
  | `Atom s when _must_escape s -> Format.fprintf fmt "\"%s\"" (String.escaped s)
  | `Atom s -> Format.pp_print_string fmt s
  | `List [] -> Format.pp_print_string fmt "()"
  | `List [x] -> Format.fprintf fmt "(%a)" pp_noindent x
  | `List l ->
      Format.pp_print_char fmt '(';
      List.iteri
        (fun i t' -> (if i > 0 then Format.pp_print_char fmt ' '; pp_noindent fmt t'))
        l;
      Format.pp_print_char fmt ')'

let to_chan oc t =
  let fmt = Format.formatter_of_out_channel oc in
  pp fmt t;
  Format.pp_print_flush fmt ()

let to_file_seq filename seq =
  _with_out filename
    (fun oc ->
      seq (fun t -> to_chan oc t; output_char oc '\n')
    )

let to_file filename t = to_file_seq filename (fun k -> k t)

(** {2 Parsing} *)

let _with_in filename f =
  let ic = open_in filename in
  try
    let x = f ic in
    close_in ic;
    x
  with e ->
    close_in ic;
    raise e

(** A parser of ['a] can return [Yield x] when it parsed a value,
    or [Fail e] when a parse error was encountered, or
    [End] if the input was empty *)
type 'a parse_result =
  | Yield of 'a
  | Fail of string
  | End

module Decoder = struct
  module L = Nunchaku_coq_sexp_lex

  type t = {
    buf: Lexing.lexbuf;
    mutable cur_tok: L.token option; (* current token *)
  }

  let cur (t:t): L.token = match t.cur_tok with
    | Some L.EOI -> assert false
    | Some t -> t
    | None ->
      (* fetch token *)
      let tok = L.token t.buf in
      t.cur_tok <- Some tok;
      tok

  let junk t = t.cur_tok <- None

  let of_lexbuf buf = {
    buf;
    cur_tok=None;
  }

  exception E_end
  exception E_error of int * int * string

  let error_ lexbuf msg =
    let start = Lexing.lexeme_start_p lexbuf in
    let line = start.Lexing.pos_lnum in
    let col = start.Lexing.pos_cnum - start.Lexing.pos_bol in
    raise (E_error (line,col,msg))

  let next (t:t) =
    let rec expr () = match cur t with
      | L.EOI -> raise E_end
      | L.ATOM s -> junk t; `Atom s
      | L.LIST_OPEN ->
        junk t;
        let l = lst [] in
        begin match cur t with
          | L.LIST_CLOSE -> junk t; `List l
          | _ -> error_ t.buf "expected ')'"
        end
      | L.LIST_CLOSE -> error_ t.buf "expected expression"
    and lst acc = match cur t with
      | L.LIST_CLOSE -> List.rev acc
      | L.LIST_OPEN | L.ATOM _ ->
        let sub = expr () in
        lst (sub::acc)
      | L.EOI -> error_ t.buf "unexpected EOI"
    in
    try Yield (expr ())
    with
      | E_end -> End
      | E_error (line,col,msg)
      | Nunchaku_coq_sexp_lex.Error (line,col,msg) ->
        Fail (Printf.sprintf "parse error at %d:%d: %s" line col msg)
end

let fail_eof () = raise End_of_file
let fail_ s = failwith ("sexp parsing failed: " ^ s)

let parse_string s : (t,string) result =
  let buf = Lexing.from_string s in
  let d = Decoder.of_lexbuf buf in
  match Decoder.next d with
    | End -> Error "unexpected end of file"
    | Yield x -> Ok x
    | Fail s -> Error s
