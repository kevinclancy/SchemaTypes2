(* Port of Typecheck.fs *)

open Syntax
open Kindcheck

(** Build a [Char_set.t] containing every byte from [lo] through [hi]
    inclusive. *)
let char_range (lo : int) (hi : int) : Char_set.t =
  let rec loop i acc =
    if i > hi then acc else loop (i + 1) (Char_set.add (Char.chr i) acc)
  in
  loop lo Char_set.empty

(** All printable bytes (32..255). *)
let printable_chars : Char_set.t = char_range 32 255

(** All alphabetical ASCII characters (upper- and lower-case). *)
let alpha_chars : Char_set.t =
  Char_set.union (char_range 65 90) (char_range 97 122)

(** All decimal digits. *)
let num_chars : Char_set.t = char_range 48 57

(** Digits plus alphabetical ASCII characters. *)
let alpha_num_chars : Char_set.t = Char_set.union num_chars alpha_chars

let is_printable (c : char) : bool = Char_set.mem c printable_chars
let is_alpha (c : char) : bool = Char_set.mem c alpha_chars
let is_alpha_num (c : char) : bool = Char_set.mem c alpha_num_chars
let is_num (c : char) : bool = Char_set.mem c num_chars

(** Whether [s] parses as a floating-point number. *)
let is_numeric (s : string) : bool =
  match float_of_string_opt s with Some _ -> true | None -> false

(** Whether [s] is a non-empty string of decimal digits (i.e. a
    non-negative integer). *)
let is_pos_int (s : string) : bool =
  s <> "" && String.for_all is_num s

(** Split [s] on every occurrence of character [c]. *)
let split_on_char (c : char) (s : string) : string list =
  String.split_on_char c s

(** Whether [s] is a "DAT"-formatted timestamp: [<= 5 digits>] or
    [<= 5 digits>.<1 or 2 digits>]. *)
let is_dat (s : string) : bool =
  match split_on_char '.' s with
  | [ int_piece; dec_piece ] ->
    String.length int_piece <= 5
    && is_pos_int int_piece
    && (String.length dec_piece = 1 || String.length dec_piece = 2)
    && is_pos_int int_piece
  | [ int_piece ] ->
    String.length int_piece <= 5 && is_pos_int int_piece
  | _ -> false

(** Whether [s] looks like an M tag: [<tag>^<routine>], where each
    piece is alphanumeric (the tag may also start with [%]). *)
let is_tag (s : string) : bool =
  match split_on_char '^' s with
  | [ tag; rou ] ->
    if tag = "" || rou = "" then false
    else if tag.[0] = '%' then
      String.for_all is_alpha_num tag
      && String.for_all is_alpha_num
           (String.sub tag 1 (String.length tag - 1))
    else String.for_all is_alpha_num tag
  | _ -> false

(** Build a [Char_set.t] from an explicit list of characters. *)
let char_set_of_list (cs : char list) : Char_set.t =
  List.fold_left (fun acc c -> Char_set.add c acc) Char_set.empty cs

(** Construct a built-in type-alias entry from its description, an
    allowed-character set, an optional runtime predicate, and an M
    assertion. The discriminator is always [Prefix ""] and the body
    type is always absent (built-ins have no surface-syntax body). *)
let make_base_entry ~description ~allowed_chars ~fs_pred ~assertion :
    type_alias_entry =
  let str_ref =
    Some
      {
        discriminator = Prefix "";
        allowed_chars;
        fixed_length = None;
        fs_pred;
      }
  in
  let pk = { str_kind = str_ref; assertion = MBlock [ MLine assertion ] } in
  {
    kind = KProper (pk, Check.no_range);
    description;
    paths = [];
    ty = None;
  }

(** The base environment of built-in type aliases: [string], [nat],
    [alpha], [data], [num], [dat], [time], [instant], [tag]. *)
let base_alias_env : type_alias_env =
  let entries =
    [
      ( "string",
        make_base_entry ~description:"A string of printable characters."
          ~allowed_chars:alpha_chars
          ~fs_pred:(Some (fun x -> String.for_all is_printable x))
          ~assertion:{|d %zzAssert(x?.APN,"has 'string' type")|} );
      ( "nat",
        make_base_entry ~description:"A natural number."
          ~allowed_chars:num_chars
          ~fs_pred:(Some (fun x -> String.for_all is_num x))
          ~assertion:{|d %zzAssert(x?.N,"has 'nat' type")|} );
      ( "alpha",
        make_base_entry ~description:"A string of alphabetical characters."
          ~allowed_chars:alpha_chars
          ~fs_pred:(Some (fun x -> String.for_all is_alpha x))
          ~assertion:{|d %zzAssert(x?.A,"has 'alpha' type")|} );
      ( "data",
        make_base_entry
          ~description:
            "A string of characters (possibly including unprintable ones)"
          ~allowed_chars:all_chars
          ~fs_pred:(Some (fun _ -> true))
          ~assertion:{|d %zzAssert(1,"can't fail")|} );
      ( "num",
        make_base_entry ~description:"A number"
          ~allowed_chars:
            (char_set_of_list
               [ '0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9'; '+'; '-';
                 'e'; 'E'; '.' ])
          ~fs_pred:(Some is_numeric)
          ~assertion:{|d %zzAssert($$zIsNumeric(x),"has 'num' type")|} );
      ( "dat",
        make_base_entry
          ~description:
            "121531 minus the number of days since Dec 31, 1840. Used to sort from recent to old."
          ~allowed_chars:
            (char_set_of_list
               [ '0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9' ])
          ~fs_pred:(Some is_dat)
          ~assertion:
            {|d %zzAssert(x?1.N.1(1"."1.2N),"has 'dat' type")|} );
      ( "time",
        make_base_entry ~description:"Number of days since Dec 31, 1840"
          ~allowed_chars:
            (char_set_of_list
               [ '0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9' ])
          ~fs_pred:(Some is_pos_int)
          ~assertion:
            {|d %zzAssert((x?1.N)&(0<=x)&(x<=86400),"has 'time' type")|} );
      ( "instant",
        make_base_entry
          ~description:"Number of seconds since midnight, Dec 31, 1840"
          ~allowed_chars:
            (char_set_of_list
               [ '0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9' ])
          ~fs_pred:(Some is_pos_int)
          ~assertion:{|d %zzAssert(x?1.N,"has 'instant' type")|} );
      ( "tag",
        make_base_entry ~description:"The name of an M tag."
          ~allowed_chars:(Char_set.remove ';' printable_chars)
          ~fs_pred:(Some is_tag)
          ~assertion:
            {|d %zzAssert(x?1(1A,1"%").AN1"^"1(1A,1"%").AN,"has 'tag' type")|} );
    ]
  in
  List.fold_left
    (fun env (name, entry) -> String_map.add name entry env)
    String_map.empty entries

(** A type-environment entry for a global: its description and
    ascribed type. *)
type type_env_entry = {
  description : string;
  (** Human-readable description of the global. *)

  ty : ty;
  (** Type ascribed to the global. *)
}

(** Maps the names of globals to their [type_env_entry]. *)
type type_env = type_env_entry String_map.t

(** Combined context for type-checking: the kind-checking context and
    the type environment for globals. *)
type type_check_context = {
  kind_check_context : context;
  (** Kind-checking context (type aliases and type variables in scope). *)

  ty_env : type_env;
  (** Maps each global to its ascribed type and description. *)
}

(** Type-check a list of type definitions, threading the accumulated
    subscript paths and extending the kind-checking context's
    type-alias environment with each definition. *)
let rec type_check_defs (ctxt : type_check_context)
    (paths : subscript_path list) (defs : type_def list) :
    (subscript_path list * type_check_context) Check.t =
  let open Check in
  match defs with
  | { comment = desc; id; ty; rng } :: rest ->
    let k_check_ctxt = ctxt.kind_check_context in
    let* paths', kind =
      with_error
        {%string|Error in definition of %{id}.|}
        rng
        (k_synth_ty k_check_ctxt ty)
    in
    let entry =
      { kind; ty = Some ty; description = desc; paths = paths' }
    in
    let k_check_ctxt' =
      { k_check_ctxt with
        ty_alias_env = String_map.add id entry k_check_ctxt.ty_alias_env }
    in
    let ctxt' = { ctxt with kind_check_context = k_check_ctxt' } in
    type_check_defs ctxt' (paths' @ paths) rest
  | [] -> return (paths, ctxt)

(** Type-check a list of global type ascriptions. Each ascription's
    type is kind-checked against the (already-fully-built) alias
    environment, then the global is added to the type environment. *)
let rec type_check_ascriptions (ctxt : type_check_context)
    (defs : type_ascription list) : type_check_context Check.t =
  let open Check in
  let k_check_ctxt = ctxt.kind_check_context in
  match defs with
  | { comment = desc; id; ty; rng } :: rest ->
    let* _kind =
      with_error
        {%string|Error in ascription of %{id}.|}
        rng
        (k_synth_ty k_check_ctxt ty)
    in
    let entry = { description = desc; ty } in
    type_check_ascriptions
      { ctxt with ty_env = String_map.add id entry ctxt.ty_env }
      rest
  | [] -> return ctxt

(** Type-check a full program: first the type definitions, then the
    global type ascriptions. *)
let type_check (prog : prog) : type_check_context Check.t =
  let open Check in
  let defs, ascriptions = prog in
  let kind_check_context =
    { ty_alias_env = base_alias_env; ty_var_env = String_map.empty }
  in
  let* _paths, def_ctxt =
    type_check_defs
      { kind_check_context; ty_env = String_map.empty }
      [] defs
  in
  type_check_ascriptions def_ctxt ascriptions
