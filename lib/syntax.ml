[@@@warning "-30"]

(** Set of characters, used for tracking allowed/banned character sets in
    string refinement types. *)
module Char_set = Set.Make (Char)

(** The universe of all characters: bytes 0..255 treated as [char]s. *)
let all_chars : Char_set.t =
  let rec loop i acc =
    if i > 255 then acc else loop (i + 1) (Char_set.add (Char.chr i) acc)
  in
  loop 0 Char_set.empty

(** Convert a character to a printable form for human-readable output
    (e.g. error messages). Non-printable bytes are shown as [<n>]. *)
let to_readable (c : char) : string =
  let n = Char.code c in
  if n < 32 || n > 126 then Printf.sprintf "<%d>" n
  else Printf.sprintf "'%c'" c

(** Convert a character to its M-language string form. Non-printable
    bytes become [$c(n)], printable ones become a quoted string. *)
let to_mstring (c : char) : string =
  let n = Char.code c in
  if n < 32 || n > 126 then Printf.sprintf "$c(%d)" n
  else Printf.sprintf "\"%c\"" c

(** A predicate deciding whether a string belongs to a string refinement
    type. Used as an escape hatch for refinements we can't describe
    structurally (prototype feature). *)
type string_pred = string -> bool

(** Information used to tell apart values belonging to different string
    refinement types — essentially a cheap-to-check witness that a
    string belongs to a particular refinement. *)
type discriminator =
  | Prefix of string
  (** All values of the type share this common prefix. The payload
      is the shared prefix string. *)

  | Literal of string
  (** The type contains exactly one known value. The payload is
      that value. *)

  | SomeLiteral
  (** The type contains exactly one value, but we do not know
      which one. *)

(** Check that discriminator [a] is a sub-discriminator of [b]: every
    string satisfying [a] must also satisfy [b]. Returns [Check.Result ()]
    on success or an error with [Check.no_range]. *)
let discriminator_sub (a : discriminator) (b : discriminator) : unit Check.t =
  match (a, b) with
  | Prefix prefix_a, Prefix prefix_b
    when String.length prefix_a >= String.length prefix_b
         && String.sub prefix_a 0 (String.length prefix_b) = prefix_b ->
    Check.Result ()
  | Literal literal_a, Prefix prefix_b
    when String.length literal_a >= String.length prefix_b
         && String.sub literal_a 0 (String.length prefix_b) = prefix_b ->
    Check.Result ()
  | Literal literal_a, Literal literal_b when literal_a = literal_b ->
    Check.Result ()
  | Literal _, SomeLiteral -> Check.Result ()
  | SomeLiteral, SomeLiteral -> Check.Result ()
  | _ -> Check.Error [ ("discriminator mismatch", Check.no_range) ]

(** Description of a string refinement type: the set of characters its
    strings may contain, a discriminator for membership, an optional
    fixed length, and an optional runtime predicate. *)
type str_ref_kind = {
  allowed_chars : Char_set.t;
      (** A superset of all characters that can appear in values of the type. *)
  discriminator : discriminator;
      (** Helps distinguish this type's values from those of other string types. *)
  fixed_length : int option;
      (** If every value of the type has the same length, holds that length. *)
  fs_pred : string_pred option;
      (** Prototype-specific: a function that decides membership.
          Ignored for equality and comparison since functions aren't
          comparable. *)
}

(** Structural equality on [str_ref_kind], excluding [fs_pred] since
    function values are not meaningfully comparable. *)
let str_ref_kind_equal (a : str_ref_kind) (b : str_ref_kind) : bool =
  Char_set.equal a.allowed_chars b.allowed_chars
  && a.discriminator = b.discriminator
  && a.fixed_length = b.fixed_length

(** Structural comparison on [str_ref_kind], excluding [fs_pred]. *)
let str_ref_kind_compare (a : str_ref_kind) (b : str_ref_kind) : int =
  let c = Char_set.compare a.allowed_chars b.allowed_chars in
  if c <> 0 then c
  else
    let c = compare a.discriminator b.discriminator in
    if c <> 0 then c else compare a.fixed_length b.fixed_length

(** The shared prefix of all strings of this refinement type, extracted
    from the discriminator. Literal and Prefix discriminators carry a
    real prefix; [SomeLiteral] has none. *)
let str_ref_kind_prefix (k : str_ref_kind) : string =
  match k.discriminator with
  | Prefix s -> s
  | Literal s -> s
  | SomeLiteral -> ""

(** Statements of the M assertion language, printed as indented lines. *)
type m_code =
  | MLine of string
  (** A single line of M code. *)

  | MBlock of m_code list
  (** A nested block of M code, rendered with extra indentation. *)

(** Render [m_code] to a string, indenting nested blocks. *)
let m_code_to_string (code : m_code) : string =
  let rec aux depth code =
    match code with
    | MLine s ->
      if depth = 0 then s
      else
        let dots = String.concat "" (List.init (depth - 1) (fun _ -> ". ")) in
        " " ^ dots ^ s
    | MBlock codes ->
      String.concat "\n" (List.map (aux (depth + 1)) codes)
  in
  aux 0 code

(** A "proper" kind — the kind of a well-formed type. Combines an
    optional string-refinement description with an M-language
    assertion about the values of the type. *)
type proper_kind = {
  str_kind : str_ref_kind option;
      (** If present, the type is a string refinement type and this
          describes its shape. If absent, the type is not a string type. *)
  assertion : m_code;
      (** Assertion about values of the type, in the M assertion language. *)
}

(** Superkind of all string kinds: any character, any prefix, no
    fixed length, no runtime predicate. *)
let proper_kind_string : proper_kind =
  {
    str_kind =
      Some
        {
          allowed_chars = all_chars;
          discriminator = Prefix "";
          fixed_length = None;
          fs_pred = None;
        };
    assertion = MLine "assertion unused";
  }

(** Superkind of all literal string kinds. *)
let proper_kind_some_literal : proper_kind =
  {
    str_kind =
      Some
        {
          allowed_chars = all_chars;
          discriminator = SomeLiteral;
          fixed_length = None;
          fs_pred = None;
        };
    assertion = MLine "assertion unused";
  }

(** Check that proper kind [a] is a sub-kind of [b]. String kinds must
    have a subset allowed-character set and a sub-discriminator; a
    non-string kind subsumes any string kind. *)
let proper_kind_sub (a : proper_kind) (b : proper_kind) : unit Check.t =
  match (a.str_kind, b.str_kind) with
  | Some { allowed_chars = chars_a; discriminator = d_a; _ },
    Some { allowed_chars = chars_b; discriminator = d_b; _ } ->
    let open Check in
    let* () =
      if Char_set.subset chars_a chars_b then Result ()
      else
        let diff = Char_set.diff chars_a chars_b in
        let min_c = Char_set.min_elt diff in
        Error
          [
            ( "Subkinding error: character " ^ to_readable min_c,
              Check.no_range );
          ]
    in
    discriminator_sub d_a d_b
  | Some _, None -> Check.Result ()
  | None, None -> Check.Result ()
  | None, Some _ -> Check.Error [ ("kind mismatch", Check.no_range) ]

(** The proper kind used for tree-shaped values, where the root location
    may hold any type (non-string). *)
let tree_kind : proper_kind =
  { str_kind = None; assertion = MLine "; loc may have any type" }

(** A kind: either the kind of a type, or the kind of a type operator. *)
type kind =
  | KProper of proper_kind * Check.range
  (** The kind of a type; carries refinement info and a source range. *)

  | KOperator of string * proper_kind * kind * Check.range
  (** The kind of a type operator. Fields are
      [(param_name, k_dom, k_cod, range)]: the bound parameter's
      name, its domain kind, the codomain kind, and the source
      range. *)

(** A surface-syntax kind (what the parser produces) — currently only
    the "Proper" form. *)
type syntax_kind =
  | Proper of Check.range
  (** The kind of a type (as opposed to a type operator). *)

(** A bound type-level parameter: its name, its kind, and the range of
    source it occurred in. *)
type ty_param = {
  id : string;  (** Identifier of the parameter. *)
  kind : proper_kind;  (** Kind of the parameter. *)
  rng : Check.range;  (** Source range of the parameter's occurrence. *)
}

(** How one field of a packed-string tuple is delimited from the next. *)
type delimiter =
  | Final
  (** The last field of a tuple — needs no delimiter. *)

  | Fixed of Check.range
  (** A fixed-width field — needs no delimiter; carries its source range. *)

  | LengthEncode of Check.range
  (** Field delimited by a 2-byte length prefix. *)

  | CharDelim of char * Check.range
  (** Field delimited by a specific character. *)


(** Render a [delimiter] to a short string for error messages. *)
let delimiter_to_string (d : delimiter) : string =
  match d with
  | Final -> "final"
  | Fixed _ -> "fixed"
  | LengthEncode _ -> "length"
  | CharDelim (c, _) -> to_readable c

(** Binary operators of the M assertion language. *)
type m_bin_op =
  | And
  (** Logical conjunction. *)

  | Or
  (** Logical disjunction. *)

  | Plus
  (** Integer/string addition. *)

  | Minus
  (** Integer subtraction. *)

  | Times
  (** Multiplication. *)

  | Mod
  (** Modulo. *)

  | Div
  (** Division. *)

  | IntDiv
  (** Integer division. *)

  | Eq
  (** Equality. *)

(** Render an [m_bin_op] to its surface-syntax symbol. *)
let m_bin_op_to_string (op : m_bin_op) : string =
  match op with
  | Eq -> "="
  | And -> "&"
  | Or -> "!"
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Mod -> "#"
  | Div -> "/"
  | IntDiv -> "\\"

(** Expressions of the M assertion language. *)
type m_expr =
  | BinOp of m_expr * m_bin_op * m_expr * Check.range
  (** A binary operator application: [left op right]. *)

  | FunCall of string * m_expr list * Check.range
  (** A function call: [name(args...)]. *)

  | Var of string * Check.range
  (** A variable reference. *)

  | Int of int32 * Check.range
  (** An integer literal. *)

  | StrLit of string * Check.range
  (** A string literal. *)

(** Render an [m_expr] to its surface syntax. *)
let rec m_expr_to_string (e : m_expr) : string =
  match e with
  | BinOp (l, op, r, _) ->
    "(" ^ m_expr_to_string l ^ m_bin_op_to_string op ^ m_expr_to_string r ^ ")"
  | FunCall (name, args, _) ->
    name ^ "(" ^ String.concat "," (List.map m_expr_to_string args) ^ ")"
  | Var (name, _) -> name
  | Int (v, _) -> Int32.to_string v
  | StrLit (v, _) -> "\"" ^ v ^ "\""

(** One field of a packed-string tuple type. *)
type tuple_field = {
  comment : string;  (** Human-readable description of the field. *)
  name : string;  (** The field's identifier. *)
  ty : ty;  (** The field's type. *)
  delim : delimiter option;  (** The field's delimiter, if any. *)
  rng : Check.range;  (** Source range of the field. *)
}

(** One field of an object (TypeScript-style) type. *)
and obj_ty_field = {
  description : string;  (** Human-readable description of the field. *)
  key_id : string option;  (** Identifier bound to the key, if any. *)
  key_ty : ty;  (** Type of the field's key. *)
  val_id : string option;  (** Identifier bound to the value, if any. *)
  val_ty : ty;  (** Type of the field's value. *)
  non_empty : bool;
      (** Whether this field must contain at least one key-value pair. *)
  rng : Check.range;  (** Source range of the field. *)
}

(** The special "root" field of an object type: the data stored at the
    object's root location. *)
and obj_ty_root = {
  description : string;  (** Human-readable description of the root field. *)
  val_ty : ty;
      (** Type (typically a string refinement type) of data at the root. *)
  rng : Check.range;  (** Source range of the root field. *)
}

(** Identifies a subscript inside a hierarchical array: the global the
    path starts from, the chain of subscript types leading to the
    point of interest, and the type of the subscript of interest. *)
and subscript_path = {
  global_name : string;  (** Name of the global at the root of the path. *)
  subscripts : ty list;
      (** Chain of subscripts on the way to the subscript of interest. *)
  ty : ty;  (** Type (a string type) of the subscript of interest. *)
}

(** The AST of types in the schema language. *)
and ty =
  | TyVec of ty * Check.range
  (** A 1-based array where the length is stored at index 0.
      Payload: element type and source range. *)

  | TyDelimList of ty * delimiter * Check.range
  (** A list whose elements are of string type, delimited by the
      given delimiter. Payload: element type, delimiter, source
      range. *)

  | TyObj of obj_ty_root option * obj_ty_field list * Check.range
  (** TypeScript's object type. Payload: the optional special root
      field, the ordinary fields, and the source range. *)

  | TyTuple of delimiter option * tuple_field list * Check.range
  (** A packed string tuple. Payload: an optional universal
      delimiter applied to every field, the list of fields, and
      the source range. *)

  | TyStrLiteral of string * Check.range
  (** A string literal type: the type containing only the given string. *)

  | TyUnion of ty list * Check.range
  (** A prefix-discriminated union of types. *)

  | TyBitStr of int * Check.range
  (** The type of length-[n] bit strings. *)

  | TyName of string * Check.range
  (** An identifier referring to a type alias or type variable. *)

  | TySubscriptPath of subscript_path * Check.range
  (** The type of all subscripts directly under a given path with
      the given key type. *)

  | TyApp of ty * ty * Check.range
  (** A type-operator application: [ty_op ty_arg]. *)

  | TyForall of string * kind * ty * Check.range
  (** A type abstraction: [(param : kind) => body]. *)

  | TyRef of ty * m_expr * Check.range
  (** A refinement type: values of the base type satisfying the
      given M-language refinement. *)

  | TyWithout of ty * Char_set.t * Check.range
  (** A "without" type: the base type excluding strings containing
      any character in the ban set. *)

(** Substitute [a] for the free type variable [x] inside [b]. *)
let rec ty_subst (a : ty) (x : string) (b : ty) : ty =
  match b with
  | TyVec (elem_ty, rng) -> TyVec (ty_subst a x elem_ty, rng)
  | TyDelimList (elem_ty, delim, rng) ->
    TyDelimList (ty_subst a x elem_ty, delim, rng)
  | TyObj (opt_root, other_fields, rng) ->
    let opt_root' =
      Option.map
        (fun (root : obj_ty_root) ->
          { root with val_ty = ty_subst a x root.val_ty })
        opt_root
    in
    let subst_field (field : obj_ty_field) =
      {
        field with
        key_ty = ty_subst a x field.key_ty;
        val_ty = ty_subst a x field.val_ty;
      }
    in
    TyObj (opt_root', List.map subst_field other_fields, rng)
  | TyTuple (universal_delim, fields, rng) ->
    let subst_field (field : tuple_field) =
      { field with ty = ty_subst a x field.ty }
    in
    TyTuple (universal_delim, List.map subst_field fields, rng)
  | TyStrLiteral (s, rng) -> TyStrLiteral (s, rng)
  | TyUnion (components, rng) ->
    TyUnion (List.map (ty_subst a x) components, rng)
  | TyBitStr (n, rng) -> TyBitStr (n, rng)
  | TyName (name, _) when name = x -> a
  | TyName (name, rng) -> TyName (name, rng)
  | TySubscriptPath (path, rng) ->
    let path' =
      {
        path with
        subscripts = List.map (ty_subst a x) path.subscripts;
        ty = ty_subst a x path.ty;
      }
    in
    TySubscriptPath (path', rng)
  | TyApp (ty_op, ty_arg, rng) ->
    TyApp (ty_subst a x ty_op, ty_subst a x ty_arg, rng)
  | TyForall (param, kind, body, rng) when param = x ->
    TyForall (param, kind, body, rng)
  | TyForall (param, kind, body, rng) ->
    TyForall (param, kind, ty_subst a x body, rng)
  | TyRef (base_ty, refinement, rng) ->
    (* todo: substitute string literals into refinement *)
    TyRef (ty_subst a x base_ty, refinement, rng)
  | TyWithout (base_ty, ban_set, rng) ->
    TyWithout (ty_subst a x base_ty, ban_set, rng)

(** Render a type to a short surface-syntax-like string. *)
let rec ty_to_string (t : ty) : string =
  match t with
  | TySubscriptPath ({ global_name; subscripts; ty = key_ty }, _) ->
    let path_strings = List.map ty_to_string subscripts in
    global_name ^ "(" ^ String.concat "," path_strings ^ ").["
    ^ ty_to_string key_ty ^ "]"
  | TyVec (elem_ty, _) -> "vec " ^ ty_to_string elem_ty
  | TyDelimList (elem_ty, delim, _) ->
    "list " ^ ty_to_string elem_ty ^ " " ^ delimiter_to_string delim
  | TyObj _ -> "{ ... }"
  | TyUnion (components, _) ->
    String.concat " | " (List.map ty_to_string components)
  | TyStrLiteral (s, _) -> "\"" ^ s ^ "\""
  | TyTuple _ -> "tuple { ... }"
  | TyBitStr (n, _) -> "BitString(" ^ string_of_int n ^ ")"
  | TyName (name, _) -> name
  | TyApp (ty_op, ty_arg, _) ->
    "(" ^ ty_to_string ty_op ^ " " ^ ty_to_string ty_arg ^ ")"
  | TyForall (param, _, body, _) ->
    "(" ^ param ^ " : <kind>) => " ^ ty_to_string body
  | TyRef (base_ty, refinement, _) ->
    "{| " ^ ty_to_string base_ty ^ " : " ^ m_expr_to_string refinement ^ "|}"
  | TyWithout (base_ty, _, _) -> "(" ^ ty_to_string base_ty ^ " without ...)"

(** Extract the source range of a type. *)
let ty_range (t : ty) : Check.range =
  match t with
  | TySubscriptPath (_, rng)
  | TyVec (_, rng)
  | TyDelimList (_, _, rng)
  | TyObj (_, _, rng)
  | TyTuple (_, _, rng)
  | TyStrLiteral (_, rng)
  | TyUnion (_, rng)
  | TyBitStr (_, rng)
  | TyName (_, rng)
  | TyApp (_, _, rng)
  | TyForall (_, _, _, rng)
  | TyRef (_, _, rng)
  | TyWithout (_, _, rng) ->
    rng

(** Build an object type field representing a multi-key dictionary,
    desugaring [stringTy_1, ..., stringTy_n] : valTy into nested
    single-key objects. *)
let make_multi_key_dict (description : string)
    (key_id_types : (string option * ty) list) (val_id : string option)
    (val_ty : ty) (rng : Check.range) : obj_ty_field =
  let rec aux description key_id_types rng =
    match key_id_types with
    | (head_id, head_ty) :: rest ->
      let id, inner = aux description rest rng in
      ( None,
        TyObj
          ( None,
            [
              {
                description;
                key_id = head_id;
                key_ty = head_ty;
                val_id = id;
                val_ty = inner;
                non_empty = false;
                rng;
              };
            ],
            rng ) )
    | [] -> (val_id, val_ty)
  in
  match key_id_types with
  | [] -> failwith "make_multi_key_dict: empty key list"
  | (head_id, head_ty) :: tail ->
    let res_val_id, res_val_ty = aux description tail rng in
    {
      description;
      key_id = head_id;
      key_ty = head_ty;
      val_id = res_val_id;
      val_ty = res_val_ty;
      non_empty = false;
      rng;
    }

(** A top-level type definition: an identifier bound to a type. *)
type type_def = {
  comment : string;  (** Human-readable description of the type. *)
  id : string;  (** Identifier the type is bound to. *)
  ty : ty;  (** The type being defined. *)
  rng : Check.range;  (** Source range of the definition. *)
}

(** A global's type ascription: "global [id] has type [ty]". *)
type type_ascription = {
  comment : string;  (** Human-readable description of the global. *)
  id : string;  (** Name of the global. *)
  ty : ty;  (** Type ascribed to the global. *)
  rng : Check.range;  (** Source range of the ascription. *)
}

(** A full program: a list of type definitions followed by a list of
    global type ascriptions. *)
type prog = type_def list * type_ascription list

(** The default root field used when an object type has no explicit
    "root" field supplied. *)
let default_root : obj_ty_root =
  {
    description = "";
    val_ty = TyName ("data", Check.no_range);
    rng = Check.no_range;
  }

(** Build an object type from a list of fields. If the first field's
    key type is the literal ["root"], promote it to the special root
    position. *)
let make_obj_ty (fields : obj_ty_field list) (rng : Check.range) : ty =
  match fields with
  | ({ key_ty = TyStrLiteral ("root", _); _ } as first) :: rest ->
    let root_field =
      {
        description = first.description;
        val_ty = first.val_ty;
        rng = first.rng;
      }
    in
    TyObj (Some root_field, rest, rng)
  | all -> TyObj (None, all, rng)

(** How a type query ended — with a closing paren (closed) or a trailing
    comma (open). *)
type query_style =
  | ClosedQuery of int option
  (** A closed query (input ended with [)]). The payload is [Some n]
      if the user wrote [@n] at the end to pick the nth tuple
      field. *)

  | OpenQuery
  (** An open query (input ended with [,]). *)

(** A user query about the type at a subscripted location. *)
type type_query = {
  global_name : string;  (** Name of the global being queried. *)
  subscripts : string list;
      (** Sequence of subscripts leading to the queried location. *)
  style : query_style;
      (** Whether the query was open or closed, plus any tuple-field index. *)
}
