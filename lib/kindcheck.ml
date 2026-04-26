(* Port of Kindcheck.fs *)

open Syntax

(** A single newline, bound so that interpolation strings can embed
    line breaks without the source-code string literals themselves
    containing raw newlines. *)
let nl = "\n"

(** Maps ascribed global names to a (path, prefix) pair. *)
type ascription_env = (ty list * string) String_map.t

(** A single entry in the type-alias environment. Describes a type
    alias: its kind, the subscript paths it depends on, its body (for
    non-built-in aliases), and a human-readable description. *)
type type_alias_entry = {
  kind : kind;
  (** The kind of the type. *)

  paths : subscript_path list;
  (** Subscript paths the type depends on (its "path coeffect"). *)

  ty : ty option;
  (** The type's body, or [None] if this is a built-in type. *)

  description : string;
  (** Human-readable description of the type. *)
}

(** Maps the name of a type to its [type_alias_entry]. *)
type type_alias_env = type_alias_entry String_map.t

(** An entry for a type variable in the type-variable environment —
    currently just its kind. *)
type type_var_entry = {
  kind : kind;
  (** Kind of the type variable. *)
}

(** Maps a type variable's name to its [type_var_entry]. *)
type type_var_env = type_var_entry String_map.t

(** The kind-checking context: a type-alias environment and a
    type-variable environment. *)
type context = {
  ty_alias_env : type_alias_env;
  (** Environment of type aliases in scope. *)

  ty_var_env : type_var_env;
  (** Environment of type variables in scope. *)
}

(** Head-normalize a type: unfold named aliases and beta-reduce
    type-operator applications at the head position. *)
let rec ty_normalize (ctxt : context) (t : ty) : ty =
  match t with
  | TyName (name, _) ->
    (match String_map.find_opt name ctxt.ty_alias_env with
     | Some { ty = Some body; _ } -> ty_normalize ctxt body
     | _ -> t)
  | TyApp (TyForall (x, _, ty_body, _), ty_arg, _) ->
    ty_subst ty_arg x ty_body
  | TyApp (ty_op, ty_arg, rng) ->
    (match ty_normalize ctxt ty_op with
     | TyForall (x, _, ty_body, _) -> ty_subst ty_arg x ty_body
     | _ -> TyApp (ty_op, ty_arg, rng))
  | _ -> t

(** Unfold a named type alias one step, if possible. *)
let ty_unfold (ctxt : context) (t : ty) : ty option =
  match t with
  | TyName (name, _) ->
    (match String_map.find_opt name ctxt.ty_alias_env with
     | Some { ty = Some body; _ } -> Some body
     | _ -> None)
  | _ -> None

(** Render a type to a long, multi-line, human-readable string,
    expanding object and tuple types and unfolding named aliases. *)
let rec ty_to_long_string (ctxt : context) (t : ty) : string =
  match t with
  | TyVec (elem_ty, _) -> {%string|vec %{ty_to_string elem_ty}|}
  | TyDelimList (elem_ty, delim, _) ->
    {%string|list %{ty_to_string elem_ty} %{delimiter_to_string delim}|}
  | TyObj (opt_root, fields, _) ->
    let root_str =
      match opt_root with
      | None -> ""
      | Some root ->
        {%string|  // %{root.description}%{nl}  root : %{ty_to_string root.val_ty},%{nl}|}
    in
    let fold_field_str (acc : string) (field : obj_ty_field) : string =
      let key_str =
        match field.key_ty with
        | TyStrLiteral (name, _) -> name
        | _ -> {%string|[%{ty_to_string field.key_ty}]|}
      in
      acc
      ^ {%string|  // %{field.description}%{nl}  %{key_str} : %{ty_to_string field.val_ty},%{nl}|}
    in
    let fields_str = List.fold_left fold_field_str "" fields in
    {%string|{%{nl}%{root_str}%{fields_str}}|}
  | TyUnion (components, _) ->
    String.concat " | " (List.map ty_to_string components)
  | TyStrLiteral (str, _) -> {%string|"%{str}"|}
  | TyTuple (univ_delim, fields, _) ->
    let field_to_str (field : tuple_field) : string =
      let comment =
        if field.comment = "" then ""
        else {%string|// %{field.comment}%{nl}|}
      in
      match field.delim with
      | Some d ->
        {%string|%{comment}%{field.name} : %{ty_to_string field.ty} : %{delimiter_to_string d}|}
      | None ->
        {%string|%{comment}%{field.name} : %{ty_to_string field.ty}|}
    in
    let fields_str = String.concat ",\n" (List.map field_to_str fields) in
    (match univ_delim with
     | Some d ->
       {%string|tuple %{delimiter_to_string d} {%{nl}%{fields_str}%{nl}}|}
     | None -> {%string|tuple {%{nl}%{fields_str}%{nl}}|})
  | TyBitStr (n, _) -> {%string|BitString(%{n#Int})|}
  | TyName (name, _) ->
    (match ty_unfold ctxt t with
     | Some body -> {%string|%{name}%{nl}%{ty_to_long_string ctxt body}|}
     | None -> name)
  | TyApp (ty_op, ty_arg, _) ->
    {%string|(%{ty_to_string ty_op} %{ty_to_string ty_arg})|}
  | TyForall (param_name, _, body_ty, _) ->
    {%string|(%{param_name} : <kind>) => %{ty_to_string body_ty}|}
  | TySubscriptPath _ | TyRef _ | TyWithout _ -> ty_to_string t

(** Characters that can appear in a delimiter. [Final] and [Fixed]
    contribute no characters; [LengthEncode] contributes every
    character; [CharDelim] contributes just its character. *)
let get_delim_chars (delim : delimiter) : Char_set.t =
  match delim with
  | Final | Fixed _ -> Char_set.empty
  | LengthEncode _ -> all_chars
  | CharDelim (c, _) -> Char_set.singleton c

(** Extract the character payload of a [CharDelim] delimiter; other
    delimiter shapes are unsupported here. *)
let get_delim_str (delim : delimiter) : string =
  match delim with
  | CharDelim (c, _) -> String.make 1 c
  | _ -> failwith "unsupported"

(** Returns code asserting a field given its delimiter and an
    assertion for its body.

    [assert_piece] assumes [Var "x"] holds the piece and ensures its
    value conforms to the piece type.

    The returned code assumes [Var "x"] is a string containing the
    piece starting at [Var "pos"], ensures the piece conforms to its
    type, advances [Var "pos"] to the first position of the next
    piece, and binds [name] (if provided) to the piece's value. *)
let assert_delim_piece (name : string option) (assert_piece : m_code)
    (delim : delimiter) : m_code =
  let name_prefix =
    match name with Some n -> {%string|s %{n}=x |} | None -> ""
  in
  match delim with
  | CharDelim (c, _) ->
    MBlock
      [
        MLine {%string|%{name_prefix}n nextPos,y|};
        MLine {%string|s nextPos=$f(x,%{to_mstring c},pos)|};
        MLine
          "s y=x,x=$s(nextPos'=0:$e(x,pos,nextPos-2),1:$$zStrExtractToEnd(x,pos)) d  s x=y";
        assert_piece;
        MLine "s pos=nextPos";
      ]
  | LengthEncode _ -> failwith "unimplemented"
  | Fixed _ -> failwith "unimplemented"
  | Final ->
    MBlock
      [
        MLine {%string|%{name_prefix}n y|};
        MLine "s y=x,x=$$zStrExtractToEnd(x,pos) d  s x=y";
        assert_piece;
        MLine "s pos=0";
      ]

(** Check that [(s, kind_of_s)] and [(t, kind_of_t)] describe disjoint
    string types, based on their discriminators. Prefixes must not
    overlap, a prefix must not prefix a literal, literals must differ,
    and unknown-literal discriminators cannot be proven disjoint. *)
let check_discrim ((s, kind_of_s) : ty * str_ref_kind)
    ((t, kind_of_t) : ty * str_ref_kind) : unit Check.t =
  let starts_with (s : string) (p : string) : bool =
    String.length s >= String.length p
    && String.sub s 0 (String.length p) = p
  in
  let s_str = ty_to_string s in
  let t_str = ty_to_string t in
  match (kind_of_s.discriminator, kind_of_t.discriminator) with
  | Prefix prefix_s, Prefix prefix_t
    when starts_with prefix_s prefix_t || starts_with prefix_t prefix_s ->
    Check.Error
      [
        ( {%string|Prefix '%{prefix_s}' of type %{s_str} overlaps prefix '%{prefix_t}' of type %{t_str}.|},
          ty_range s );
      ]
  | Prefix _, Prefix _ -> Check.Result ()
  | Prefix prefix_s, Literal lit_t when starts_with lit_t prefix_s ->
    Check.Error
      [
        ( {%string|Prefix '%{prefix_s}' of type %{s_str} is a prefix of type '%{lit_t}'.|},
          ty_range s );
      ]
  | Prefix _, Literal _ -> Check.Result ()
  | Literal lit_s, Prefix prefix_t when starts_with lit_s prefix_t ->
    Check.Error
      [
        ( {%string|Prefix '%{prefix_t}' of type %{t_str} is a prefix of type '%{lit_s}'.|},
          ty_range s );
      ]
  | Literal _, Prefix _ -> Check.Result ()
  | Literal lit_s, Literal lit_t when lit_s = lit_t ->
    Check.Error
      [
        ( {%string|The type %{s_str} is equal to the type %{t_str}.|},
          ty_range s );
      ]
  | Literal _, Literal _ -> Check.Result ()
  | SomeLiteral, _ ->
    Check.Error
      [
        ( {%string|Unknown literals such as %{s_str} can't be proven disjoint frome any type.|},
          ty_range s );
      ]
  | _, SomeLiteral ->
    Check.Error
      [
        ( {%string|Unknown literals such as %{t_str} can't be proven disjoint frome any type.|},
          ty_range t );
      ]

(** Check that a type has fixed width. Currently only bit-strings and
    string literals qualify. *)
let k_check_fixed (t : ty) : unit Check.t =
  match t with
  | TyBitStr _ | TyStrLiteral _ -> Check.Result ()
  | _ ->
    Check.Error
      [
        ( {%string|Type %{ty_to_string t} does not have fixed width|},
          Check.no_range );
      ]

(** [k_check_field ctxt opt_univ_delim field is_final] kind-checks a
    tuple field. Returns the field's subscript paths, string-refinement
    kind, and generated M assertion code.

    [opt_univ_delim] is an optional tuple-universal delimiter applied
    to every field; [is_final] indicates whether this is the final
    field in the tuple. *)
let rec k_check_field (ctxt : context) (opt_univ_delim : delimiter option)
    (field : tuple_field) (is_final : bool) :
    (subscript_path list * str_ref_kind * m_code) Check.t =
  let open Check in
  let* paths, body_ref_kind, body_assertion = k_check_str_ty ctxt field.ty in
  let* delim =
    match (field.delim, opt_univ_delim) with
    | Some d, Some univ ->
      let d_str = delimiter_to_string d in
      let u_str = delimiter_to_string univ in
      Error
        [
          ( {%string|Providing both a field-specific delimiter %{d_str} and a tuple-level delimiter %{u_str} is illegal. Please provide only one or the other.|},
            field.rng );
        ]
    | Some d, None -> Result d
    | None, None ->
      if not is_final then
        Error
          [
            ( {%string|Missing delimiter for type: %{ty_to_string field.ty}|},
              field.rng );
          ]
      else Result Final
    | None, Some univ -> Result univ
  in
  let* () =
    match delim with
    | Fixed _ -> k_check_fixed field.ty
    | CharDelim (c, _) ->
      if Char_set.mem c body_ref_kind.allowed_chars then
        Error
          [
            ( {%string|The delimiter '%{to_readable c}' can occur in values of the type %{ty_to_string field.ty}|},
              field.rng );
          ]
      else Result ()
    | LengthEncode _ -> Result ()
    | Final -> Result ()
  in
  return
    ( paths,
      body_ref_kind,
      assert_delim_piece (Some field.name) body_assertion delim )

(** Kind-check a type and require it to be a string type. Returns the
    subscript paths, the string-refinement kind, and the M assertion
    code for the type. *)
and k_check_str_ty (ctxt : context) (t : ty) :
    (subscript_path list * str_ref_kind * m_code) Check.t =
  let t_str = ty_to_string t in
  let err_not_string =
    {%string|Expected %{t_str} to be a string type, but it is not.|}
  in
  let err_malformed = {%string|Type %{t_str} malformed|} in
  let open Check in
  let* paths, kind =
    with_error err_malformed (ty_range t) (k_synth_ty ctxt t)
  in
  match kind with
  | KProper ({ str_kind = Some str_kind; assertion }, _) ->
    return (paths, str_kind, assertion)
  | _ -> Error [ (err_not_string, ty_range t) ]

(** Kind-check a type and require it to be a proper type (as opposed
    to a type operator). Returns the subscript paths and the proper
    kind. *)
and k_check_proper_ty (ctxt : context) (t : ty) :
    (subscript_path list * proper_kind) Check.t =
  let t_str = ty_to_string t in
  let err_not_proper =
    {%string|Expected %{t_str} to be a proper type, but it is not.|}
  in
  let err_malformed = {%string|Type %{t_str} malformed|} in
  let open Check in
  let* paths, kind =
    with_error err_malformed (ty_range t) (k_synth_ty ctxt t)
  in
  match kind with
  | KProper (proper, _) -> return (paths, proper)
  | _ -> Error [ (err_not_proper, ty_range t) ]

(** Synthesize the kind of a type. Returns the subscript paths the
    type depends on and the type's kind. *)
and k_synth_ty (ctxt : context) (t : ty) :
    (subscript_path list * kind) Check.t =
  let open Check in
  match t with
  | TyVec (_, _) -> failwith "vectors not yet implemented"
  | TyDelimList (_, Final, rng) ->
    Error [ ("Final is not a legal delimiter for lists", rng) ]
  | TyDelimList (elem_ty, delim, rng) ->
    let* paths, elem_str_ref, elem_assert = k_check_str_ty ctxt elem_ty in
    let delim_chars = get_delim_chars delim in
    let* () =
      let common_chars = Char_set.inter elem_str_ref.allowed_chars delim_chars in
      if Char_set.is_empty common_chars then Result ()
      else
        let c = to_readable (Char_set.min_elt common_chars) in
        Error
          [
            ( {%string|Both values of the element type and the delimiter may contain the character %{c}.|},
              rng );
          ]
    in
    let assert_field = assert_delim_piece None elem_assert delim in
    let assertion =
      MBlock
        [
          MLine "n pos";
          MLine "s pos=1";
          MLine "f  d  q:pos=0";
          assert_field;
        ]
    in
    let str_ref =
      Some
        {
          discriminator = Prefix "";
          allowed_chars = Char_set.union delim_chars elem_str_ref.allowed_chars;
          fixed_length = None;
          fs_pred = None;
        }
    in
    return
      ( paths,
        KProper ({ str_kind = str_ref; assertion }, Check.no_range) )
  | TyObj (opt_root, fields, rng) ->
    let check_false_root (field : obj_ty_field) : unit Check.t =
      match field.key_ty with
      | TyStrLiteral ("root", _) ->
        Error [ ("Only the leading field may be called 'root'", field.rng) ]
      | _ -> Result ()
    in
    let* root_paths, root_assert =
      match opt_root with
      | Some root ->
        let* root_paths, _, root_assert =
          with_error "Object root type must be a string type." rng
            (k_check_str_ty ctxt root.val_ty)
        in
        return (root_paths, root_assert)
      | None ->
        return
          ( [],
            MBlock
              [
                MLine
                  "d %zzAssert($d(@loc)=\"10\",\"location \"_loc_\" should not contain data\")";
              ] )
    in
    let* () = do_all (List.map check_false_root fields) in
    let* key_ref_asserts =
      let_all
        (List.map (fun (f : obj_ty_field) -> k_check_str_ty ctxt f.key_ty) fields)
    in
    let key_paths = List.concat_map (fun (p, _, _) -> p) key_ref_asserts in
    let key_refs = List.map (fun (_, k, _) -> k) key_ref_asserts in
    let key_ty_refs =
      List.combine (List.map (fun (f : obj_ty_field) -> f.key_ty) fields) key_refs
    in
    let key_ty_ref_pairs = Utils.all_unique_unordered_pairs key_ty_refs in
    let check_pairs =
      do_all (List.map (fun (a, b) -> check_discrim a b) key_ty_ref_pairs)
    in
    let* () = with_error "Keys are not disjoint." rng check_pairs in
    let* val_path_kinds =
      let_all
        (List.map
           (fun (f : obj_ty_field) -> k_check_proper_ty ctxt f.val_ty)
           fields)
    in
    let val_paths = List.concat_map fst val_path_kinds in
    let val_kinds = List.map snd val_path_kinds in
    let key_prefixes =
      List.map (fun (_, k) -> str_ref_kind_prefix k) key_ty_refs
    in
    let assert_field ((field, key_prefix) : obj_ty_field * string)
        (key_assert : m_code) (val_kind : proper_kind) : m_code list =
      let check_prefix =
        [ MLine {%string|i $$zStrStartsWith(x,"%{key_prefix}") d  q|} ]
      in
      let key_id_code =
        match field.key_id with
        | Some id -> [ MLine {%string|n %{id} s %{id}=x|} ]
        | None -> []
      in
      let val_id_code =
        match field.val_id with
        | Some id -> [ MLine {%string|n %{id} s %{id}=$na(@loc@(x))|} ]
        | None -> []
      in
      let body =
        match val_kind with
        | { str_kind = Some _; assertion = str_val_assert } ->
          [
            MBlock
              [
                MLine "n y";
                MLine "d";
                key_assert;
                MLine "s y=x,x=@loc@(x) d  s x=y";
                str_val_assert;
              ];
          ]
        | { str_kind = None; assertion = array_val_assert } ->
          [
            MBlock
              [
                MLine "s loc=$na(@loc@(x)),level=level+1";
                MLine "d";
                key_assert;
                MLine "d";
                array_val_assert;
                MLine "s level=level-1,loc=$na(@loc,level)";
              ];
          ]
      in
      List.concat [ check_prefix; key_id_code; val_id_code; body ]
    in
    let key_asserts = List.map (fun (_, _, a) -> a) key_ref_asserts in
    let fields_with_prefixes = List.combine fields key_prefixes in
    let all_field_asserts =
      let rec loop fs ks vs =
        match (fs, ks, vs) with
        | f :: fs', k :: ks', v :: vs' ->
          assert_field f k v :: loop fs' ks' vs'
        | [], [], [] -> []
        | _ -> failwith "k_synth_ty TyObj: list length mismatch"
      in
      loop fields_with_prefixes key_asserts val_kinds
    in
    let assertion =
      MBlock
        [
          MLine "d";
          root_assert;
          MLine "n x";
          MLine "f  s x=$o(@loc@(x)) q:x=\"\" d";
          MBlock (List.concat all_field_asserts);
        ]
    in
    return
      ( List.concat [ root_paths; key_paths; val_paths ],
        KProper ({ str_kind = None; assertion }, Check.no_range) )
  | TyTuple (_, [], _) ->
    let str_ref =
      Some
        {
          discriminator = Prefix "";
          allowed_chars = Char_set.empty;
          fixed_length = Some 0;
          fs_pred = None;
        }
    in
    return
      ( [],
        KProper
          ( {
              str_kind = str_ref;
              assertion = MBlock [ MLine "d %zzAssert(x=\"\",\"error\")" ];
            },
            Check.no_range ) )
  | TyTuple (univ_delim, fields, _) ->
    let get_field_delim_chars (field : tuple_field) : Char_set.t =
      match field.delim with
      | Some d -> get_delim_chars d
      | None -> Char_set.empty
    in
    let n = List.length fields in
    let leading =
      let rec take k xs =
        if k <= 0 then []
        else match xs with x :: rest -> x :: take (k - 1) rest | [] -> []
      in
      take (n - 1) fields
    in
    let last_field =
      let rec last = function
        | [ x ] -> x
        | _ :: rest -> last rest
        | [] -> failwith "impossible"
      in
      last fields
    in
    let* leading_kind_path_assert =
      let_all (List.map (fun x -> k_check_field ctxt univ_delim x false) leading)
    in
    let* last_kind_path_assert = k_check_field ctxt univ_delim last_field true in
    let all_path_kind_asserts =
      leading_kind_path_assert @ [ last_kind_path_assert ]
    in
    let paths = List.concat_map (fun (p, _, _) -> p) all_path_kind_asserts in
    let kinds = List.map (fun (_, k, _) -> k) all_path_kind_asserts in
    let asserts = List.map (fun (_, _, a) -> a) all_path_kind_asserts in
    let field_body_chars =
      List.fold_left
        (fun acc (k : str_ref_kind) -> Char_set.union acc k.allowed_chars)
        Char_set.empty kinds
    in
    let delim_chars =
      match univ_delim with
      | Some d -> get_delim_chars d
      | None ->
        List.fold_left
          (fun acc f -> Char_set.union acc (get_field_delim_chars f))
          Char_set.empty fields
    in
    let head_discriminator =
      match kinds with
      | first :: _ ->
        (match first.discriminator with
         | Prefix s | Literal s -> Prefix s
         | SomeLiteral -> Prefix "")
      | [] -> Prefix ""
    in
    let str_ref =
      Some
        {
          discriminator = head_discriminator;
          allowed_chars = Char_set.union field_body_chars delim_chars;
          fixed_length = None;
          fs_pred = None;
        }
    in
    let assert_pieces =
      List.concat_map (fun assertion -> [ MLine "d"; assertion ]) asserts
    in
    let names = List.map (fun (f : tuple_field) -> f.name) fields in
    let new_all_names = MLine {%string|n %{String.concat "," names}|} in
    return
      ( paths,
        KProper
          ( {
              str_kind = str_ref;
              assertion =
                MBlock
                  (new_all_names :: MLine "n pos s pos=1" :: assert_pieces);
            },
            Check.no_range ) )
  | TyStrLiteral (str, _) ->
    let str_chars =
      let s = ref Char_set.empty in
      String.iter (fun c -> s := Char_set.add c !s) str;
      !s
    in
    let str_ref =
      Some
        {
          discriminator = Literal str;
          allowed_chars = str_chars;
          fixed_length = Some (String.length str);
          fs_pred = Some (fun x -> x = str);
        }
    in
    return
      ( [],
        KProper
          ( {
              str_kind = str_ref;
              assertion =
                MBlock
                  [ MLine {%string|d %zzAssert(x="%{str}","error")|} ];
            },
            Check.no_range ) )
  | TyUnion (components, _) ->
    let common_prefix (prefixes : string list) : string =
      match prefixes with
      | [] -> ""
      | first :: _ ->
        let min_length =
          List.fold_left
            (fun acc s -> min acc (String.length s))
            (String.length first) prefixes
        in
        let rec loop i =
          if i >= min_length then i
          else
            let c = first.[i] in
            if List.for_all (fun s -> s.[i] = c) prefixes then loop (i + 1)
            else i
        in
        let len = loop 0 in
        String.sub first 0 len
    in
    let assert_component
        ((_, kind, assertion) : subscript_path list * str_ref_kind * m_code) :
        m_code list =
      let prefix = str_ref_kind_prefix kind in
      [
        MLine {%string|i $$zStrStartsWith(x, "%{prefix}") d  q|};
        assertion;
      ]
    in
    let* ref_asserts = let_all (List.map (k_check_str_ty ctxt) components) in
    let _paths = List.concat_map (fun (p, _, _) -> p) ref_asserts in
    let kinds = List.map (fun (_, k, _) -> k) ref_asserts in
    let prefixes =
      List.map
        (fun (k : str_ref_kind) ->
          match k.discriminator with
          | Prefix s | Literal s -> s
          | SomeLiteral -> "")
        kinds
    in
    let ty_kinds = List.combine components kinds in
    let* () =
      do_all
        (List.map
           (fun (a, b) -> check_discrim a b)
           (Utils.all_unique_unordered_pairs ty_kinds))
    in
    let preds =
      List.filter_map (fun (k : str_ref_kind) -> k.fs_pred) kinds
    in
    let str_ref =
      Some
        {
          discriminator = Prefix (common_prefix prefixes);
          allowed_chars =
            List.fold_left
              (fun acc (k : str_ref_kind) ->
                Char_set.union acc k.allowed_chars)
              Char_set.empty kinds;
          fixed_length = None;
          fs_pred = Some (fun s -> List.exists (fun p -> p s) preds);
        }
    in
    let assertion =
      MBlock
        (List.concat
           [
             List.concat_map assert_component ref_asserts;
             [
               MLine
                 "d %zzAssert(0,x_\" does no match any components of union type.\")";
             ];
           ])
    in
    return ([], KProper ({ str_kind = str_ref; assertion }, Check.no_range))
  | TyBitStr (_, _) ->
    let res =
      Some
        {
          discriminator = Prefix "";
          allowed_chars = all_chars;
          fixed_length = None;
          fs_pred = None;
        }
    in
    return
      ( [],
        KProper
          ({ str_kind = res; assertion = MBlock [] }, Check.no_range) )
  | TySubscriptPath (path, _) ->
    let* key_ty_paths, str_ref_kind, key_ty_assertion =
      k_check_str_ty ctxt path.ty
    in
    let check_subscript (subscript : ty) : unit Check.t =
      let* _, kind = k_check_proper_ty ctxt subscript in
      proper_kind_sub kind proper_kind_some_literal
    in
    let* () = do_all (List.map check_subscript path.subscripts) in
    let subscript_strings = List.map ty_to_string path.subscripts in
    let subscripts_part =
      if path.subscripts = [] then "x"
      else String.concat "," subscript_strings ^ ",x"
    in
    let glob = path.global_name in
    let assertion =
      MBlock
        [
          MLine "d";
          key_ty_assertion;
          MLine
            {%string|d %zzAssert($d(%{glob}(%{subscripts_part})),"subscript exists at path")|};
        ]
    in
    return
      ( path :: key_ty_paths,
        KProper
          ( { str_kind = Some str_ref_kind; assertion }, Check.no_range ) )
  | TyName (name, rng) ->
    (match String_map.find_opt name ctxt.ty_alias_env with
     | Some entry -> return ([], entry.kind)
     | None ->
       (match String_map.find_opt name ctxt.ty_var_env with
        | Some entry -> return ([], entry.kind)
        | None ->
          Error [ ({%string|Type '%{name}' is not in context.|}, rng) ]))
  | TyApp (ty_op, ty_arg, _) ->
    let* _subscripts_op, k_op = k_synth_ty ctxt ty_op in
    let* _subscripts_arg, k_arg = k_check_proper_ty ctxt ty_arg in
    let* _param_name, _k_cod =
      match k_op with
      | KOperator (param_name, k_dom, k_cod, _) ->
        let error =
          {%string|Kind of type %{ty_to_string ty_arg} is not a subkind of parameter kind|}
        in
        let* () =
          with_error error (ty_range ty_arg) (proper_kind_sub k_arg k_dom)
        in
        return (param_name, k_cod)
      | _ ->
        Error
          [
            ( {%string|Expected a type operator but found %{ty_to_string ty_op}.|},
              ty_range ty_op );
          ]
    in
    let* subscripts, k_red = k_synth_ty ctxt (ty_normalize ctxt t) in
    return (subscripts, k_red)
  | TyForall (param_name, k_param, ty_body, _) ->
    let* k_param_proper =
      match k_param with
      | KProper (k_proper_param, _) -> return k_proper_param
      | _ ->
        Error [ ("Type parameters must be proper types", ty_range t) ]
    in
    let ctxt' =
      { ctxt with
        ty_var_env =
          String_map.add param_name { kind = k_param } ctxt.ty_var_env }
    in
    let* paths, k_body = k_synth_ty ctxt' ty_body in
    return
      ( paths,
        KOperator (param_name, k_param_proper, k_body, Check.no_range) )
  | TyRef (base_ty, refinement, rng) ->
    let* base_paths, base_proper_kind =
      with_error "Only proper types can be refined" rng
        (k_check_proper_ty ctxt base_ty)
    in
    let assertion' =
      MBlock
        [
          MLine "d";
          base_proper_kind.assertion;
          MLine {%string|d %zzAssert(%{m_expr_to_string refinement}, "error")|};
        ]
    in
    return
      ( base_paths,
        KProper ({ base_proper_kind with assertion = assertion' }, rng) )
  | TyWithout (base_ty, char_ban_set, rng) ->
    let* base_ty_paths, str_ref_kind, base_ty_assertion =
      k_check_str_ty ctxt base_ty
    in
    let assert_no_char (c : char) =
      MLine {%string|d %zzAssert($f(x,%{to_mstring c})=0 , "error")|}
    in
    let ban_lines =
      Char_set.fold (fun c acc -> assert_no_char c :: acc) char_ban_set []
    in
    let assertion' = MBlock (List.rev_append ban_lines [ base_ty_assertion ]) in
    let str_ref_kind' =
      {
        str_ref_kind with
        allowed_chars =
          Char_set.diff str_ref_kind.allowed_chars char_ban_set;
      }
    in
    return
      ( base_ty_paths,
        KProper
          ( { str_kind = Some str_ref_kind'; assertion = assertion' }, rng ) )
