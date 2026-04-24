%{
open Syntax
%}

/* Tokens carrying semantic values */
/* ID / GLOBALID carry (most-recent-comment, identifier-string) */
%token <string * string> ID
%token <string * string> GLOBALID
%token <char> CHAR
%token <int32> INT
%token <string> STRLITERAL
%token <string> FUNNAME
/* LSQUAREBRACK carries the most-recent-comment. */
%token <string> LSQUAREBRACK
/* TYPE carries the most-recent-comment. */
%token <string> TYPE

/* Plain punctuation / keyword tokens */
%token LENGTH TUPLE EQUALS COMMA COLON LANGLE RANGLE FIXED
%token LBRACK RBRACK EOF PIPE RSQUAREBRACK LIST
%token IN LPAREN RPAREN AT VEC DOT ASTERISK MAPSTO DOUBLECOLON
%token KARRAY KSTRINGLIT KSTRING UNDERSCORE OR AND LBARBRACK RBARBRACK
%token WITHOUT PLUS MINUS

%left PIPE AND OR PLUS MINUS EQUALS

%start <type_def list> parse_type_def_list
%start <prog> parse_prog
%start <type_query> parse_query

%%

parse_query:
  | g=GLOBALID LPAREN xs=subscript_list COMMA EOF
      { { global_name = snd g; subscripts = List.rev xs; style = OpenQuery } }
  | g=GLOBALID LPAREN EOF
      { { global_name = snd g; subscripts = []; style = OpenQuery } }
  | g=GLOBALID LPAREN xs=subscript_list RPAREN EOF
      { { global_name = snd g; subscripts = List.rev xs; style = ClosedQuery None } }
  | g=GLOBALID LPAREN xs=subscript_list RPAREN AT n=INT EOF
      { { global_name = snd g;
          subscripts = List.rev xs;
          style = ClosedQuery (Some (Int32.to_int n)) } }
  ;

subscript_list:
  | xs=subscript_list COMMA s=STRLITERAL { s :: xs }
  | s=STRLITERAL { [s] }
  ;

parse_prog:
  | ts=type_def_list IN asc=type_ascription_list EOF
      { (List.rev ts, List.rev asc) }
  ;

parse_type_def_list:
  | ts=type_def_list EOF { List.rev ts }
  ;

proper_kind:
  | ASTERISK { (tree_kind, $loc) }
  ;

type_ascription_list:
  | xs=type_ascription_list a=type_ascription { a :: xs }
  | a=type_ascription { [a] }
  ;

type_ascription:
  | g=GLOBALID COLON t=typ
      { ({ comment = fst g; id = snd g; ty = t; rng = $loc }
         : type_ascription) }
  ;

type_def_list:
  | ts=type_def_list t=type_def { t :: ts }
  | t=type_def { [t] }
  ;

type_param:
  | LPAREN i=ID COLON k=proper_kind RPAREN
      { { id = fst i; kind = fst k; rng = $loc } }
  ;

type_param_list:
  | xs=type_param_list p=type_param { p :: xs }
  | p=type_param { [p] }
  ;

type_def:
  | c=TYPE i=ID EQUALS t=typ
      { ({ comment = c; id = snd i; ty = t; rng = $loc } : type_def) }
  | c=TYPE i=ID EQUALS PIPE u=union_type
      { let ty =
          match u with
          | [ hd ] -> hd
          | _ -> TyUnion (List.rev u, $loc)
        in
        ({ comment = c; id = snd i; ty; rng = $loc } : type_def) }
  ;

union_type:
  | xs=union_type PIPE t=simple_type { t :: xs }
  | t=simple_type { [t] }
  ;

string_list:
  | xs=string_list COMMA s=STRLITERAL { s :: xs }
  | s=STRLITERAL { [s] }
  ;

simple_type:
  | TUPLE LBRACK fs=tuple_field_list RBRACK
      { TyTuple (None, List.rev fs, $loc) }
  | TUPLE d=delimiter LBRACK fs=tuple_field_list RBRACK
      { TyTuple (Some d, List.rev fs, $loc) }
  | i=ID { TyName (snd i, $loc) }
  | s=STRLITERAL { TyStrLiteral (s, $loc) }
  | LIST t=typ d=delimiter { TyDelimList (t, d, $loc) }
  | g=GLOBALID LPAREN ss=simple_type_list RPAREN DOT LSQUAREBRACK kt=typ RSQUAREBRACK
      { TySubscriptPath
          ( { global_name = snd g; subscripts = List.rev ss; ty = kt },
            $loc ) }
  | g=GLOBALID LPAREN RPAREN DOT LSQUAREBRACK kt=typ RSQUAREBRACK
      { TySubscriptPath
          ( { global_name = snd g; subscripts = []; ty = kt }, $loc ) }
  ;

simple_type_list:
  | t=simple_type COMMA rest=simple_type_list { t :: rest }
  | t=simple_type { [t] }
  ;

simple_type_app:
  | f=simple_type_app a=simple_type { TyApp (f, a, $loc) }
  | t=simple_type { t }
  ;

obj_field:
  | i=ID COLON t=typ
      { { description = fst i;
          key_id = None;
          key_ty = TyStrLiteral (snd i, $loc);
          val_id = None;
          val_ty = t;
          non_empty = true;
          rng = $loc } }
  | i=ID COLON vi=ID UNDERSCORE t=typ
      { { description = fst i;
          key_id = None;
          key_ty = TyStrLiteral (snd i, $loc);
          val_id = Some (snd vi);
          val_ty = t;
          non_empty = true;
          rng = $loc } }
  | c=LSQUAREBRACK ids=id_type_list RSQUAREBRACK COLON t=typ
      { make_multi_key_dict c ids None t $loc }
  | c=LSQUAREBRACK ids=id_type_list RSQUAREBRACK COLON vi=ID UNDERSCORE t=typ
      { make_multi_key_dict c ids (Some (snd vi)) t $loc }
  ;

obj_fields:
  | xs=obj_fields COMMA f=obj_field { f :: xs }
  | f=obj_field { [f] }
  ;

char_list:
  | c=CHAR COMMA rest=char_list { c :: rest }
  | c=CHAR { [c] }
  ;

typ:
  | t=simple_type PIPE u=union_type
      { TyUnion (t :: List.rev u, $loc) }
  | t=simple_type { t }
  | LBRACK fs=obj_fields RBRACK
      { make_obj_ty (List.rev fs) $loc }
  | LPAREN VEC t=typ RPAREN { TyVec (t, $loc) }
  | LPAREN i=ID DOUBLECOLON k=kind RPAREN MAPSTO body=typ
      { TyForall (snd i, k, body, $loc) }
  | LPAREN t=simple_type_app RPAREN { t }
  | LBARBRACK t=typ COLON e=m_expr RBARBRACK
      { TyRef (t, e, $loc) }
  | LPAREN t=typ WITHOUT cs=char_list RPAREN
      { let ban_set =
          List.fold_left
            (fun acc c -> Char_set.add c acc)
            Char_set.empty cs
        in
        TyWithout (t, ban_set, $loc) }
  ;

id_type_list:
  | t=typ COMMA rest=id_type_list { (None, t) :: rest }
  | t=typ { [ (None, t) ] }
  | i=ID UNDERSCORE t=typ COMMA rest=id_type_list
      { (Some (snd i), t) :: rest }
  | i=ID UNDERSCORE t=typ { [ (Some (snd i), t) ] }
  ;

m_expr_list:
  | e=m_expr COMMA rest=m_expr_list { e :: rest }
  | e=m_expr { [e] }
  ;

m_bin_op:
  | AND { And }
  | OR  { Or }
  | PLUS { Plus }
  | MINUS { Minus }
  | EQUALS { Eq }
  ;

m_expr:
  | f=FUNNAME LPAREN args=m_expr_list RPAREN
      { FunCall (f, args, $loc) }
  | f=FUNNAME LPAREN RPAREN
      { FunCall (f, [], $loc) }
  | l=m_expr AND r=m_expr { BinOp (l, And, r, $loc) }
  | l=m_expr OR r=m_expr { BinOp (l, Or, r, $loc) }
  | l=m_expr PLUS r=m_expr { BinOp (l, Plus, r, $loc) }
  | l=m_expr MINUS r=m_expr { BinOp (l, Minus, r, $loc) }
  | l=m_expr EQUALS r=m_expr { BinOp (l, Eq, r, $loc) }
  | i=ID { Var (snd i, $loc) }
  | n=INT { Int (n, $loc) }
  | LPAREN e=m_expr RPAREN { e }
  | s=STRLITERAL { StrLit (s, $loc) }
  ;

kind:
  | KARRAY
      { KProper
          ( { str_kind = None; assertion = MLine "unused assertion" },
            $loc ) }
  | KSTRINGLIT
      { KProper
          ( { str_kind =
                Some
                  { allowed_chars = all_chars;
                    discriminator = SomeLiteral;
                    fixed_length = None;
                    fs_pred = None };
              assertion = MLine "unused assertion" },
            $loc ) }
  | KSTRING
      { KProper (proper_kind_string, $loc) }
  ;

tuple_field_list:
  | xs=tuple_field_list COMMA f=tuple_field { f :: xs }
  | f=tuple_field { [f] }
  ;

tuple_field:
  | i=ID COLON t=typ COLON d=delimiter
      { { comment = fst i; name = snd i; ty = t; delim = Some d; rng = $loc } }
  | i=ID COLON t=typ
      { { comment = fst i; name = snd i; ty = t; delim = None; rng = $loc } }
  ;

delimiter:
  | FIXED { Fixed $loc }
  | LENGTH { LengthEncode $loc }
  | c=CHAR { CharDelim (c, $loc) }
  | LANGLE n=INT RANGLE
      { CharDelim (Char.chr (Int32.to_int n), $loc) }
  ;
