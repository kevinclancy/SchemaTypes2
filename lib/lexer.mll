{
open Parser

(** Most recently accumulated doc-comment text, built up by the
    [comment] rule and consumed when the next TYPE / LSQUAREBRACK /
    ID / GLOBALID token is emitted. Cleared on blank lines. *)
let last_comment = ref ""

(** Advance the lexer's position to the next line. *)
let newline (lexbuf : Lexing.lexbuf) : unit =
  Lexing.new_line lexbuf

(** Remove the leading and trailing quotes from a quoted string. *)
let remove_quotes (s : string) : string =
  String.sub s 1 (String.length s - 2)
}

let digit = ['0'-'9']
let whitespace = [' ' '\t']
let newline = ('\n' | '\r' '\n')
let alpha = ['a'-'z' 'A'-'Z']
let alnum = ['a'-'z' 'A'-'Z' '1'-'9']

rule token = parse
  | newline        { newline lexbuf; last_comment := ""; token lexbuf }
  | whitespace     { token lexbuf }
  | "length"       { LENGTH }
  | "fixed"        { FIXED }
  | "list"         { LIST }
  | "without"      { WITHOUT }
  | "vec"          { VEC }
  | "in"           { IN }
  | "tuple"        { TUPLE }
  | "type"         { TYPE (!last_comment) }
  | "KArray"       { KARRAY }
  | "KStringLit"   { KSTRINGLIT }
  | "KString"      { KSTRING }
  | "=>"           { MAPSTO }
  | "::"           { DOUBLECOLON }
  | "{|"           { LBARBRACK }
  | "|}"           { RBARBRACK }
  | "."            { DOT }
  | "|"            { PIPE }
  | "*"            { ASTERISK }
  | "="            { EQUALS }
  | ","            { COMMA }
  | "("            { LPAREN }
  | ")"            { RPAREN }
  | "{"            { LBRACK }
  | "}"            { RBRACK }
  | "_"            { UNDERSCORE }
  | "@"            { AT }
  | ":"            { COLON }
  | "["            { LSQUAREBRACK (!last_comment) }
  | "]"            { RSQUAREBRACK }
  | "<"            { LANGLE }
  | ">"            { RANGLE }
  | "!"            { OR }
  | "&"            { AND }
  | "+"            { PLUS }
  | "-"            { MINUS }
  | ['\''][^'"']['\''] {
      let s = Lexing.lexeme lexbuf in
      CHAR s.[1]
    }
  | "//"           { last_comment := ""; comment lexbuf }
  | ['"'] [^'"']* ['"'] { STRLITERAL (remove_quotes (Lexing.lexeme lexbuf)) }
  | ['^'] ['%']? alnum* {
      GLOBALID (!last_comment, Lexing.lexeme lexbuf)
    }
  | alpha alnum* {
      ID (!last_comment, Lexing.lexeme lexbuf)
    }
  | ['-']? digit+ {
      INT (Int32.of_string (Lexing.lexeme lexbuf))
    }
  | "$$" alnum* { FUNNAME (Lexing.lexeme lexbuf) }
  | "$" alnum* { FUNNAME (Lexing.lexeme lexbuf) }
  | eof            { EOF }

and comment = parse
  | newline whitespace* "//" {
      newline lexbuf;
      last_comment := !last_comment ^ "\n";
      comment lexbuf
    }
  | newline { newline lexbuf; token lexbuf }
  | _ { last_comment := !last_comment ^ Lexing.lexeme lexbuf; comment lexbuf }
