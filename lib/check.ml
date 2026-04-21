(** A source-code range, represented as a pair of lexing positions
    [(start, end)]. Used to tag AST nodes and error messages with the
    locations they came from. *)
type range = Lexing.position * Lexing.position

let no_pos : Lexing.position =
  { pos_fname = ""; pos_lnum = 0; pos_bol = 0; pos_cnum = 0 }

let no_range : range = (no_pos, no_pos)

(** The result of a check: either a successful value of type ['a] or an
    error carrying a stack of messages annotated with source ranges. *)
type 'a t =
  (* A failed check, carrying a stack of (message, source range) pairs
     describing the error and the context it was raised in. *)
  | Error of (string * range) list
  (* A successful check, carrying the produced value. *)
  | Result of 'a

let return (x : 'a) : 'a t = Result x

let bind (c : 'a t) (f : 'a -> 'b t) : 'b t =
  match c with
  | Error stack -> Error stack
  | Result r -> f r

let ( let* ) = bind
let ( let+ ) c f = bind c (fun x -> return (f x))

let with_error (msg : string) (rng : range) (c : 'a t) : 'a t =
  match c with
  | Error stack -> Error ((msg, rng) :: stack)
  | Result r -> Result r

let rec sequence (l : unit t list) : unit t =
  match l with
  | Error stack :: _ -> Error stack
  | _ :: rest -> sequence rest
  | [] -> Result ()

let rec fold (init : 's) (f : 's -> 'a -> 's) (l : 'a t list) : 's t =
  match l with
  | first :: rest ->
    let* a = first in
    let* s = fold init f rest in
    return (f s a)
  | [] -> return init

let rec fold_m (init : 's) (f : 's -> 'a -> 's t) (l : 'a list) : 's t =
  match l with
  | first :: rest ->
    let* s1 = f init first in
    fold_m s1 f rest
  | [] -> return init

let rec map (f : 'a -> 'b) (l : 'a t list) : 'b list t =
  match l with
  | first :: rest ->
    let* a = first in
    let* b = map f rest in
    return (f a :: b)
  | [] -> return []

let rec let_all (l : 'a t list) : 'a list t =
  match l with
  | first :: rest ->
    let* a = first in
    let* b = let_all rest in
    return (a :: b)
  | [] -> return []

let rec do_all (l : unit t list) : unit t =
  match l with
  | first :: rest ->
    let* () = first in
    do_all rest
  | [] -> return ()
