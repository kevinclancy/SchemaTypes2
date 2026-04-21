let rec all_unique_unordered_pairs (lst : 'a list) : ('a * 'a) list =
  match lst with
  | head :: rest ->
    let a = List.map (fun x -> (head, x)) rest in
    a @ all_unique_unordered_pairs rest
  | [] -> []

let fst3 (x, _, _) = x
let snd3 (_, x, _) = x
let thrd3 (_, _, x) = x
