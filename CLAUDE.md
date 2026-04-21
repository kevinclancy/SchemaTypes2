# SchemaTypes2 — project conventions

## Code style

- **Document every type definition.** Every `type` declaration — records,
  variants, aliases, abstract types — gets a doc comment (`(** ... *)`)
  explaining what the type represents. This applies to ported types as well
  as new ones.
- **Document every variant of sum types.** When defining a variant (sum) type
  — whether a plain variant, polymorphic variant, or GADT — attach a doc
  comment to each constructor explaining what the variant represents and
  what its payload fields mean. This applies to ported types as well as new
  ones.
- **Variant and record doc-comment layout.** Doc comments for variant
  constructors and record fields go on the line *after* the
  constructor/field, aligned in the same column as the `|` (for
  variants) or the field name (for records). Each constructor/field +
  docstring group must be separated from the next by a blank line. The
  blank line is load-bearing — without it, OCaml's parser merges
  adjacent docstrings and merlin/VSCode hover shows the wrong
  documentation. Examples:
  ```
  type t =
    | A of int
    (** Doc for A. *)

    | B of string
    (** Doc for B. *)

  type r = {
    x : int;
    (** Doc for x. *)

    y : string;
    (** Doc for y. *)
  }
  ```
