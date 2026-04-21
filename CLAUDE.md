# SchemaTypes2 — project conventions

## Code style

- **Document every type definition.** Every `type` declaration — records,
  variants, aliases, abstract types — gets a doc comment (`(** ... *)`)
  explaining what the type represents. This applies to ported types as well
  as new ones.
- **Document every variant of sum types.** When defining a variant (sum) type
  — whether a plain variant, polymorphic variant, or GADT — attach a comment
  to each constructor explaining what the variant represents and what its
  payload fields mean. This applies to ported types as well as new ones.
