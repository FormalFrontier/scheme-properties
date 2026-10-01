# Generic-point rational noninvertibility

Import `SchemeProperties.GenericPointRationalNoninvertibility`. This module
combines the [generic-point function-field map](GenericPointFunctionField.md),
the [Jacobson birational obstruction](JacobsonBirationalObstruction.md) and the
[exact native rational inverse bridge](RationalMapPartialIso.md).

For integral schemes `X` and `Y` in the same universe, with `Subsingleton X`,
`JacobsonSpace Y` and `Nontrivial Y`, the theorem
`Scheme.RationalMap.not_twoSidedInverse_of_subsingleton_of_jacobson` rules out
**both** source-first inverse laws for independently dominant native quotients
`forward : X ⤏ Y` and `reverse : Y ⤏ X`:

```text
forward.comp reverse = RationalMap.id X
reverse.comp forward = RationalMap.id Y
```

The exact inverse-to-`PartialIso` theorem would produce a birational relation,
contradicting the Jacobson obstruction. Dominance is required of each map;
the result does not identify either with the inverse of a total scheme map.

For integral `Y`, let `g = Y.fromSpecStalk (genericPoint Y)` and choose **any**
total structure map `sY : Y ⟶ S`. The construction
`Scheme.genericPointRationalHom Y sY` is a dominant rational arrow over `S`
from the chosen source structure **exactly `g ≫ sY`** to `sY`. The equation
`Scheme.genericPointRationalHom_toRationalMap` identifies its native quotient
with `g.toRationalMap`. Under `JacobsonSpace Y` and `Nontrivial Y`,
`Scheme.genericPointRationalHom_boundary` proves that the arrow's **actual
reversed** `functionFieldMap` has `IsIso` while the chosen-base rational arrow
does not. If it did, its categorical inverse would induce independently
dominant native quotients satisfying both laws above, although
`Spec Y.functionField` is subsingleton.

The [ordinary-import private client](../Test/GenericPointRationalNoninvertibilityClient.lean)
uses `Y = Spec ℚ[X]`, `S = Spec ℚ` and the polynomial-coefficient structure
map. It establishes **together** local finite type of the target structure,
failure of local finite type for the induced source structure, `IsIso` for
the reversed function-field map, and non-`IsIso` for the rational arrow.
Its `ZMod 2` example keeps the finite-field boundary visible. The source
is the actual `Spec Y.functionField`, not a claimed literal `Spec (RatFunc ℚ)`.

Neither the inverse obstruction nor the chosen-base boundary adds local finite
type, Noetherian, separatedness or infinite-field assumptions. The
non-finite-type example is separate from the inverse obstruction: these
results assert no universal converse, unrestricted category equivalence,
or total-scheme isomorphism. Earlier module-specific disclaimers in the
generic-point and Jacobson guides concern those modules alone; the composition
here is the specified rational noninverse theorem.

Original Formal Frontier proof expression is credited collectively in
[CREDITS](CREDITS.md). The arguments import mathlib's native rational maps,
birational and Jacobson geometry, and generic stalks rather than copying
their upstream proofs; authentic individual upstream notices stay upstream.
