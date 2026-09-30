# Dominant rational inverses over a chosen base

Import `SchemeProperties.RationalFunctionFieldInverse` directly or through
`SchemeProperties`. For arbitrary `S : Scheme.{u}` and integral objects
`X Y : IntegralDominantRationalSchemeOver S`, the given arrow `f : X ⟶ Y`
carries a dominant native quotient rational map over the objects' independently
chosen total maps to `S`.

* `IntegralDominantRationalSchemeOver.isIso_iff_isIso_functionFieldMap f`:
  assuming **only** `[LocallyOfFiniteType X.toBase]`, the given chosen-base
  rational arrow is an isomorphism exactly when its contravariant
  `f.toRationalMap.functionFieldMap : Y.toScheme.functionField ⟶
  X.toScheme.functionField` is an isomorphism of `CommRingCat` objects.
* `IntegralDominantRationalSchemeOver.isIso_functionFieldMap f`:
  an isomorphism of the given arrow yields an isomorphism of function-field
  maps **without** a local finite type hypothesis.

The construction applies the public compatibility triangle for the dominant
quotient to the inverse field homomorphism. Contravariance of `Spec.map`
reverses the triangle, and [reconstruction](RationalFunctionFieldReconstruction.md)
spreads that inverse homomorphism into a rational map whose **target is the
original source**. Reconstruction therefore needs source local finite type,
not target local finite type. Public field-homomorphism readback, reversed
composition and identity, and [faithfulness](RationalFunctionFieldFaithfulness.md)
establish both native quotient inverse laws; the chosen-base category packages
these as `IsIso f`. The three private checks in the ordinary direct-import
[client](../Test/RationalFunctionFieldInverseClient.lean) exercise independently
chosen maps, both quotient inverse laws and the converse without finiteness.
They do not export new theorems.

This is an isomorphism in the *native dominant rational category*, not an
isomorphism of total schemes. No `PartialIso` or `BirationalOver` conversion
is supplied; absence of a formal bridge does not assert mathematical
unrelatedness. Source local finite type is sufficient, not necessary for
individual arrows. A field-isomorphism criterion without an extendability
condition on the original source is false in general. No separatedness or
target local finite type is assumed.

Reproduce in this project's root with pinned `leanprover/lean4:v4.34.0-rc2`,
mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`, and the unchanged
Scheme Properties graph of 11 resolved packages and three direct requirements.
First successfully run `lake exe cache get`, then run
`lake build SchemeProperties.RationalFunctionFieldInverse` and
`lake build Test.RationalFunctionFieldInverseClient`. These are destination
commands, **not** records of a destination run.

The focused module uses this library's native reconstruction and function-field
pullback interfaces. Its original project proof expression is credited in
[Credits](CREDITS.md); it does not establish a total-scheme isomorphism.
