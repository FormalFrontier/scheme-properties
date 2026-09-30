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

**Original preparation snapshot, September 30, 2026, before Scheme Properties
PR #148's later review:** the isolated incubator donor code
`db402a20a6e76ec62720d9b28ce045fa874bf6e1` had independent code review
and Atlas's code-only acceptance under incubator issue #343; it was never
merged into shared incubator main. The predecessor reconstruction had a
separate verified official Scheme Properties release
`5e98363b3a8738544d966d1603ace4df183573d4`, whose tree equals the original
destination transfer's parent tree. At that preparation stage, destination
build, complete transitive axiom
audit including private and generated declarations, fresh transfer review,
Atlas's destination acceptance and integration, distinct reviewed release,
publication and source-specific correspondence/coverage were **pending**, not
inferred from the donor's checks or review. This is a historical snapshot, not
a later current verdict; consult Scheme Properties PR #148 and Atlas's incubator
#343 for subsequent exact-revision evidence and decisions. Destination code
acceptance and integration do not themselves establish official publication or
source coverage.

Original static argument: worker-b Task
`hive-request-b7543b20151ccad863ac1811c291a8f92d0b6931` (UID
`70e238b7-5c9d-4823-b446-107bf789661b`), independently assessed by worker-a
Task `hive-request-1ede527b2a9f5a3c079b5ef66dc7ff9ac3258d6f` (UID
`63800e6d-5cae-4e30-b85e-8b53ffa2c8aa`). Original [producer](../SchemeProperties/RationalFunctionFieldInverse.lean),
client and guide: worker-b Task
`hive-request-d08fb8e66816eeda60f176adb2a705118712a0bf` (UID
`20e3853c-7a2c-44db-b98e-e26f5a4cb0f8`), independently reviewed by
worker-a Task `hive-request-b3aa2ab1ace57a60d8225302ef3f5053442efa16`
(UID `d1e145b8-7bb5-4425-bd3c-be736e2951b5`). The separate transfer and
adapted documentation are by worker-b Task
`hive-request-50a6b8f62bfe8ef71ff3eebc1e00b9c2fb376413` (UID
`4b59b8cd-4509-4cc7-a6d8-86aad520a21f`). See [Credits](CREDITS.md)
for distinct expression provenance and rights qualifications.
