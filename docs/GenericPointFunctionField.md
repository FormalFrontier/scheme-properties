# Generic-point morphisms and function fields

Import `SchemeProperties.GenericPointFunctionField` for results about the
canonical map `j := Y.fromSpecStalk (genericPoint Y)` for an arbitrary
integral scheme `Y`. Here `K := Y.functionField` is the stalk at its generic
point, and `j : Spec K ⟶ Y` is a total morphism; its native rational quotient
is `j.toRationalMap`. The reversed field homomorphism is the **actual**
`j.toRationalMap.functionFieldMap : K ⟶ (Spec K).functionField`, not an
independently selected field isomorphism. This focused module publicly imports
the local `SchemeProperties.RationalFunctionFieldReconstruction` interface.

The producer supplies `fromSpecStalk_genericPoint_isDominant` and
`fromSpecStalk_genericPoint_toRationalMap_isDominant` as instances. The theorem
`genericPoint_functionFieldMap_specMap` reads the reversed map back: its
`Spec.map` is exactly `(Spec K).fromSpecStalk (genericPoint (Spec K))`.
`genericPoint_functionFieldMap_isIso` then establishes `IsIso` of the native
field homomorphism. The proof uses the public
`Scheme.RationalMap.functionFieldMap_compatible` without a local finite-type
assumption, monicity of the stalk morphism, the isomorphism between a field
and its closed-point stalk, and full faithfulness of `Spec`.

With `[JacobsonSpace Y] [Nontrivial Y]`, the theorem
`not_locallyOfFiniteType_fromSpecStalk_genericPoint` shows `¬ LocallyOfFiniteType j`.
For **any independently chosen** `sY : Y ⟶ S`, the theorem
`not_locallyOfFiniteType_fromSpecStalk_genericPoint_comp Y sY` states
`¬ LocallyOfFiniteType (j ≫ sY)`. This is a boundary on the *source structure
map* `Spec K ⟶ S`: it does not assert that every non-locally-finite-type
source morphism lacks a rational inverse. No Noetherian, separatedness,
infinite-field, presentation or finiteness premise is imposed.

An ordinary direct-import private client is at
[`Test/GenericPointFunctionFieldClient.lean`](../Test/GenericPointFunctionFieldClient.lean).
It specializes the generic theorems to `Y = Spec ℚ[X]`, proves its
nontriviality using the distinct prime ideals `(0)` and `(X)`, and
instantiates the relative boundary using the finite-type structure morphism
given by `Polynomial.C`. Its generic source is
`Spec((Spec ℚ[X]).functionField)`. Although this function field has the
canonical fraction-field relationship with `ℚ[X]`, this development does
**not** identify it literally with `RatFunc ℚ`, nor claim a checked equality of
the corresponding spectrum objects. A point-spectrum client checks the positive
field-map result without the `Nontrivial` condition. These nine private
declarations are examples, not additional public library results.

Reproduction with the repository's `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and its exact official
GitHub dependencies: first run `lake exe cache get` successfully under the
current manifest, then run
`lake --wfail build SchemeProperties SchemePropertiesTest SchemePropertiesExamples`.
Alternatively focus on `lake --wfail build SchemeProperties.GenericPointFunctionField`
and `lake --wfail build Test.GenericPointFunctionFieldClient`.
The dependency on reconstruction is a **local** library import, not an extra
Lake dependency or an external incubator import.

This original project proof imports mathlib's generic-stalk tools (including
Andrew Yang and Fangming Li) and rational-map interfaces building on Justus
Springer; it also imports this library's reconstruction module. See
[Credits](CREDITS.md) for expression provenance.
