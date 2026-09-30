# Function-field pullback along dominant rational maps

`SchemeProperties.RationalFunctionFieldPullback` constructs a unital
homomorphism `Y.functionField ⟶ X.functionField` from each dominant native quotient
rational map `r : X ⤏ Y` between integral schemes. The construction uses the
quotient-invariant native `r.fromFunctionField : Spec X.functionField ⟶ Y`:
dominance sends the closed point of `Spec X.functionField` to the generic point
of `Y`, so `Scheme.stalkClosedPointTo` applies after the canonical stalk transport.
No locally-finite-type, separatedness, or base-scheme assumption is imposed.

Use `import SchemeProperties.RationalFunctionFieldPullback` for the focused
module, or `import SchemeProperties` for the aggregate. The focused module
imports the existing integral dominant rational-map category and mathlib's
native composition and stalk interfaces. The main interfaces are:

- `Scheme.RationalMap.fromFunctionField_closedPoint`: the generic-image bridge.
- `Scheme.RationalMap.functionFieldMap`: the reversed ring homomorphism.
- `Scheme.RationalMap.functionFieldMap_eq_of_fromFunctionField_eq`: readback
  invariance for identical native maps from the source field spectrum.
- `Scheme.RationalMap.fromFunctionField_comp`: geometric compatibility with native
  quotient composition; it needs only the **first** arrow dominant, and the
  second arrow and its target may be arbitrary.
- `Scheme.RationalMap.functionFieldMap_id` and
  `Scheme.RationalMap.functionFieldMap_comp`: identity and reversed composition;
  the latter needs an integral target and **both** arrows dominant.
- `IntegralDominantRationalScheme.functionFieldFunctor`:
  `IntegralDominantRationalSchemeᵒᵖ ⥤ CommRingCat`, using the existing integral
  objects and dominant quotient arrows of Scheme Properties.

The composition bridge computes the actual native partial composite on the
inverse-image dense open. Its two morphisms into the second representative's
domain become equal after composing with the open immersion; monicity then
identifies them. The native stalk factorization identifies their composites
with the first representative's map from its function-field spectrum.
Quotient-level compatibility follows from native composition of representatives;
the quotient calculation uses the native `RationalMap.toRationalMap_comp` law.
`Spec.map_injective` and monicity of `fromSpecStalk` then give reversed composition
of ring homomorphisms. This argument does not assume that ordinary
`stalkClosedPointTo_comp` alone applies to rational composition.

The [private direct-import client](../Test/RationalFunctionFieldPullbackClient.lean)
checks generic
image, representative readback, dense restriction, identities, two- and
three-arrow composition, and mapping by the category functor.
This module does not reconstruct rational maps from arbitrary field homomorphisms,
prove fullness/faithfulness, or assert a relative or birational result.

The [pinned toolchain](../lean-toolchain), [Lake requirements](../lakefile.toml)
and [resolved manifest](../lake-manifest.json) give the exact Lean 4, mathlib
and 11-package dependency graph; `coherent-modules` and
`finite-etale-algebras` are official **private** GitHub dependencies requiring
authorized access. After obtaining access, fetch the matching precompiled
mathlib cache (`lake exe cache get`) before building the focused module, its
private client or the aggregate. This guide and client are outside the
[fixed historical 73-module API snapshot](README.md).
