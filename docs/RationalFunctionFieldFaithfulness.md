# Faithfulness of function-field pullback

Import `SchemeProperties.RationalFunctionFieldFaithfulness` to use the
existing function-field pullback on dominant native rational maps between integral
schemes together with its equality-reflection and faithfulness results.

## Public interfaces

- `AlgebraicGeometry.Scheme.RationalMap.eq_of_functionFieldMap_eq` states that if
  `X` and `Y` are integral schemes, `r s : X ⤏ Y` are each dominant, and
  `r.functionFieldMap = s.functionFieldMap`, then `r = s`. The dominance
  witnesses are independent. The conclusion concerns quotient rational maps,
  not chosen representatives or their domains.
- The `Faithful` instance for
  `AlgebraicGeometry.IntegralDominantRationalScheme.functionFieldFunctor` says
  that pullback distinguishes arrows in
  `IntegralDominantRationalScheme.{u}ᵒᵖ`. For arrows `f g : A ⟶ B`, their
  underlying rational maps run from `B.unop` to `A.unop`; functorial pullback
  reverses this orientation. The instance makes `functionFieldFunctor.map_injective`
  available to ordinary category-theoretic clients.

The proof specializes the public `RationalMap.fromFunctionField_comp` to the
identity arrow, uses native composition with identity and the identity's generic
stalk calculation, and then applies native equality reflection for rational
maps from the source's function-field spectrum. It does not expose the
predecessor's private factorization or reimplement its function-field map.

`Test.RationalFunctionFieldFaithfulnessClient` contains only
private direct-import clients checking both independent-dominance quotient
reflection and `map_injective` for reversed category arrows; it exports no
additional mathematical API.

## Provenance and limits

The underlying pullback is supplied by the existing
`SchemeProperties.RationalFunctionFieldPullback` module in this same project.
This companion adapts original Formal Frontier proof expression; see
[Credits](CREDITS.md). It proves injectivity, **not** fullness,
an existence or reconstruction theorem, an equivalence, a birational result,
or a relative/base-change claim. No locally finite-type, separatedness, or
common-base assumption is required for this injectivity result. Faithfulness
alone establishes no particular source's formal coverage.

With the [pinned Lean toolchain](../lean-toolchain),
[Lake requirements](../lakefile.toml) and [resolved manifest](../lake-manifest.json)
(Lean 4.34.0-rc2, mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`,
11 packages, three direct requirements), obtain access to the official private
`coherent-modules` and `finite-etale-algebras` dependencies. First fetch the
matching precompiled mathlib cache using `lake exe cache get`, then run focused
checks with `lake build SchemeProperties.RationalFunctionFieldFaithfulness` and
`lake build Test.RationalFunctionFieldFaithfulnessClient`. The focused modules
and clients are outside the [fixed historical 73-module API snapshot](README.md).
