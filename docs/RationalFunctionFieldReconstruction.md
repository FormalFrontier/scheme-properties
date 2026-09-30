# Dominant rational maps from compatible function-field maps

Import `SchemeProperties.RationalFunctionFieldReconstruction` (or the aggregate
`SchemeProperties` root). The producer imports the same-project
`SchemeProperties.RationalFunctionFieldFaithfulness` and its pullback API; it
does not duplicate either predecessor's definitions or categorical machinery.

For `X Y S : Scheme.{u}` with `[IsIntegral X]`, `[IsIntegral Y]`, choose total
arrows `sX : X ⟶ S` and `sY : Y ⟶ S`. Put `ηX := genericPoint X` and
`ηY := genericPoint Y`. A field homomorphism points **backward**:

```lean
φ : Y.functionField ⟶ X.functionField
hφ : (Spec.map φ ≫ Y.fromSpecStalk ηY) ≫ sY = X.fromSpecStalk ηX ≫ sX
```

Under `[LocallyOfFiniteType sY]`, the noncomputable
`Scheme.RationalMap.ofFunctionFieldMap sX sY φ hφ : X ⤏ Y` is a native
**quotient** rational map. The producer exports the inferred instance
`ofFunctionFieldMap_isDominant`, the explicit theorem
`isDominant_ofFunctionFieldMap`, and the exact laws
`ofFunctionFieldMap_compHom` and `functionFieldMap_ofFunctionFieldMap`:

```lean
(ofFunctionFieldMap sX sY φ hφ).compHom sY = sX.toRationalMap
(ofFunctionFieldMap sX sY φ hφ).functionFieldMap = φ
```

Conversely, for any **independently dominant** `r : X ⤏ Y`, the equation
`r.compHom sY = sX.toRationalMap` yields the geometric triangle for
`r.functionFieldMap` by `functionFieldMap_compatible sX sY r`; this direction
requires **no** local-finite-type condition. If `sY` is locally of finite type,
`ofFunctionFieldMap_functionFieldMap sX sY r h` reconstructs `r` exactly.
For two independently dominant maps, the imported official
`eq_of_functionFieldMap_eq` reflects equality of their reversed field maps
without local finite type, separatedness, or chosen base. The private ordinary
import client at `Test/RationalFunctionFieldReconstructionClient.lean`
checks all these claims with arbitrary endpoints, independently chosen arrows,
and independently given dominance witnesses; it exports no declaration.

The native `ofFunctionField` spreads out the compatible map
`Spec.map φ ≫ Y.fromSpecStalk ηY` on a dense open. The image of the source
field spectrum's unique point under `Spec.map φ` is the target's unique point;
the stalk map sends this point to `ηY`. The spread-out map therefore contains
the target generic point in its image and is dominant. Its geometric readback
equals the original map; composition with identity gives the public generic
factorization for a dominant rational map. Cancel the preimmersion
`Y.fromSpecStalk ηY` and use `Spec.map_injective` to recover `φ`.
The converse combines native total-map stalk formulas and composition, then
uses native geometric equality reflection on *quotients*. The base equation
does **not** say every representative is strictly over `S`.

Local finite type on `sY` is sufficient for this construction. Uniform existence
without that hypothesis is **not** proved here; no counterexample to such
existence is formalized in this module. There is no finite-type requirement
on `X`, no separatedness assumption on `Y`, no unrestricted `Full` instance
or assertion that all geometric maps from a function-field spectrum are dominant.

Reproduce the focused producer/client checks with the repository's pinned Lean
toolchain (`leanprover/lean4:v4.34.0-rc2`) and exact `lake-manifest.json`
(mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`, 11 resolved
packages and three direct GitHub dependencies). From this project root, after
obtaining access to its private official dependencies:

```sh
lake exe cache get
lake build SchemeProperties.RationalFunctionFieldReconstruction
lake build Test.RationalFunctionFieldReconstructionClient
```

The proof imports this library's pullback and faithfulness modules and
mathlib's native spreading, quotient, stalk and scheme APIs. Adapted
expression is credited in [Credits](CREDITS.md).
