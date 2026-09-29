# Relative composition of rational maps over a scheme

Import `SchemeProperties.RationalMapComposition` directly or use the aggregate
`SchemeProperties`. This module's sole direct mathematical import is mathlib's
`Mathlib.AlgebraicGeometry.Birational.Composition`. Its declarations extend the
**native** partial- and rational-map APIs in `AlgebraicGeometry.Scheme`; they
do not define new maps or composition laws.

- `PartialMap.isOver_comp_of_isDominant_first`: for schemes `X`, `Y`, `Z`, `S` in
  one universe, `[PreirreducibleSpace X]`, `[Nonempty Y]`, `[X.Over S]`,
  `[Y.Over S]`, `[Z.Over S]`, a map `f : X.PartialMap Y` with
  `[IsDominant f.hom]` and `[f.IsOver S]`, and any `g : Y.PartialMap Z` with
  `[g.IsOver S]`, concludes `(f.comp g).IsOver S`.
- `RationalMap.isOver_comp_of_isDominant_first`: with the same scheme/space/base
  assumptions, `f : X ⤏ Y` with `[f.IsDominant]` and `[f.IsOver S]`, and any
  `g : Y ⤏ Z` with `[g.IsOver S]`, concludes `(f.comp g).IsOver S`.

Neither lemma needs dominance of the second map, reducedness, separatedness,
finite type, irreducibility of the target, nor a nonemptiness assumption on `Z`.
These are **named lemmas**, not globally installed instances. The partial-map
proof computes the underlying native composite and uses the open-restriction and
image-isomorphism triangles to commute its structure map to `S`. The quotient
proof selects over-`S` representatives, transfers dominance of the first map,
then applies the partial-map result and native quotient composition. Arbitrarily
chosen rational-map representatives need not be over `S` on their entire domain.
Native `compHom` remains the existing interface for a total second morphism;
native composition density still relies on dominance of the first map and the
stated preirreducibility/nonemptiness assumptions.

For example, with those scheme and typeclass assumptions in scope:

```lean
example (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z)
    [f.IsOver S] [g.IsOver S] : (f.comp g).IsOver S :=
  RationalMap.isOver_comp_of_isDominant_first f g
```

The ordinary-import [client](../Test/RationalMapCompositionClient.lean) checks
both generic second maps and both native `compHom` equalities for a total second
morphism. Its four theorems are private tests, not public API; they do not
construct a nondominant example.

For project reproduction, use the pinned `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json` with access to the declared private GitHub dependencies.
Fetch the matching mathlib cache **successfully** before building:

```sh
lake exe cache get
LAKE_JOBS=2 lake build SchemeProperties.RationalMapComposition
LAKE_JOBS=2 lake build SchemePropertiesTest
```

The project's default targets also include `SchemeProperties` and
`SchemePropertiesExamples`. The producer and client both enable
`warningAsError`. Reproduction instructions are not a verification receipt,
acceptance or source-coverage claim.

The proof reuses native rational-map definitions and over-base APIs by Andrew
Yang and Justus Springer and native composition by Justus Springer. Scope and
research guidance: Atlas. Original Lean proofs and client: Formal Frontier
Agents, Hive Task `hive-request-d04a528c8fefc542b1e53f2a0d565eecd90fde23`,
UID `94b1be7d-b4fc-4bc6-8fcf-c08d31f48c9e`. Scheme Properties transfer:
Formalization Worker B, Hive Task
`hive-request-fb8c186a9915829afa350a73e09f7dfd98df6c89`, UID
`ccb5a70b-e209-413c-af50-ee0b4a733e97`.
