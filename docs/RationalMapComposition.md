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

The separate [dense-open pullback interface](DenseOpenPullback.md) asks whether
**every** dense target open pulls back densely in ambient `X`. Its open-map
sufficiency result needs only `IsOpenMap f.hom`; its dominant route retains a
preirreducible source and nonempty target. The two relative-composition lemmas
here keep their stronger native first-map dominance and over-base hypotheses;
they neither assume the new predicate nor establish a generalized composition
law from it. The separate [controlled-composition module](DenseOpenComposition.md)
does define native partial- and rational-map operations from an explicit
`PullsDenseOpens` proof. Its
[controlled over-base companion](DenseOpenCompositionOver.md) proves the
resulting controlled composite over `S` when both maps are over `S`, without
dominance or the native theorem's preirreducibility/nonemptiness assumptions.
It does not replace the native `comp` theorem or assert predicate closure or
category laws.

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
lake build SchemeProperties.RationalMapComposition
lake build SchemePropertiesTest
```

The project's default targets also include `SchemeProperties` and
`SchemePropertiesExamples`. The producer and client both enable
`warningAsError`. Reproduction instructions are not a verification receipt,
acceptance or source-coverage claim.

The proof imports native rational-map and chosen-base APIs by Andrew Yang
and Justus Springer and composition by Justus Springer; original project
arguments and their adaptation are credited in [Credits](CREDITS.md).
