<!-- SPDX-License-Identifier: Apache-2.0 -->

# Composition controlled by dense-open pullback

Import `SchemeProperties.DenseOpenComposition` directly or use the aggregate
`SchemeProperties`. For arbitrary same-universe schemes `X Y Z : Scheme.{u}`,
this module extends mathlib's native partial and quotient rational maps; it
does not define another map type or a global composition instance. The first
map must explicitly satisfy the prerequisite
[`PullsDenseOpens`](DenseOpenPullback.md): the pullback of **every** dense open
of `Y` is dense in the ambient `X`, not just in the first map's dense domain.

## Operations and representatives

All declarations below live in `AlgebraicGeometry.Scheme`.

| Public declaration | Meaning |
| --- | --- |
| `PartialMap.compOfPullsDenseOpens f hf g` | Given `f : X.PartialMap Y`, `hf : f.PullsDenseOpens` and any `g : Y.PartialMap Z`, builds a native partial map with domain `f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain)`, dense by `hf g.domain g.dense_domain`, and morphism `(f.domain.ι.isoImage _).inv ≫ f.hom ∣_ g.domain ≫ g.hom`. The generated `compOfPullsDenseOpens_domain` and `_hom` projections expose these data. |
| `PartialMap.compOfPullsDenseOpens_restrict_left`, `_right` | Identify the result on a common dense restriction. The right restriction pulls back the *chosen* witness of equivalence, not necessarily the whole intersection of domains. |
| `PartialMap.compOfPullsDenseOpens_equiv_of_equiv_left`, `_right`, `compOfPullsDenseOpens_equiv_of_equiv` | Preserve equivalence when either or both partial-map representatives change. |
| `RationalMap.compOfPullsDenseOpens f hf g` | Given `f : X ⤏ Y`, `hf : f.PullsDenseOpens`, and any `g : Y ⤏ Z`, descend the partial composite to the existing quotient. `RationalMap.compOfPullsDenseOpens_def` computes it on a second representative; `RationalMap.toRationalMap_compOfPullsDenseOpens` proves independence of the first representative. |
| `PartialMap.compOfPullsDenseOpens_toPartialMap`, `RationalMap.compOfPullsDenseOpens_toRationalMap` | For a total second morphism `g : Y ⟶ Z`, recover existing `compHom` without extra geometry. |
| `PartialMap.compOfPullsDenseOpens_eq_comp`, `RationalMap.compOfPullsDenseOpens_eq_comp` | Recover mathlib's native `comp` when `[PreirreducibleSpace X] [Nonempty Y]` and the corresponding first-map dominance assumption also hold. |

For example, after `import SchemeProperties.DenseOpenComposition`, with
`open AlgebraicGeometry AlgebraicGeometry.Scheme` and
`{X Y Z : Scheme.{u}}` in scope:

```lean
example (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) :
    (f.compOfPullsDenseOpens hf g).domain =
      f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain) :=
  rfl

example (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) :
    f.toRationalMap.compOfPullsDenseOpens
        (f.pullsDenseOpens_toRationalMap_iff.mpr hf) g.toRationalMap =
      (f.compOfPullsDenseOpens hf g).toRationalMap :=
  RationalMap.toRationalMap_compOfPullsDenseOpens f hf g
```

The [direct-import client](../Test/DenseOpenCompositionClient.lean) checks
eleven private uses: arbitrary partial and rational compositions, changes of
both representatives, the quotient bridge, the open-map sufficiency route,
and native/total-second compatibilities. These are private API clients,
not new public declarations or constructed nondominant examples.

## Scope and neighboring APIs

The general operations require neither first-map dominance nor
`PreirreducibleSpace X` or `Nonempty Y`; there is no reducedness,
separatedness, finite-type or relative-base assumption. The premise `hf`
still has to be supplied: `PartialMap.pullsDenseOpens_of_isOpenMap` gives it
when `IsOpenMap f.hom`; a separate dominant route has additional hypotheses.
Neither a concrete nondominant witness nor closure of `PullsDenseOpens` under
composition is proved. No associativity, category law, generalized dominance
follows from this module alone. Its [controlled over-base companion](DenseOpenCompositionOver.md)
proves that the partial/rational controlled composite preserves `IsOver S`
when **both** maps are over `S` and the first has explicit `PullsDenseOpens`;
it does not prove predicate closure or category laws. The separate
[relative composition](RationalMapComposition.md) lemmas instead preserve
the base for native `comp` under first-map dominance and their stronger
preirreducibility/nonemptiness hypotheses.

## Reproduction and provenance

Use the repository's pinned Lean `leanprover/lean4:v4.34.0-rc2`, exact
`lakefile.toml` and `lake-manifest.json` (mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`). The declared official
`coherent-modules` and `finite-etale-algebras` dependencies are private
GitHub repositories, requiring authorized access. From the project root,
install the toolchain and **successfully fetch the matching precompiled
mathlib cache before building**:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
LAKE_JOBS=2 lake exe cache get
LAKE_JOBS=2 lake --wfail build SchemeProperties.DenseOpenComposition SchemePropertiesTest SchemeProperties
```

Completion also requires an applicable build and transitive standard-axiom
audit of all actual public, private and generated origin declarations,
allowing only `propext`, `Classical.choice` and `Quot.sound`.
Commands here are reproduction instructions, not a receipt for this destination.
This transfer derives from the separately accepted isolated contribution
`b592c13ff04fc9b8b87ef615c622f9a1e8e1ef86` in incubator issue #203;
that origin's review and checks do not certify a destination revision or
source correspondence. [CREDITS](CREDITS.md) distinguishes the original
Formal Frontier author and independent reviewer from the destination transfer.
The source uses native quotient and partial-map APIs by Andrew Yang, and
adapts native composition proof expression by Justus Springer, retaining
his copyright/Apache-2.0/author notice. No book prose or source PDF is copied.
