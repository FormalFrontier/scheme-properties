<!-- SPDX-License-Identifier: Apache-2.0 -->

# Pulling back dense opens along partial and rational maps

Import `SchemeProperties.DenseOpenPullback` directly, or use the aggregate
`SchemeProperties` import. This module extends mathlib's **native**
`AlgebraicGeometry.Scheme.PartialMap` and `RationalMap` (`X ⤏ Y`); it adds no
new map type or global instance. The [direct-import client](../Test/DenseOpenPullbackClient.lean)
checks seven anonymous uses of the API with warnings treated as errors.

For arbitrary same-universe schemes `X` and `Y`, `f.PullsDenseOpens` means
that **every** `V : Y.Opens` dense in `Y` has pullback
`f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ V)` dense in the **whole source `X`**, not merely
in the domain of `f`. The predicate itself has no reducedness, separation,
preirreducibility, dominance or nonemptiness assumption; it does not exclude
empty schemes. Native partial maps already have dense domains.

## Public interface

All these declarations are in `AlgebraicGeometry.Scheme`:

| Declaration | Meaning and hypotheses |
| --- | --- |
| `PartialMap.PullsDenseOpens` | The all-dense-target-opens predicate above. |
| `PartialMap.pullsDenseOpens_iff_of_equiv` | Equivalent native partial maps have the same property. |
| `PartialMap.pullsDenseOpens_restrict_iff` | Restricting to a dense source open `W` with `W ≤ f.domain` preserves the property in both directions. |
| `PartialMap.pullsDenseOpens_of_isOpenMap` | `IsOpenMap f.hom` alone suffices; no dominance or irreducibility is required. |
| `PartialMap.pullsDenseOpens_of_isDominant` | A separate route assumes `[PreirreducibleSpace X] [Nonempty Y] [IsDominant f.hom]`. |
| `RationalMap.PullsDenseOpens` | Some native partial-map representative has the property. |
| `PartialMap.pullsDenseOpens_toRationalMap_iff` | The quotient rational map has the property exactly when its given partial map does. |
| `RationalMap.pullsDenseOpens_representative_iff` | The property can instead be tested on the native chosen `representative`. |

For example, with `{X Y : Scheme.{u}}` and the relevant hypotheses in scope:

```lean
example (f : X.PartialMap Y) (hf : IsOpenMap f.hom) :
    f.toRationalMap.PullsDenseOpens :=
  f.pullsDenseOpens_toRationalMap_iff.mpr (f.pullsDenseOpens_of_isOpenMap hf)
```

The full [client](../Test/DenseOpenPullbackClient.lean) also checks the
equivalence, restriction, quotient, representative and dominant routes. These
generic examples are not concrete nondominant witnesses and persist no new
public theorem declarations.

## Argument and limits

For equivalent partial maps, the native `equiv` supplies a common dense open
on which their restrictions agree. A private equality of pullbacks restricted
to that open, density of intersections with dense opens, and density
monotonicity establish the two directions. Native `restrict_equiv` yields the
restriction theorem. Invariance makes the existential predicate on the native
rational-map quotient independent of representatives and gives both bridge
equivalences.

The open-map route uses mathlib's `Dense.preimage` for `f.hom`, then density
of the image under the dense-domain inclusion into `X`. In contrast, the
dominant route uses the preirreducible/nonempty-open argument available under
its stated assumptions. Bare dominance for arbitrary schemes does **not**
follow as a sufficient condition here; this predicate module itself does not
prove dominance from `PullsDenseOpens`. The separately imported
[dominance companion](DenseOpenPullbackDominance.md) proves that converse under
`[Nonempty X] [PreirreducibleSpace Y]`, and an iff under four explicit
nonempty/preirreducible hypotheses. Pulling back one selected second-map domain
is weaker than the *every* dense-open contract. The predicate module itself
defines no composition operation. Its [controlled-composition consumer](DenseOpenComposition.md)
uses an explicit `PullsDenseOpens` proof for partial and rational composition,
but proves no predicate closure, associativity, category structure or general
relative-base composite **by itself**. Its
[controlled over-base companion](DenseOpenCompositionOver.md) proves the
controlled composite over a common `S` from explicit first-map `PullsDenseOpens`
and both maps' `IsOver S` hypotheses, without making the predicate closed
under composition. For the separate, stronger-premise **native** over-base
composition lemmas, see [Relative Composition](RationalMapComposition.md).

## Reproduction and provenance

Use the repository-pinned `lean-toolchain` (Lean v4.34.0-rc2),
`lakefile.toml` and `lake-manifest.json` (mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`). The declared official
`coherent-modules` and `finite-etale-algebras` dependencies live in private
GitHub repositories and require authorized access. Install the pinned
toolchain, fetch its matching precompiled mathlib cache **successfully before**
building in a fresh checkout, and build the producer, client and aggregate
targets:

```sh
lake exe cache get
LAKE_JOBS=2 lake --wfail build SchemeProperties.DenseOpenPullback SchemePropertiesTest SchemeProperties
```

For completed-result checks, audit the transitive axioms of **all** actual
origin declarations, including private/generated ones, allowing only
`propext`, `Classical.choice` and `Quot.sound`. The isolated incubator origin
at `aa3709064e8706ff816bc5e2ebb5ceeb58435432` received its own
independent review and acceptance; those facts do not establish the checks,
review, integration, official publication or source coverage of any destination
revision. Exact destination evidence and decisions must be bound separately
to the corresponding revision.

The original proofs and seven anonymous clients were developed by Formal
Frontier Agents (worker-b Hive Task
`hive-request-807aa4d70fffcd9d73f486c3fb6e8796148d8e28`, UID
`f923d027-9e1c-4025-9f69-0d3418cc6cea`). The static destination transfer
was prepared by worker-b Hive Task
`hive-request-e4ef017b9a63b331b0d19e462f22b5ec6fbe5722` (UID
`e1220436-76eb-4683-9b1c-13e67dadf037`); Atlas supplied scope and
coordinates destination acceptance. The separately reviewed origin is credited
in [CREDITS](CREDITS.md). This work imports rather than copies mathlib's native
partial/rational-map APIs (Andrew Yang), composition (Justus Springer) and
topological density tools; it copies no book prose or selected-source text.
