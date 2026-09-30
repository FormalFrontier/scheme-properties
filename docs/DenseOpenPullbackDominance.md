<!-- SPDX-License-Identifier: Apache-2.0 -->

# Dense-open pullback and dominance

Import `SchemeProperties.DenseOpenPullbackDominance` directly or use the
`SchemeProperties` aggregate root. Its
[ordinary-import client](../Test/DenseOpenPullbackDominanceClient.lean) checks
four private generic examples; neither file introduces a new map type, instance,
or exceptional-scheme fixture. This companion extends the
[dense-open pullback predicate](DenseOpenPullback.md) on mathlib's native
same-universe partial and rational maps.

For `f : X.PartialMap Y`, `f.PullsDenseOpens` means that for **every** dense open
`V : Y.Opens`, the inverse image under `f.hom`, transported along the inclusion
of `f.domain`, is dense in the **whole source scheme `X`**, not merely in
`f.domain`. For `r : X ⤏ Y`, `r.PullsDenseOpens` is the existing
representative-independent rational-map predicate.

## API and hypotheses

All four declarations lie in `AlgebraicGeometry.Scheme`:

| Declaration | Exact assumptions and conclusion |
| --- | --- |
| `PartialMap.isDominant_of_pullsDenseOpens f hf` | `[Nonempty X] [PreirreducibleSpace Y]` and `hf : f.PullsDenseOpens` give `IsDominant f.hom`. |
| `RationalMap.isDominant_of_pullsDenseOpens r hr` | `[Nonempty X] [PreirreducibleSpace Y]` and `hr : r.PullsDenseOpens` give `r.IsDominant`. |
| `PartialMap.pullsDenseOpens_iff_isDominant f` | `[PreirreducibleSpace X] [Nonempty X] [PreirreducibleSpace Y] [Nonempty Y]` give `f.PullsDenseOpens ↔ IsDominant f.hom`. |
| `RationalMap.pullsDenseOpens_iff_isDominant r` | The same four hypotheses give `r.PullsDenseOpens ↔ r.IsDominant`. |

For the converse, every nonempty target open is dense because `Y` is
preirreducible. Its dense pullback has a point because `X` is nonempty; the
pulled-back point carries an **actual domain-point witness**, whose image
lies in the given target open. Thus the underlying morphism has dense range.
The rational-map result uses an **arbitrary** representative via the existing
`PartialMap.pullsDenseOpens_toRationalMap_iff` and native
`PartialMap.isDominant_toRationalMap_iff` bridges.

The **dominance-to-pullback** direction of each iff reuses the predicate
module's previously established `PartialMap.pullsDenseOpens_of_isDominant`
and quotient transport, retaining that result's `[Nonempty Y]` premise.
Neither converse needs source preirreducibility or target nonemptiness; neither
requires reducedness, integrality or an open underlying morphism. The iff is
deliberately not unrestricted: an empty source or reducible target can obstruct
pullback-to-dominance, while a reducible source can obstruct
dominance-to-pullback.
These boundaries are not new compiled counterexamples.

## Reproduction and provenance

The [pinned toolchain](../lean-toolchain) is `leanprover/lean4:v4.34.0-rc2`;
the [Lake requirements](../lakefile.toml) and
[manifest](../lake-manifest.json) pin mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and exact official
private-GitHub `coherent-modules` and `finite-etale-algebras` releases.
Authorized access to those private dependencies is needed. With the pinned
toolchain installed, fetch the matching precompiled mathlib cache **successfully
before** building a fresh checkout, or after changing pins/removing `.lake`:

```sh
lake exe cache get
lake --wfail build SchemeProperties.DenseOpenPullbackDominance SchemePropertiesTest SchemeProperties
```

The proofs use imported mathlib dominance and composition by Justus
Springer and partial/rational-map quotients by Andrew Yang. Their original
notices remain upstream; see [Credits](CREDITS.md).
