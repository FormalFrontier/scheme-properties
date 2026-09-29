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
deliberately not unrestricted: an empty source or reducible target obstructs
the converse, and a reducible source can obstruct the forward implication.
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
LAKE_JOBS=2 lake --wfail build SchemeProperties.DenseOpenPullbackDominance SchemePropertiesTest SchemeProperties
```

Completion evidence additionally requires a successful applicable destination
build and the full transitive axiom audit of actual origin declarations,
including private/generated ones, permitting only `propext`,
`Classical.choice` and `Quot.sound`. The separately reviewed isolated donor
`e115570b05adebd1d4b9b5f8c3cc7fbd4a1025ad` supplied the proofs and client;
its original checks and review do **not** establish destination checks,
acceptance, publication, or source coverage. Exact destination evidence and
decisions belong to the revision to which they apply.

The original converse exposition was by Hive Task
`hive-request-7cd28f4c844b22e75425fed3fe9d76930b8f1ab7` (UID
`dc65fd6d-d7e8-400b-ab99-01d2b1ae8971`), independently reviewed by Task
`hive-request-c83093c0267bb0c99bc85cd4fc3a8bb3bfadb402` (UID
`123f5562-d5c1-4e9f-8f74-f23d9e9fffaa`); mathematical review does not
establish source correspondence. The donor Lean implementation is by Task
`hive-request-79825c8e94f5352c8e75fb6a16c1859618eef289` (UID
`6a8d0c63-9b1a-4eca-b111-4b8898be6498`) with fresh donor code review by
Task `hive-request-32455516cc0f7e39cda54d2b9f621859bff7af3c` (UID
`11d896b5-c1ad-42a3-8fb6-45158421d024`). This destination transfer is
by Task `hive-request-ce06b62b5f59999150c88d30d70f9d878166052a`
(UID `ddece77d-7c0f-4a45-bb62-e8028d116843`); separate destination review
and responsible-maintainer acceptance are revision-specific.

The imported mathlib native dominance and composition APIs are by **Justus
Springer** (2026, Apache-2.0); native partial/rational quotient and
representative APIs are by **Andrew Yang** (2024, Apache-2.0). Their proof
bodies are not copied, and no source-specific correspondence is necessary to
use these theorems.
