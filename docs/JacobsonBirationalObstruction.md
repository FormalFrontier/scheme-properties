# Jacobson birational obstruction

Import `SchemeProperties.JacobsonBirationalObstruction` directly (or import
`SchemeProperties`). The module provides four independent geometric statements
in `AlgebraicGeometry.Scheme` for schemes in the same universe:

- `PartialIso.subsingleton_target`: if `[Subsingleton X]` and
  `[JacobsonSpace Y]`, any `p : X.PartialIso Y` gives `Subsingleton Y`,
  including the empty source case.
- `not_birational_of_subsingleton_of_jacobson`: adding `[Nontrivial Y]`
  excludes `Birational X Y`, mathlib's `Nonempty (PartialIso X Y)`.
- `nontrivial_spec_polynomial`: for every field `k`, the underlying space of
  `Spec (CommRingCat.of k[X])` has at least two points. This is proved using
  `PrimeSpectrum.subsingleton_iff_isField_of_isReduced` and
  `Polynomial.not_isField`, not assumed.
- `not_birational_spec_field_spec_polynomial`: for arbitrary fields `K` and
  `k` in the same universe, `Spec (CommRingCat.of K)` is not birational to
  `Spec (CommRingCat.of k[X])`, including when the fields are finite.

The proof transfers subsingletonness from the source open to the target open
through the partial isomorphism's homeomorphism. The target is a locally
closed, preirreducible set with finite image under the identity map. Mathlib's
`subsingleton_image_closure_of_finite_of_isPreirreducible` in a Jacobson space
shows that its closure is subsingleton; density makes this closure all of `Y`.
The general obstruction assumes no integrality, irreducibility, reducedness,
Noetherianity, finite type, nonemptiness or infinite-field hypothesis. For the
polynomial case, a reduced polynomial ring cannot be a field, and the
polynomial Jacobson instance provides the target hypothesis.

The direct-import [client](../Test/JacobsonBirationalObstructionClient.lean)
uses namespace `SchemePropertiesTest.JacobsonBirationalObstruction` and
contains only private declarations: the general result, `K = RatFunc ℚ`
with `k = ℚ`, `K = k = ZMod 2`, an empty-source obstruction, and a positive
identity `PartialIso` of a field spectrum.

To reproduce with the pinned `leanprover/lean4:v4.34.0-rc2`, mathlib4
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and the exact official
private dependency revisions in the project manifest (access required):

```sh
lake exe cache get
lake build SchemeProperties.JacobsonBirationalObstruction
lake build Test.JacobsonBirationalObstructionClient
```

This module establishes **only geometric non-birationality**. It does not
prove the canonical generic inclusion's function-field-map `IsIso`, failure
of the source structure map's local finite type, a specified native rational
arrow's non-`IsIso`, a full function-field criterion or source coverage. A
native categorical rational-map inverse is not identified here with a
`Scheme.PartialIso`.

At the September 30, 2026 transfer-preparation snapshot, the isolated donor
had independent review and acceptance, and the destination's preceding
geometric release was already verified. Destination-specific checks, fresh
review, acceptance and separate official publication of *this addition*
remain distinct; this dated snapshot is not a later current verdict.
Original proof author: worker-b Hive Task
`hive-request-b9bc0adfa7b6a92259e85b615edfd85f75296b73` (UID
`ab7408f2-a4e4-40b7-b790-558218bc29bf`); independent original reviewer:
worker-a Task `hive-request-28ab9d8a82363aad56f39f187950fff9bba27d1c`
(UID `f26cd7a3-a683-4523-baae-d9793a089478`). Destination adaptation:
worker-b Task `hive-request-15da982db8ae147e73865a711744772b196448d7`
(UID `42176d07-1a49-48ee-9763-d3227be0a1f1`). The project code is
Apache-2.0 and retains its collective author notice. It imports rather
than copies mathlib's birational API by Justus Springer, Jacobson topology
and reduced-spectrum results by Andrew Yang, and polynomial Jacobson
instance work by Devon Tuma and other contributors; see [Credits](CREDITS.md).
