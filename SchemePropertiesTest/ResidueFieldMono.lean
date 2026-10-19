/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Field.ZMod

/-!
# Residue fields of the closed point modulo two

The integer cast onto `ZMod 2` induces a closed immersion
`Spec (ZMod 2) ⟶ Spec ℤ`. At its source's closed point, the canonical residue-field
map is an isomorphism by the monomorphism theorem. Its monomorphism property
comes from surjectivity of the integer cast, not from a hypothesis on the model.

This example does not rely on a scheme retraction: any reverse scheme map would
induce a unital ring map `ZMod 2 → ℤ`, contradicting `2 ≠ 0` in the integers.
The residue-field assertion does not assert an isomorphism of the whole schemes.

## References

* Mathlib's closed-immersion API, by Amelia Livingston, Christian Merten and
  Jonas van der Schaaf.
* Mathlib's integer-cast, `ZMod` field and local-ring closed-point APIs, by
  Chris Hughes and their respective contributors.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

/-- The quotient-spectrum morphism induced by integer cast modulo two. -/
private noncomputable abbrev modTwoClosedPoint :
    Spec (CommRingCat.of (ZMod 2)) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod 2)))

private instance modTwoClosedPoint_isClosedImmersion : IsClosedImmersion modTwoClosedPoint :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Int.castRingHom (ZMod 2))) (by
      change Function.Surjective (Int.castRingHom (ZMod 2))
      exact ZMod.intCast_surjective)

/-- The canonical map `κ((2)) ⟶ 𝔽₂` at the closed point of the quotient spectrum
is an isomorphism. -/
private theorem isIso_residueFieldMap_modTwoClosedPoint :
    IsIso (modTwoClosedPoint.residueFieldMap (IsLocalRing.closedPoint (ZMod 2))) :=
  Scheme.Hom.isIso_residueFieldMap_of_mono modTwoClosedPoint _

end AlgebraicGeometry
