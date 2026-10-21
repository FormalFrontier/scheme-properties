/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.HomogeneousLocalizationReduced
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Reduced projective spectra

The homogeneous localization of a reduced graded ring is reduced: its canonical
map into the ordinary localization is injective. Consequently, the stalks of
`Proj` are reduced, and so is `Proj` itself. No nonemptiness or finiteness
assumption is needed.

## References

The proof uses Graded Rings' `HomogeneousLocalization.isReduced`, together with
Mathlib's `AlgebraicGeometry.Proj.stalkIso'` and
`AlgebraicGeometry.isReduced_of_isReduced_stalk`.
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry.Proj

/-- The projective spectrum of a reduced naturally graded ring is reduced,
including when its projective spectrum is empty. -/
instance isReduced {A : Type u} {σ : Type v}
    [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] [_root_.IsReduced A] :
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.Proj 𝒜) := by
  let : ∀ x : AlgebraicGeometry.Proj 𝒜,
      _root_.IsReduced ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x) := fun x ↦
    _root_.isReduced_of_injective (stalkIso' 𝒜 x).toRingHom (stalkIso' 𝒜 x).injective
  exact isReduced_of_isReduced_stalk (AlgebraicGeometry.Proj 𝒜)

end AlgebraicGeometry.Proj
