/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.GeometricallyIntegral
public import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# A relative square of the affine line

The base is the spectrum of the polynomial ring in countably many variables over `ℚ`.
Its domain instance gives integrality of the base; no locally Noetherian hypothesis is used.
Smoothness of the affine-line projection supplies flatness and universal openness, so the
relative square is geometrically integral and has integral total space.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.AffineSpace

/-- The product of two affine lines over the spectrum of `MvPolynomial ℕ ℚ` is geometrically
integral over the base, and its total space is integral. -/
theorem geometricallyIntegral_and_isIntegral_rat_mvPolynomial_square :
    let S := Spec (CommRingCat.of (MvPolynomial ℕ ℚ))
    let L : Over S := Over.mk (𝔸(Fin 1; S) ↘ S)
    GeometricallyIntegral (L ⊗ L).hom ∧ IsIntegral (L ⊗ L).left := by
  let S := Spec (CommRingCat.of (MvPolynomial ℕ ℚ))
  let L : Over S := Over.mk (𝔸(Fin 1; S) ↘ S)
  change GeometricallyIntegral (L ⊗ L).hom ∧ IsIntegral (L ⊗ L).left
  have : IsIntegral S := by infer_instance
  have : Smooth L.hom := by
    have : MorphismProperty.RespectsIso @Smooth := by
      rw [HasRingHomProperty.eq_affineLocally @Smooth]
      exact affineLocally_respectsIso _ RingHom.Smooth.respectsIso
    change Smooth (𝔸(Fin 1; S) ↘ S)
    rw [← MorphismProperty.cancel_left_of_respectsIso @Smooth
        (SpecIso (Fin 1) (CommRingCat.of (MvPolynomial ℕ ℚ))).inv,
      SpecIso_inv_over, HasRingHomProperty.Spec_iff (P := @Smooth)]
    change (algebraMap (MvPolynomial ℕ ℚ)
      (MvPolynomial (Fin 1) (MvPolynomial ℕ ℚ))).Smooth
    exact RingHom.smooth_algebraMap.mpr inferInstance
  have : GeometricallyIntegral L.hom := by
    change GeometricallyIntegral (𝔸(Fin 1; S) ↘ S)
    infer_instance
  have : IsIntegral L.left :=
    GeometricallyIntegral.isIntegral_of_flat_of_universallyOpen L.hom
  refine ⟨GeometricallyIntegral.tensorObj_of_flat_of_universallyOpen L L, ?_⟩
  change IsIntegral (pullback L.hom L.hom)
  exact GeometricallyIntegral.isIntegral_pullback_of_flat_of_universallyOpen L.hom L.hom

end AlgebraicGeometry.AffineSpace
