/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.MaximalPointHom
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.DualNumber

/-!
# Full-map and scalar checks for ringed maximal-point morphisms

Polynomial evaluation over the dual numbers uses the scalar locality endpoint
over a nonfield with the given algebra actions. Identity and projection to
constants on the dual numbers have the same point map but distinct full
ringed morphisms, detected by coordinate recovery on the nonzero square-zero
element. Its square vanishes by `DualNumber.eps_pow_two`.

The empty-open and zero-ring coordinate controls are in
`SchemePropertiesTest.MaximalPointSpace`.
-/

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Spec

namespace SchemePropertiesTest.MaximalPointRingedHom

private instance : Algebra.FiniteType ℚ (DualNumber ℚ) := by
  refine Algebra.FiniteType.of_surjective (Polynomial.aeval (DualNumber.eps : DualNumber ℚ)) ?_
  intro x
  refine ⟨Polynomial.C x.fst + Polynomial.C x.snd * Polynomial.X, ?_⟩
  apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

private instance : IsJacobsonRing (DualNumber ℚ) := isJacobsonRing_of_finiteType (A := ℚ)

private def evaluation : Polynomial (DualNumber ℚ) →ₐ[DualNumber ℚ] DualNumber ℚ :=
  Polynomial.aeval 0

private def evaluationRinged :
    (maximalPointSpace (DualNumber ℚ)).toRingedSpace ⟶
      (maximalPointSpace (Polynomial (DualNumber ℚ))).toRingedSpace :=
  (maximalPointMapOfAlgHom evaluation).toShHom

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_scalars :
    (evaluationRinged.hom.c.app (op ⊤)).hom.comp
        (maximalPointScalars (Polynomial (DualNumber ℚ))
          (algebraMap (DualNumber ℚ) (Polynomial (DualNumber ℚ)))) =
      maximalPointScalars (DualNumber ℚ) (algebraMap (DualNumber ℚ) (DualNumber ℚ)) := by
  have hρ : maximalPointRingedHomCoordinates evaluationRinged = evaluation.toRingHom := by
    dsimp only [evaluationRinged]
    rw [maximalPointMapOfAlgHom_eq, maximalPointRingedHomCoordinates_map]
  apply RingHom.ext
  intro k
  calc
    _ = maximalPointCoordinates (DualNumber ℚ)
        (maximalPointRingedHomCoordinates evaluationRinged
          (algebraMap (DualNumber ℚ) (Polynomial (DualNumber ℚ)) k)) :=
      maximalPointRingedHomCoordinates_apply evaluationRinged _
    _ = _ := by
      rw [hρ]
      exact congrArg (maximalPointCoordinates (DualNumber ℚ)) (evaluation.commutes k)

-- The same full morphism acquires locality over the given nonfield scalars,
-- and its original coordinate homomorphism still kills the polynomial variable.
set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_lift_kills_variable :
    maximalPointRingHom
        (maximalPointRingedHomLiftOfScalars evaluationRinged evaluation_scalars)
        Polynomial.X = 0 := by
  rw [← maximalPointRingedHomCoordinates_toShHom,
    maximalPointRingedHomLiftOfScalars_toShHom]
  dsimp only [evaluationRinged]
  rw [maximalPointMapOfAlgHom_eq, maximalPointRingedHomCoordinates_map]
  exact Polynomial.aeval_X (0 : DualNumber ℚ)

private def dualProjection : DualNumber ℚ →ₐ[ℚ] DualNumber ℚ :=
  (TrivSqZeroExt.inlAlgHom ℚ ℚ ℚ).comp (TrivSqZeroExt.fstHom ℚ ℚ ℚ)

private def dualIdentityRinged :=
  (maximalPointMapOfAlgHom (AlgHom.id ℚ (DualNumber ℚ))).toShHom

private def dualProjectionRinged := (maximalPointMapOfAlgHom dualProjection).toShHom

private theorem dual_same_points (x : maximalPointSpace (DualNumber ℚ)) :
    dualIdentityRinged.hom.base x = dualProjectionRinged.hom.base x := by
  apply Subtype.ext
  apply PrimeSpectrum.ext
  exact (IsLocalRing.eq_maximalIdeal (inferInstance :
    (dualIdentityRinged.hom.base x).val.asIdeal.IsMaximal)).trans
      (IsLocalRing.eq_maximalIdeal (inferInstance :
        (dualProjectionRinged.hom.base x).val.asIdeal.IsMaximal)).symm

-- Full morphisms, unlike their point maps, distinguish the nilpotent.
private theorem dual_different_full_morphisms : dualIdentityRinged ≠ dualProjectionRinged := by
  intro h
  have hc := congrArg maximalPointRingedHomCoordinates h
  have he := RingHom.congr_fun hc (DualNumber.eps : DualNumber ℚ)
  have hread (φ : DualNumber ℚ →ₐ[ℚ] DualNumber ℚ) :
      maximalPointRingedHomCoordinates (maximalPointMapOfAlgHom φ).toShHom = φ.toRingHom :=
    maximalPointRingedHomCoordinates_map φ.toRingHom (maximal_comap_of_algHom φ)
  dsimp only [dualIdentityRinged, dualProjectionRinged] at he
  rw [hread, hread] at he
  have hz : (DualNumber.eps : DualNumber ℚ) = 0 := he
  have h10 : (1 : ℚ) = 0 := congrArg TrivSqZeroExt.snd hz
  exact one_ne_zero h10

end SchemePropertiesTest.MaximalPointRingedHom
