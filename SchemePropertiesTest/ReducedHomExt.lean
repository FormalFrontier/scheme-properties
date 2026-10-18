/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.ReducedHomExt
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.Algebra.DualNumber

/-!
# Reduced-source extensionality on the affine line

On `Spec ℚ[T]`, translation by `1` followed by translation by `-1` agrees
with the coordinate substitution `T ↦ T`. The field-point witness is computed
on constants and `T`, independently of either extensionality theorem. Both
criteria then recover equality of these scheme morphisms.

The ring-level dual-number boundary records a nonzero element killed by every
ring homomorphism to a field; no scheme counterexample is constructed here.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace SchemePropertiesTest.ReducedHomExt

private def affineLine : Scheme := Spec (CommRingCat.of (Polynomial ℚ))

private theorem affineLine_reduced_nonempty : IsReduced affineLine ∧ Nonempty affineLine := by
  constructor <;> dsimp [affineLine] <;> infer_instance

private def translation (a : ℚ) : affineLine ⟶ affineLine :=
  Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C a)))

private def translationRoundTrip : affineLine ⟶ affineLine :=
  translation 1 ≫ translation (-1)

private def coordinateIdentity : affineLine ⟶ affineLine :=
  Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom Polynomial.C Polynomial.X))

private theorem translation_field_points (K : Type) [Field K]
    (p : Spec (CommRingCat.of K) ⟶ affineLine) :
    p ≫ translationRoundTrip = p ≫ coordinateIdentity := by
  dsimp [affineLine, translationRoundTrip, translation, coordinateIdentity] at p ⊢
  apply Spec.preimage_injective
  simp only [Spec.preimage_comp, Spec.preimage_map]
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · -- The pulled-back coordinate is `(p⁎T + 1) - 1 = p⁎T`.
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_add, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    simp

private theorem translation_eq_of_residue_fields :
    translationRoundTrip = coordinateIdentity := by
  let : IsReduced affineLine := affineLine_reduced_nonempty.1
  exact AlgebraicGeometry.Scheme.Hom.ext_of_fromSpecResidueField
    (fun x => translation_field_points (affineLine.residueField x)
      (affineLine.fromSpecResidueField x))

private theorem translation_eq_of_all_field_points :
    translationRoundTrip = coordinateIdentity := by
  let : IsReduced affineLine := affineLine_reduced_nonempty.1
  exact AlgebraicGeometry.Scheme.Hom.ext_of_field_valued_points
    (fun K _ p => translation_field_points K p)

private theorem dualNumber_eps_ne_zero : (DualNumber.eps : DualNumber ℚ) ≠ 0 := by
  intro h
  have h' : (1 : ℚ) = 0 := by
    simpa using congrArg TrivSqZeroExt.snd h
  exact one_ne_zero h'

private theorem dualNumber_field_kills_eps (K : Type) [Field K]
    (φ : DualNumber ℚ →+* K) : φ DualNumber.eps = 0 := by
  have h : φ DualNumber.eps * φ DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  rcases mul_eq_zero.mp h with h | h <;> exact h

end SchemePropertiesTest.ReducedHomExt
