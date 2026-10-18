/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.AffineGenerators
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Data.ZMod.Basic

/-!
# Affine-line applications and the zero-ring boundary

The identity of `Spec ℚ[X]` illustrates strong generation, detection and the all-ring-points
criterion. Independently, evaluation at zero gives a monomorphism which misses the rational
point at one and is not an isomorphism. Evaluation of `X` proves this for every possible
factorization, without classifying endomorphisms of the rational field.

The spectrum of `ZMod 1` is empty: maps from it cannot distinguish the zero section from
an isomorphism. This explains why the criterion tests all rings rather than only the zero ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

private def affineLine : Scheme := Spec (.of (Polynomial ℚ))

private def p0 : Spec (.of ℚ) ⟶ affineLine :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℚ)))

private def p1 : Spec (.of ℚ) ⟶ affineLine :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : ℚ)))

private theorem affineLine_nonempty : Nonempty affineLine :=
  inferInstanceAs (Nonempty (PrimeSpectrum (Polynomial ℚ)))

private theorem p0_mono : Mono p0 := by
  change Mono (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℚ))))
  letI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℚ)))) :=
    IsClosedImmersion.spec_of_surjective _ (fun q => ⟨Polynomial.C q, by simp⟩)
  infer_instance

private theorem p0_misses_p1 (g : Spec (.of ℚ) ⟶ Spec (.of ℚ)) : g ≫ p0 ≠ p1 := by
  intro h
  change g ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℚ))) =
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : ℚ))) at h
  have he : CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℚ)) ≫ Spec.preimage g =
      CommRingCat.ofHom (Polynomial.evalRingHom (1 : ℚ)) := by
    simpa only [Spec.preimage_comp, Spec.preimage_map] using
      congrArg (fun f : Spec (.of ℚ) ⟶ Spec (.of (Polynomial ℚ)) => Spec.preimage f) h
  have hx := congrArg
    (fun k : CommRingCat.of (Polynomial ℚ) ⟶ CommRingCat.of ℚ => k.hom Polynomial.X) he
  have hz : (0 : ℚ) = 1 := by
    simpa [CommRingCat.hom_comp] using hx
  exact zero_ne_one hz

private theorem p0_points_not_surjective :
    ¬ Function.Surjective (fun g : Spec (.of ℚ) ⟶ Spec (.of ℚ) => g ≫ p0) := by
  intro h
  obtain ⟨g, hg⟩ := h p1
  exact p0_misses_p1 g hg

private theorem p0_not_isIso : ¬ IsIso p0 := by
  intro h
  letI : IsIso p0 := h
  exact p0_misses_p1 (p1 ≫ inv p0) (by simp [Category.assoc])

private theorem affineLine_identity_strongGenerator : IsIso (𝟙 affineLine) := by
  exact Scheme.isStrongGenerator_isAffine.isIso_of_mono (𝟙 affineLine)
    (fun G _ h => ⟨h, by simp⟩)

private theorem affineLine_identity_detecting : IsIso (𝟙 affineLine) := by
  apply Scheme.isDetecting_isAffine
  intro G _ h
  exact ⟨h, by simp, fun k hk => by simpa using hk⟩

private theorem affineLine_identity_points :
    ∀ (R : Type) [CommRing R],
      Function.Bijective (fun g : Spec (.of R) ⟶ affineLine => g ≫ 𝟙 affineLine) :=
  (Scheme.isIso_iff_bijective_spec (𝟙 affineLine)).mp (by infer_instance)

private theorem zeroRing_isEmpty : IsEmpty (Spec (.of (ZMod 1))) :=
  inferInstanceAs (IsEmpty (PrimeSpectrum (ZMod 1)))

private theorem zeroRing_identity : IsIso (𝟙 (Spec (.of (ZMod 1)))) := by
  apply (Scheme.isIso_iff_bijective_spec _).mpr
  intro R _
  constructor
  · intro a b h
    simpa only [Category.comp_id] using h
  · intro b
    exact ⟨b, Category.comp_id b⟩

private theorem zeroRing_points_zeroSection_bijective :
    Function.Bijective (fun g : Spec (.of (ZMod 1)) ⟶ Spec (.of ℚ) => g ≫ p0) := by
  letI : IsEmpty (Spec (.of (ZMod 1))) := zeroRing_isEmpty
  have h := isInitialOfIsEmpty (X := Spec (.of (ZMod 1)))
  constructor
  · intro a b _
    exact h.hom_ext a b
  · intro b
    exact ⟨h.to _, h.hom_ext _ _⟩
