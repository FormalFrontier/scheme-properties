/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.Normal
import SchemeProperties.RationalFunctionFieldReconstruction
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# A finite dominant morphism that is not birational

The spectrum map induced by the inclusion of the real numbers into the complex
numbers is finite and dominant, with integral source and normal integral target.
Its induced map on function fields is not an isomorphism: the inclusion misses
`Complex.I`. Compatibility with the canonical maps from the generic stalk spectra
connects this obstruction to the induced function-field map.

## References

* Mathlib: complex numbers as a finite-dimensional real vector space, the affine
  spectrum dictionaries, and the closed-point stalk isomorphism for a local ring.
* Scheme Properties, `RationalFunctionFieldReconstruction`: compatibility of the
  function-field map with the maps from generic stalk spectra.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace SchemePropertiesTest.IntegralBirationalIsomorphismBoundary

private def complexToReal : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℝ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))

private instance complexToReal_isFinite : IsFinite complexToReal := by
  apply (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap ℝ ℂ))).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

private instance complexToReal_isDominant : IsDominant complexToReal := by
  rw [isDominant_iff]
  change DenseRange (PrimeSpectrum.comap (algebraMap ℝ ℂ))
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap ℝ ℂ)).mpr
  rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℝ ℂ)).mp
    Complex.ofReal_injective]
  exact bot_le

private theorem complexToReal_boundary :
    IsIntegral (Spec (CommRingCat.of ℂ)) ∧
    IsIntegral (Spec (CommRingCat.of ℝ)) ∧
    IsNormal (Spec (CommRingCat.of ℝ)) ∧
    IsFinite complexToReal ∧ IsIntegralHom complexToReal ∧
    IsDominant complexToReal ∧
    ¬ IsIso complexToReal.toRationalMap.functionFieldMap ∧
    ¬ IsIso complexToReal := by
  have hnotIso : ¬ IsIso complexToReal := by
    intro h
    have hsurj : Function.Surjective (algebraMap ℝ ℂ) :=
      ((isIso_SpecMap_iff (f := CommRingCat.ofHom (algebraMap ℝ ℂ))).mp h).2
    obtain ⟨r, hr⟩ := hsurj Complex.I
    change (r : ℂ) = Complex.I at hr
    have him : (0 : ℝ) = 1 := by
      simpa only [Complex.ofReal_im, Complex.I_im] using congrArg Complex.im hr
    exact zero_ne_one him
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, hnotIso⟩
  intro hfield
  letI := hfield
  -- These isomorphisms come from the local-ring stalk dictionary, not topology alone.
  haveI : IsIso ((Spec (CommRingCat.of ℂ)).fromSpecStalk
      (genericPoint (Spec (CommRingCat.of ℂ)))) := by
    have hpoint : genericPoint (Spec (CommRingCat.of ℂ)) =
        closedPoint (CommRingCat.of ℂ) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      change (⊥ : Ideal ℂ) = maximalIdeal ℂ
      exact maximalIdeal_eq_bot.symm
    rw [hpoint, ← AlgebraicGeometry.Spec_stalkClosedPointIso]
    infer_instance
  haveI : IsIso ((Spec (CommRingCat.of ℝ)).fromSpecStalk
      (genericPoint (Spec (CommRingCat.of ℝ)))) := by
    have hpoint : genericPoint (Spec (CommRingCat.of ℝ)) =
        closedPoint (CommRingCat.of ℝ) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      change (⊥ : Ideal ℝ) = maximalIdeal ℝ
      exact maximalIdeal_eq_bot.symm
    rw [hpoint, ← AlgebraicGeometry.Spec_stalkClosedPointIso]
    infer_instance
  have hcompat := Scheme.RationalMap.functionFieldMap_compatible
    complexToReal (𝟙 (Spec (CommRingCat.of ℝ))) complexToReal.toRationalMap (by
      change (complexToReal.toPartialMap.compHom (𝟙 _)).toRationalMap = _
      rw [Scheme.PartialMap.compHom_id])
  have htriangle :
      (Spec (CommRingCat.of ℂ)).fromSpecStalk
          (genericPoint (Spec (CommRingCat.of ℂ))) ≫ complexToReal =
        Spec.map complexToReal.toRationalMap.functionFieldMap ≫
          (Spec (CommRingCat.of ℝ)).fromSpecStalk
            (genericPoint (Spec (CommRingCat.of ℝ))) := by
    simpa only [Category.comp_id] using hcompat.symm
  exact hnotIso (IsIso.of_isIso_fac_left htriangle)

end SchemePropertiesTest.IntegralBirationalIsomorphismBoundary
