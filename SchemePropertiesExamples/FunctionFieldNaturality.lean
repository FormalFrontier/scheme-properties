/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RationalFunctionFieldNaturality
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

/-!
# Function-field naturality for the affine line over the rationals

The coefficient inclusion from `ℚ` to `ℚ[X]` induces the structure morphism
of the affine line. Evaluation at zero splits this inclusion, so the structure
morphism is dominant independently of function-field naturality.
-/

set_option warningAsError true

open CategoryTheory AlgebraicGeometry

namespace SchemePropertiesExamples.FunctionFieldNaturality

/-- The structure morphism of the affine line over the rationals. -/
noncomputable def coefficientProjection :
    Spec (CommRingCat.of (Polynomial ℚ)) ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ))

instance coefficientProjection_isDominant : IsDominant coefficientProjection := by
  have hsplit :
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℚ))) ≫
        coefficientProjection = 𝟙 (Spec (CommRingCat.of ℚ)) := by
    unfold coefficientProjection
    rw [← Spec.map_comp]
    have h : CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℚ)) = 𝟙 (CommRingCat.of ℚ) := by
      ext
      simp
    rw [h, Spec.map_id]
  have : IsDominant
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℚ))) ≫
        coefficientProjection) := by
    rw [hsplit]
    infer_instance
  exact IsDominant.of_comp
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℚ)))) coefficientProjection

/-- Every nonempty open of the base has nonempty inverse image on the affine line. -/
theorem coefficient_preimage_nonempty (U : (Spec (CommRingCat.of ℚ)).Opens)
    [Nonempty U] : Nonempty (coefficientProjection ⁻¹ᵁ U) :=
  coefficientProjection.nonempty_preimage_of_isDominant U

attribute [local instance] coefficient_preimage_nonempty

/-- Generic germs of pulled-back rational-base sections are given by the induced
function-field homomorphism. -/
theorem coefficient_app_germ (U : (Spec (CommRingCat.of ℚ)).Opens) [Nonempty U] :
    coefficientProjection.app U ≫
        (Spec (CommRingCat.of (Polynomial ℚ))).germToFunctionField
          (coefficientProjection ⁻¹ᵁ U) =
      (Spec (CommRingCat.of ℚ)).germToFunctionField U ≫
        coefficientProjection.toRationalMap.functionFieldMap :=
  coefficientProjection.app_germToFunctionField U

end SchemePropertiesExamples.FunctionFieldNaturality
