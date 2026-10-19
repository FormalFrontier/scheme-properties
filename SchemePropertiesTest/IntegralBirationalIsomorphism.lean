/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Field.Rat
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import SchemeProperties.Normal
import SchemeProperties.RationalFunctionFieldPullback

/-!
# The identity of the rational spectrum

The identity of `Spec ℚ` is an integral dominant morphism between integral normal
schemes. Its canonical function-field map and the scheme morphism itself are
isomorphisms, by the corresponding identity laws. This example uses the spectrum,
normality and function-field APIs independently of the integral-morphism
isomorphism criterion.

All declarations in this module are private.
-/

open AlgebraicGeometry CategoryTheory

namespace SchemePropertiesTest.IntegralBirationalIsomorphism

/-- The identity morphism of the spectrum of the rational field. -/
private noncomputable abbrev rationalSpectrumIdentity :
    Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of ℚ) :=
  𝟙 _

/-- The integral normal spectrum and all morphism properties of its identity,
including invertibility of its canonical function-field map. -/
private theorem rationalSpectrumIdentity_properties :
    IsIntegral (Spec (CommRingCat.of ℚ)) ∧
    IsNormal (Spec (CommRingCat.of ℚ)) ∧
    IsIntegralHom rationalSpectrumIdentity ∧
    IsDominant rationalSpectrumIdentity ∧
    IsIso rationalSpectrumIdentity.toRationalMap.functionFieldMap ∧
    IsIso rationalSpectrumIdentity := by
  have hfield : IsIso rationalSpectrumIdentity.toRationalMap.functionFieldMap := by
    change IsIso (Scheme.RationalMap.id (Spec (CommRingCat.of ℚ))).functionFieldMap
    rw [Scheme.RationalMap.functionFieldMap_id]
    infer_instance
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, hfield, inferInstance⟩

end SchemePropertiesTest.IntegralBirationalIsomorphism
