/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Field.Rat
import SchemeProperties.IntegralBirationalIsomorphism

/-!
# Integral isomorphisms on the rational spectrum

The integral-morphism isomorphism criterion applies to the identity of `Spec ℚ`,
whose canonical function-field map is the identity.
-/

open AlgebraicGeometry CategoryTheory

namespace SchemePropertiesTest.IntegralBirationalRationalSpectrum

private theorem rationalSpectrumIdentity_isIso :
    IsIso (𝟙 (Spec (CommRingCat.of ℚ))) := by
  haveI :
      IsIso (Scheme.Hom.toRationalMap (𝟙 (Spec (CommRingCat.of ℚ)))).functionFieldMap := by
    change IsIso (Scheme.RationalMap.id (Spec (CommRingCat.of ℚ))).functionFieldMap
    rw [Scheme.RationalMap.functionFieldMap_id]
    infer_instance
  exact Scheme.Hom.isIso_of_isIntegralHom_of_isIso_functionFieldMap (𝟙 _)

end SchemePropertiesTest.IntegralBirationalRationalSpectrum
