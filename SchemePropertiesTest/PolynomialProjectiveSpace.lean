/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.PolynomialProjectiveSpace
import Mathlib.Algebra.Field.ZMod

/-!
# A coordinate chart in the polynomial projective line

Over the two-element field, a coefficient prime gives a point of the first coordinate
chart in `PolynomialProjectiveSpace (ZMod 2) 1`. The chart witness uses the coordinate
morphism and its point formula. A second example obtains a point from nonemptiness,
uses the integral-space instance, and deduces surjectivity of the coefficient morphism
from its full scheme-morphism section identity.

## References

The field and domain structures on `ZMod 2` use Chris Hughes's Mathlib formalization.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.PolynomialProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem binaryProjectiveLine_domain_coordinateChart :
    IsDomain (ZMod 2) ∧
      Nonempty ↥(Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2))
        (MvPolynomial.X (0 : Fin 2))) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let p : PrimeSpectrum (ZMod 2) := Classical.choice inferInstance
  let x : PolynomialProjectiveSpace (ZMod 2) 1 := coordinateSection (ZMod 2) 1 0 p
  refine ⟨inferInstance, ⟨⟨x, ?_⟩⟩⟩
  simpa only [x, coordinateSection_apply] using
    Proj.coordinatePoint_mem_basicOpen (R := ZMod 2) (0 : Fin 2) p

private theorem binaryProjectiveLine_integral_surjective :
    ∃ _ : PolynomialProjectiveSpace (ZMod 2) 1,
      IsIntegral (PolynomialProjectiveSpace (ZMod 2) 1) ∧
        Function.Surjective (toSpec (ZMod 2) 1) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x⟩ := nonempty (ZMod 2) 1
  refine ⟨x, inferInstance, ?_⟩
  intro p
  refine ⟨coordinateSection (ZMod 2) 1 0 p, ?_⟩
  have h := congrArg
    (fun f : Spec (CommRingCat.of (ZMod 2)) ⟶ Spec (CommRingCat.of (ZMod 2)) => f p)
    (coordinateSection_toSpec (ZMod 2) 1 0)
  simpa [Scheme.Hom.comp_apply] using h

end AlgebraicGeometry.PolynomialProjectiveSpace
