/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.PolynomialProjCoordinates
import Mathlib.Data.ZMod.Basic

/-!
# A coordinate chart over the two-element ring

The chart at the first variable in the polynomial projective line over `ZMod 2` is nonempty.
Its point is constructed from a coefficient prime using the coordinate-point API.

## References

The coefficient ring uses Mathlib's modular-ring formalization by Chris Hughes.
-/

@[expose] public section

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem binaryCoordinateChart_nonempty :
    Nonempty ↥(Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2))
      (MvPolynomial.X (0 : Fin 2))) := by
  let : Fact (1 < 2) := ⟨Nat.one_lt_two⟩
  let p : PrimeSpectrum (ZMod 2) := Classical.choice inferInstance
  exact ⟨⟨coordinatePoint (0 : Fin 2) p, coordinatePoint_mem_basicOpen _ _⟩⟩

private theorem binaryCoordinateAwayEval_X_div_X :
    coordinateAwayEval (R := ZMod 2) (0 : Fin 2)
        (HomogeneousLocalization.Away.mk
          (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2))
          (MvPolynomial.isHomogeneous_X (ZMod 2) (0 : Fin 2)) 1
          (MvPolynomial.X (0 : Fin 2))
          (by simpa using MvPolynomial.isHomogeneous_X (ZMod 2) (0 : Fin 2))) = 1 := by
  rw [coordinateAwayEval_mk]
  simp

end AlgebraicGeometry.Proj
