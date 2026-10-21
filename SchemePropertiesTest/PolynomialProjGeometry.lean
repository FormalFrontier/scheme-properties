/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.PolynomialProjGeometry
import Mathlib.Data.ZMod.Basic

/-!
# Two coordinate points over the two-element ring

The coordinate points at `0` and `1` in the polynomial projective line over `ZMod 2`
have complementary coordinate-chart memberships and are distinct. The generic
nontriviality theorem also rules out a subsingleton underlying point set.
The coefficient-ring nontriviality is obtained before using that theorem.

## References

The coordinate geometry is due to Formal Frontier Agents, using Mathlib's projective
charts and polynomial evaluation. The modular-ring formalization is by Chris Hughes.
-/

@[expose] public section

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem binaryCoordinatePoints_separated :
    (∃ p : PrimeSpectrum (ZMod 2),
      coordinatePoint (0 : Fin 2) p ∈
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2))
          (MvPolynomial.X (0 : Fin 2)) ∧
      coordinatePoint (0 : Fin 2) p ∉
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2))
          (MvPolynomial.X (1 : Fin 2)) ∧
      coordinatePoint (1 : Fin 2) p ∈
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2))
          (MvPolynomial.X (1 : Fin 2)) ∧
      coordinatePoint (1 : Fin 2) p ∉
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2))
          (MvPolynomial.X (0 : Fin 2)) ∧
      coordinatePoint (0 : Fin 2) p ≠ coordinatePoint (1 : Fin 2) p) ∧
      ¬ Subsingleton (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2))) := by
  let : Fact (1 < 2) := ⟨Nat.one_lt_two⟩
  have : Nontrivial (ZMod 2) := inferInstance
  let p : PrimeSpectrum (ZMod 2) := Classical.choice inferInstance
  constructor
  · refine ⟨p, ?_, ?_, ?_, ?_, coordinatePoint_ne _ _ _ (by decide)⟩ <;>
      simp only [coordinatePoint_mem_basicOpen_iff] <;> decide
  · let : Nontrivial (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2))) :=
      nontrivial_mvPolynomial
    intro h
    obtain ⟨x, y, hxy⟩ := exists_pair_ne
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod 2)))
    exact hxy (h.elim x y)

end AlgebraicGeometry.Proj
