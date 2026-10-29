/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.MaximalPointSpace

/-!
# Boundary checks for maximal-point spaces

Global coordinates remain injective without any reducedness assumption.
The subsingleton-ring case and the empty principal open need no nonemptiness
hypothesis.
-/

@[expose] public section

noncomputable section

universe u

open TopologicalSpace Opposite AlgebraicGeometry.Spec

namespace SchemePropertiesTest.MaximalPointSpace

variable (R : Type u) [CommRing R] [IsJacobsonRing R]

example (r : R) (h : maximalPointCoordinates R r = 0) : r = 0 :=
  (maximalPointCoordinates R).injective (by simpa only [map_zero] using h)

example [Subsingleton R] : Subsingleton ((maximalPointSpace R).presheaf.obj (op ⊤)) :=
  (maximalPointCoordinates R).symm.injective.subsingleton

example : maximalPointBasicOpen R (0 : R) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  exact False.elim ((mem_maximalPointBasicOpen R 0 x).mp hx x.val.asIdeal.zero_mem)

end SchemePropertiesTest.MaximalPointSpace
