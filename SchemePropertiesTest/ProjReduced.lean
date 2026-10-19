/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import SchemeProperties.ProjReduced

/-!
# Reducedness of the projective line

The projective spectrum of the polynomial ring in two variables over an arbitrary
field, with its total-degree grading, is reduced.
-/

namespace SchemePropertiesTest.ProjReduced

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem projectiveLine_isReduced (K : Type u) [Field K] :
    AlgebraicGeometry.IsReduced
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) := by
  infer_instance

end SchemePropertiesTest.ProjReduced
