/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.JacobsonClosedPoints
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Closed-point trace criterion for a given immersion

An immersion into a Jacobson scheme becomes a closed immersion when the trace of
its full range is closed in the closed-point subspace. The morphism and its stalk
maps are retained, with no reducedness or quasi-compactness assumption.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace SchemePropertiesTest.JacobsonClosedPoints

example {H G : Scheme.{u}} (f : H ⟶ G) [IsImmersion f] [JacobsonSpace G]
    (htrace : IsClosed ((Subtype.val : closedPoints G → G) ⁻¹' Set.range f)) :
    IsClosedImmersion f := by
  apply IsClosedImmersion.of_isPreimmersion f
  exact f.isLocallyClosed_range.isClosed_iff_isClosed_preimage_closedPoints.mpr htrace

end SchemePropertiesTest.JacobsonClosedPoints
