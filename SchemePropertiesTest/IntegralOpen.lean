/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.Integral
import Mathlib.Algebra.Field.ZMod

/-!
# Integral open subschemes of a reducible spectrum

The spectrum of a product of two fields is reduced but not integral. The integral-open
existence theorem applies to this original spectrum, and the canonical inclusion has
exactly the selected original open as its image.
-/

open AlgebraicGeometry TopologicalSpace

-- The ambient scheme is not integral, even though it has a nonempty integral open.
example :
    ¬ IsIntegral (Spec (CommRingCat.of (ZMod 2 × ZMod 2))) ∧
      ∃ U : (Spec (CommRingCat.of (ZMod 2 × ZMod 2))).Opens,
        (U : Set (Spec (CommRingCat.of (ZMod 2 × ZMod 2)))).Nonempty ∧
          IsIntegral U.toScheme ∧
            Set.range U.ι = (U : Set (Spec (CommRingCat.of (ZMod 2 × ZMod 2)))) := by
  constructor
  · intro h
    let : IsDomain (ZMod 2 × ZMod 2) := (affine_isIntegral_iff _).mp h
    exact false_of_nontrivial_of_product_domain (ZMod 2) (ZMod 2)
  · obtain ⟨U, hU, hIntegral⟩ :=
      Scheme.exists_nonempty_isIntegral_open_of_noetherianSpace
        (Spec (CommRingCat.of (ZMod 2 × ZMod 2)))
    exact ⟨U, hU, hIntegral, U.range_ι⟩
