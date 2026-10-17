/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.LocallyNormalRing.Product
import Mathlib.Algebra.Ring.PUnit
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Normality of a disconnected affine scheme

The spectrum of `ℤ × ℤ` is normal by the product instance, even though its
coordinate ring is not a domain. A zero-ring factor is also allowed.
-/

@[expose] public section

open AlgebraicGeometry

private theorem normal_int_prod_spectrum : IsNormal (Spec (CommRingCat.of (ℤ × ℤ))) := by
  infer_instance

private theorem locallyNormal_int_prod_zero : IsLocallyNormalRing (ℤ × PUnit) := by
  let _ : IsLocallyNormalRing PUnit :=
    ⟨fun p ↦ isEmptyElim p, fun p ↦ isEmptyElim p⟩
  infer_instance
