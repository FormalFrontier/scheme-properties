/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Ring.PUnit
import SchemeProperties.NormalPolynomial

/-!
# Locally normal polynomial rings

The general multivariate polynomial instance applies to countably many variables over
`ℚ`. It also applies over the zero ring, whose prime spectrum is empty.
-/

namespace SchemePropertiesTest.NormalPolynomial

private theorem rational_polynomialRing : IsLocallyNormalRing (MvPolynomial ℕ ℚ) := by
  exact MvPolynomial.isLocallyNormalRing (R := ℚ) (ι := ℕ)

private theorem zero_polynomialRing : IsLocallyNormalRing (MvPolynomial ℕ PUnit) := by
  let _ : IsLocallyNormalRing PUnit :=
    ⟨fun p ↦ isEmptyElim p, fun p ↦ isEmptyElim p⟩
  exact MvPolynomial.isLocallyNormalRing (R := PUnit) (ι := ℕ)

end SchemePropertiesTest.NormalPolynomial
