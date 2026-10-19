/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import SchemeProperties.Normal

public section

/-!
# A normal affine scheme with infinitely many polynomial variables

The polynomial ring `MvPolynomial ℕ ℚ` is locally normal, and its affine spectrum
is normal. The variable type is infinite. The ring-theoretic inputs are Mathlib's
unique factorization theorem for multivariate polynomials and its integral
closedness theorem for GCD domains.
-/

open AlgebraicGeometry

namespace SchemePropertiesTest.InfinitePolynomialRing

private theorem variables_not_finite : ¬ Finite ℕ :=
  Infinite.not_finite

private theorem isLocallyNormalRing : IsLocallyNormalRing (MvPolynomial ℕ ℚ) := by
  letI : UniqueFactorizationMonoid (MvPolynomial ℕ ℚ) :=
    MvPolynomial.uniqueFactorizationMonoid ℕ
  letI : IsIntegrallyClosed (MvPolynomial ℕ ℚ) :=
    GCDMonoid.toIsIntegrallyClosed
  exact isLocallyNormalRing_of_isDomain _

private theorem isNormal_spec : IsNormal (Spec (.of (MvPolynomial ℕ ℚ))) := by
  letI : IsLocallyNormalRing (MvPolynomial ℕ ℚ) := isLocallyNormalRing
  infer_instance

end SchemePropertiesTest.InfinitePolynomialRing
