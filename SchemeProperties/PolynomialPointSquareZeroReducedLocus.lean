/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ReducedLocusEquiv
public import SchemeProperties.PolynomialPointReducedLocus
public import MultivariatePolynomials.PointSquareZeroQuotient

@[expose] public section

set_option warningAsError true

/-!
# Reduced prime localizations of polynomial point quotients

For a separated family of points over a field, the full reduced
prime-localization locus of the polynomial quotient is open precisely when the
point family has finite image. The quotient presentation imposes only the
squares and point-linear relations on its generators.

## References

* R. Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, Remark 5.2.2,
  for the motivating non-open reduced-locus phenomenon; no identification with
  its particular ring is asserted here.
* Mathlib's prime-localization and spectrum APIs.
* Multivariate Polynomials' polynomial point-quotient equivalence.
-/

open scoped TrivSqZeroExt

namespace MvPolynomial

universe uK uι

section

/-- For an injective family of field-valued points, the reduced-localization
locus at *all* primes of the polynomial point quotient is open exactly when the
image of the family is finite. Injectivity supplies pairwise unit differences
for the canonical square-zero presentation; this does not classify families
without that separation property. -/
theorem isOpen_reduced_atPrime_pointSquareZeroQuotient_iff_finite_range
    {K : Type uK} [Field K] {ι : Type uι} (a : ι → K)
    (ha : Function.Injective a) :
    IsOpen {p : PrimeSpectrum (MvPolynomial.pointSquareZeroQuotient a) |
      _root_.IsReduced (Localization.AtPrime p.asIdeal)} ↔
      (Set.range a).Finite := by
  have hsep : ∀ i j : ι, i ≠ j → IsUnit (a i - a j) := by
    intro i j hij
    exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun h => hij (ha h)))
  exact (PrimeSpectrum.isOpen_isReduced_atPrime_iff_ringEquiv
    (pointSquareZeroAlgEquiv a hsep).toRingEquiv).trans
      (Polynomial.isOpen_reduced_atPrime_directSum_evalQuotient_iff_finite_range a)

end

end MvPolynomial
