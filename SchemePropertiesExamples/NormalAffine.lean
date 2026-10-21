/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Normal
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Normality of the integer spectrum and a distinguished open

The integers are an integrally closed domain, so their spectrum is normal.
The distinguished open `D(2)` is affine and normal. It contains the generic
point but omits the prime ideal `(2)`, so it is nonempty and a strict open subset.
The empty spectrum of the zero ring `PUnit` supplies the boundary case.

## References

* `SchemeProperties.Normal` for local normality, normal spectra, and restriction.
* Mathlib's `Algebra.EuclideanDomain.Int`, `RingTheory.PrincipalIdealDomain`, and
  `RingTheory.Polynomial.RationalRoot` for integral closedness of the integers.
* Mathlib's `AlgebraicGeometry.AffineScheme` and `RingTheory.Spectrum.Prime` for
  distinguished affine opens and the prime-spectrum witnesses.
-/

noncomputable section

namespace AlgebraicGeometry

private abbrev integerSpec : Scheme := Spec (CommRingCat.of ℤ)

private theorem integer_isDomain : IsDomain ℤ := Int.instIsDomain

private theorem integer_isIntegrallyClosed : IsIntegrallyClosed ℤ := by
  let _ : IsDomain ℤ := integer_isDomain
  let _ : IsPrincipalIdealRing ℤ := EuclideanDomain.instIsPrincipalIdealRing
  let _ : UniqueFactorizationMonoid ℤ := PrincipalIdealRing.to_uniqueFactorizationMonoid
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

private theorem integer_isLocallyNormalRing : IsLocallyNormalRing ℤ := by
  let _ : IsDomain ℤ := integer_isDomain
  let _ : IsIntegrallyClosed ℤ := integer_isIntegrallyClosed
  exact isLocallyNormalRing_of_isDomain ℤ

private theorem integerSpec_isNormal : IsNormal integerSpec := by
  let _ : IsLocallyNormalRing ℤ := integer_isLocallyNormalRing
  exact normalSpec (R := CommRingCat.of ℤ)

/-- The basic open `D(2)` in `Spec ℤ`. -/
public abbrev integerBasicOpenTwo : (Spec (CommRingCat.of ℤ)).Opens :=
  PrimeSpectrum.basicOpen (2 : ℤ)

/-- The integer open is the distinguished open defined by the constant two. -/
public theorem integerBasicOpenTwo_eq :
    integerBasicOpenTwo = PrimeSpectrum.basicOpen (2 : ℤ) := rfl

/-- Membership in `D(2)` means that two is not in the prime ideal. -/
public theorem mem_integerBasicOpenTwo (p : Spec (CommRingCat.of ℤ)) :
    p ∈ integerBasicOpenTwo ↔ (2 : ℤ) ∉ p.asIdeal :=
  PrimeSpectrum.mem_basicOpen (2 : ℤ) p

/-- The distinguished open `D(2)` in the integer spectrum is affine. -/
public theorem integerBasicOpenTwo_isAffineOpen : IsAffineOpen integerBasicOpenTwo :=
  IsAffineOpen.Spec_basicOpen (R := CommRingCat.of ℤ) (2 : ℤ)

private def integerBasicOpenTwoPoint : integerBasicOpenTwo := by
  let p : Spec (CommRingCat.of ℤ) := (⊥ : PrimeSpectrum ℤ)
  refine ⟨p, (mem_integerBasicOpenTwo p).2 ?_⟩
  simpa only [p, PrimeSpectrum.asIdeal_bot, Ideal.mem_bot] using Int.prime_two.ne_zero

/-- The generic point belongs to `D(2)`, so this open is nonempty. -/
public theorem integerBasicOpenTwo_nonempty : Nonempty integerBasicOpenTwo :=
  ⟨integerBasicOpenTwoPoint⟩

private def integerTwoPrime : PrimeSpectrum ℤ :=
  ⟨Ideal.span {(2 : ℤ)}, Ideal.isPrime_span_singleton_of_prime Int.prime_two⟩

private theorem integerTwoPrime_not_mem_basicOpenTwo :
    integerTwoPrime ∉ integerBasicOpenTwo := by
  intro hp
  exact (mem_integerBasicOpenTwo integerTwoPrime).mp hp
    (Ideal.mem_span_singleton_self (2 : ℤ))

/-- The open `D(2)` is a strict subset of `Spec ℤ`, since it omits the prime `(2)`. -/
public theorem integerBasicOpenTwo_ne_top : integerBasicOpenTwo ≠ ⊤ := by
  intro h
  apply integerTwoPrime_not_mem_basicOpenTwo
  rw [h]
  exact TopologicalSpace.Opens.mem_top _

/-- The open subscheme `D(2)` of the integer spectrum is normal. -/
public theorem integerBasicOpenTwo_isNormal : IsNormal integerBasicOpenTwo := by
  let _ : IsNormal integerSpec := integerSpec_isNormal
  infer_instance

private abbrev zeroSpec : Scheme := Spec (CommRingCat.of PUnit.{1})

private theorem zeroSpec_isEmpty : IsEmpty zeroSpec := by
  change IsEmpty (PrimeSpectrum PUnit.{1})
  infer_instance

private theorem zeroRing_isLocallyNormalRing : IsLocallyNormalRing PUnit.{1} where
  isDomain_atPrime p := isEmptyElim p
  isIntegrallyClosed_atPrime p := isEmptyElim p

private theorem zeroSpec_isNormal : IsNormal zeroSpec := by
  let _ : IsLocallyNormalRing PUnit.{1} := zeroRing_isLocallyNormalRing
  exact normalSpec (R := CommRingCat.of PUnit.{1})

private theorem integerSpec_globalSections_isLocallyNormalRing :
    IsLocallyNormalRing Γ(integerSpec, ⊤) :=
  (isNormal_iff_isLocallyNormalRing integerSpec).mp integerSpec_isNormal

private theorem integerBasicOpenTwo_sections_isLocallyNormalRing :
    IsLocallyNormalRing Γ(integerSpec, integerBasicOpenTwo) :=
  (integerBasicOpenTwo_isAffineOpen.isNormal_iff_isLocallyNormalRing).mp
    integerBasicOpenTwo_isNormal

private theorem integerSpec_affineOpenCover_isLocallyNormalRing :
    ∀ i : integerSpec.affineOpenCover.I₀,
      IsLocallyNormalRing (integerSpec.affineOpenCover.X i) :=
  (IsNormal.iff_of_affineOpenCover integerSpec integerSpec.affineOpenCover).mp
    integerSpec_isNormal

private theorem zeroSpec_globalSections_isLocallyNormalRing :
    IsLocallyNormalRing Γ(zeroSpec, ⊤) :=
  (isNormal_iff_isLocallyNormalRing zeroSpec).mp zeroSpec_isNormal

end AlgebraicGeometry
