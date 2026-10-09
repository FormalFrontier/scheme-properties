/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.QuotientClosedPoints
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.FiniteType

/-!
# Scheme points of polynomial quotients

The evaluation map attached to a zero of an arbitrary polynomial ideal defines a
base-compatible affine scheme point. Its underlying prime is the closed prime
constructed by evaluation, and, for finitely many variables over an algebraically
closed field, Mathlib's scheme-point equivalence recovers the quotient zero-locus
equivalence. The ideal may be nonreduced or the unit ideal.

## Limitations

These comparisons require a common universe for the field and variables because
Mathlib's `Spec.homEquivAlgHom` is stated at a common universe. The underlying
polynomial closed-point construction has independent universes.

## References

* R. Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, §3.6.9 and the
  discussion following Exercise 5.1.E (October 21, 2025 draft).
* Mathlib's `Spec.map`, `Spec.homEquivAlgHom`, `pointEquivClosedPoint` and generic
  finite-type affine-spectrum instance.
* The quotient zero-locus and closed-point construction in Multivariate Polynomials.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace MvPolynomial

universe u

variable {K : Type u} [Field K] {σ : Type u}

/-- Quotient evaluation gives a base-compatible affine scheme point. -/
def zeroLocusSchemePoint (I : Ideal (MvPolynomial σ K)) (a : zeroLocus K I) :
    {g : AlgebraicGeometry.Spec ↧K ⟶
        AlgebraicGeometry.Spec ↧(MvPolynomial σ K ⧸ I) //
      g ≫ AlgebraicGeometry.Spec.algebraMap K (MvPolynomial σ K ⧸ I) = 𝟙 _} := by
  refine ⟨AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (zeroLocusQuotientEval I a).toRingHom), ?_⟩
  simp [AlgebraicGeometry.Spec.algebraMap, ← AlgebraicGeometry.Spec.map_comp,
    ← CommRingCat.ofHom_comp]

/-- The underlying morphism of quotient evaluation is `Spec.map` of descended
evaluation. -/
@[simp] theorem zeroLocusSchemePoint_val (I : Ideal (MvPolynomial σ K))
    (a : zeroLocus K I) :
    (zeroLocusSchemePoint I a).val = AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (zeroLocusQuotientEval I a).toRingHom) := rfl

/-- The quotient evaluation point commutes with the structure map to `Spec K`. -/
theorem zeroLocusSchemePoint_comp (I : Ideal (MvPolynomial σ K))
    (a : zeroLocus K I) :
    (zeroLocusSchemePoint I a).val ≫
      AlgebraicGeometry.Spec.algebraMap K (MvPolynomial σ K ⧸ I) = 𝟙 _ :=
  (zeroLocusSchemePoint I a).property

/-- The affine morphism of quotient evaluation is the underlying morphism of
Mathlib's base-compatible scheme point. This needs neither finitely many
variables nor algebraic closure. -/
theorem zeroLocusQuotientEval_specMap (I : Ideal (MvPolynomial σ K))
    (a : zeroLocus K I) :
    AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (zeroLocusQuotientEval I a).toRingHom) =
      ((AlgebraicGeometry.Spec.homEquivAlgHom
        (R := K) (A := MvPolynomial σ K ⧸ I) (B := K)).symm
        (zeroLocusQuotientEval I a)).val := by
  rfl

/-- The underlying prime of the affine evaluation point is the closed quotient
prime with evaluation kernel, for any field and variable type. -/
theorem zeroLocusClosedPoint_specMap (I : Ideal (MvPolynomial σ K))
    (a : zeroLocus K I) :
    (zeroLocusClosedPoint I a).val =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (zeroLocusQuotientEval I a).toRingHom)
        (IsLocalRing.closedPoint K) := by
  apply PrimeSpectrum.ext
  change (zeroLocusClosedPoint I a).val.asIdeal =
    (PrimeSpectrum.comap (zeroLocusQuotientEval I a).toRingHom
      (IsLocalRing.closedPoint K)).asIdeal
  rw [PrimeSpectrum.comap_asIdeal, zeroLocusClosedPoint_asIdeal]
  rw [show (IsLocalRing.closedPoint K).asIdeal = ⊥ from
    IsLocalRing.maximalIdeal_eq_bot]
  exact RingHom.ker_eq_comap_bot _

variable [IsAlgClosed K] [Finite σ]

/-- Mathlib's equivalence from base-compatible scheme points to closed points
maps the quotient evaluation point to the quotient zero-locus point. In contrast
to a reduced affine-variety convention, the ideal is arbitrary. -/
theorem zeroLocusEquivClosedPoints_pointEquiv
    (I : Ideal (MvPolynomial σ K)) (a : zeroLocus K I) :
    zeroLocusEquivClosedPoints I a =
      AlgebraicGeometry.pointEquivClosedPoint
        (AlgebraicGeometry.Spec ↧(MvPolynomial σ K ⧸ I) ↘ AlgebraicGeometry.Spec ↧K)
        (zeroLocusSchemePoint I a) := by
  apply Subtype.ext
  change (zeroLocusEquivClosedPoints I a).val =
    (zeroLocusSchemePoint I a).val (IsLocalRing.closedPoint K)
  rw [zeroLocusEquivClosedPoints_apply, zeroLocusClosedPoint_specMap,
    zeroLocusSchemePoint_val]

end MvPolynomial
