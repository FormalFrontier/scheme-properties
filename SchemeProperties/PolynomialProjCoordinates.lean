/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Coordinate points of polynomial projective spectra

Coordinate evaluation sends one variable to `1` and all other variables to `0`.
`coordinateAwayEval` extends this evaluation to the degree-zero localization at that variable;
`coordinateAwayEval_mk` computes it on homogeneous fractions. For each coefficient prime,
`coordinatePoint` gives a point of the corresponding projective basic open, with membership
and chart-inclusion formulas.

The variable type and coefficient ring have independent universes. The construction uses
maps of prime spectra, rather than a morphism of schemes between these universes.

## Implementation notes

The coefficient ring may be the zero ring, in which case there is no coefficient prime to
supply. An empty variable type has no coordinate to choose. No finiteness, domain or field
hypothesis is imposed, and no distinctness assertion is needed for these constructions.

## References

The constructions use Mathlib's polynomial evaluation and grading (Johannes Hölzl,
Johan Commelin, Mario Carneiro and Eric Wieser), projective-spectrum charts (Andrew Yang
and Jujian Zhang), homogeneous localizations (Jujian Zhang and Eric Wieser), localizations
(Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston and Anne Baanen), prime spectra
(Johan Commelin, Filippo A. E. Nuccio and Andrew Yang), and categories of rings
(Kim Morrison, Johannes Hölzl and Yury Kudryashov).
-/

@[expose] public section

namespace AlgebraicGeometry.Proj

open CategoryTheory

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ : Type v} {R : Type u} [CommRing R]

private noncomputable def coordinateEval (i : σ) : MvPolynomial σ R →+* R :=
  MvPolynomial.eval (fun j ↦ @ite R (j = i) (Classical.propDecidable (j = i)) 1 0)

private lemma coordinateEval_X_self (i : σ) :
    coordinateEval (R := R) i (MvPolynomial.X i) = 1 := by
  classical
  simp [coordinateEval]

/-- Coordinate evaluation on the degree-zero localization at `X i`. -/
@[no_expose] noncomputable def coordinateAwayEval (i : σ) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule σ R)
      (MvPolynomial.X i) →+* R :=
  (Localization.awayLift (coordinateEval (R := R) i) (MvPolynomial.X i)
    (by rw [coordinateEval_X_self]; exact isUnit_one)).comp
      (algebraMap
        (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule σ R)
          (MvPolynomial.X i))
        (Localization.Away (MvPolynomial.X i)))

/-- A homogeneous fraction with denominator a power of `X i` evaluates to the coordinate
value of its numerator, since `X i` evaluates to `1`. -/
@[simp] theorem coordinateAwayEval_mk (i : σ) (n : ℕ) (a : MvPolynomial σ R)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule σ R (n • (1 : ℕ))) :
    coordinateAwayEval i
        (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule σ R)
          (MvPolynomial.isHomogeneous_X R i) n a ha) =
      MvPolynomial.eval
        (fun j ↦ @ite R (j = i) (Classical.propDecidable (j = i)) 1 0) a := by
  change
    Localization.awayLift (coordinateEval (R := R) i) (MvPolynomial.X i)
      (by rw [coordinateEval_X_self]; exact isUnit_one)
      (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule σ R)
        (MvPolynomial.isHomogeneous_X R i) n a ha).val =
      coordinateEval (R := R) i a
  refine (congrArg
    (Localization.awayLift (coordinateEval (R := R) i) (MvPolynomial.X i)
      (by rw [coordinateEval_X_self]; exact isUnit_one))
    (HomogeneousLocalization.Away.val_mk (MvPolynomial.homogeneousSubmodule σ R)
      n (MvPolynomial.isHomogeneous_X R i) a ha)).trans ?_
  simpa only [one_pow, mul_one] using
    (Localization.awayLift_mk (coordinateEval (R := R) i) (MvPolynomial.X i)
      a (1 : R) (by rw [coordinateEval_X_self, mul_one]) n)

/-- The coordinate point over a coefficient prime, obtained by applying the canonical chart
inclusion at `X i` to the prime pulled back along coordinate evaluation. -/
noncomputable def coordinatePoint (i : σ) (p : PrimeSpectrum R) :
    Proj (MvPolynomial.homogeneousSubmodule σ R) :=
  (Proj.awayι (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X i)
    (m := 1) (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one)
      (PrimeSpectrum.comap (coordinateAwayEval i) p)

/-- The coordinate point lies in its coordinate basic open. -/
theorem coordinatePoint_mem_basicOpen (i : σ) (p : PrimeSpectrum R) :
    coordinatePoint i p ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X i) := by
  rw [← Proj.opensRange_awayι (MvPolynomial.homogeneousSubmodule σ R)
    (MvPolynomial.X i) (m := 1) (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one]
  exact ⟨PrimeSpectrum.comap (coordinateAwayEval i) p, rfl⟩

/-- The coordinate point is the image of the pulled-back prime under the chart inclusion. -/
theorem coordinatePoint_eq_awayι (i : σ) (p : PrimeSpectrum R) :
    coordinatePoint i p =
      (Proj.awayι (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.X i)
        (m := 1) (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one)
          (PrimeSpectrum.comap (coordinateAwayEval i) p) := by
  rfl

/-- Coordinate evaluation sends a coefficient, mapped through degree zero, to itself. -/
theorem coordinateAwayEval_fromZeroRingHom (i : σ) (r : R) :
    coordinateAwayEval i
      (HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule σ R)
        (Submonoid.powers (MvPolynomial.X i))
        (algebraMap R ↥(MvPolynomial.homogeneousSubmodule σ R 0) r)) = r := by
  change
    Localization.awayLift (coordinateEval (R := R) i) (MvPolynomial.X i)
      (by rw [coordinateEval_X_self]; exact isUnit_one)
      (HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule σ R)
        (Submonoid.powers (MvPolynomial.X i))
        (algebraMap R ↥(MvPolynomial.homogeneousSubmodule σ R 0) r)).val = r
  rw [← HomogeneousLocalization.algebraMap_apply,
    ← HomogeneousLocalization.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply
      ↥(MvPolynomial.homogeneousSubmodule σ R 0)
      (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule σ R)
        (MvPolynomial.X i))
      (Localization.Away (MvPolynomial.X i)),
    ← Localization.mk_algebraMap]
  simp [coordinateEval, Localization.awayLift, Localization.mk_one_eq_algebraMap,
    MvPolynomial.algebraMap_eq]

/-- Coordinate evaluation retracts the coefficient map through degree zero. -/
theorem coordinateAwayEval_comp_fromZeroRingHom (i : σ) :
    ((coordinateAwayEval (R := R) i).comp
      (HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule σ R)
        (Submonoid.powers (MvPolynomial.X i)))).comp
      (algebraMap R ↥(MvPolynomial.homogeneousSubmodule σ R 0)) = RingHom.id R := by
  ext r
  exact coordinateAwayEval_fromZeroRingHom i r

end AlgebraicGeometry.Proj
