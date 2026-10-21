/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.PolynomialProjCoordinates
public import SchemeProperties.ProjReduced
public import SchemeProperties.ProjIrreducible

/-!
# Polynomial projective space

`PolynomialProjectiveSpace R n` is the projective spectrum of the polynomial ring in
`n + 1` variables over `R`, with its total-degree grading. Its coefficient morphism
`toSpec` factors through the spectrum of the degree-zero subring.

For each coordinate `i`, `coordinateSection` is the morphism from `Spec R` obtained
from coordinate evaluation in the chart at `X i`. Its value at a coefficient prime
is the coordinate point supplied by `Proj.coordinatePoint`.

The definitions allow every commutative ring, including the zero ring, and every
natural number `n`, including `0`. The coordinate morphisms are sections of `toSpec`.
Over a nontrivial ring projective space is nonempty, and over a domain it is integral.

## References

The constructions use Mathlib's projective-spectrum charts and structural morphisms
(Andrew Yang and Jujian Zhang), homogeneous polynomials (Johan Commelin and Eric Wieser),
polynomial evaluation (Johannes Hölzl, Johan Commelin and Mario Carneiro), homogeneous
localizations (Jujian Zhang and Eric Wieser), degree-zero algebras (Eric Wieser,
Kevin Buzzard, Jujian Zhang and Fangming Li), and scheme and ring categories
(Kim Morrison, Johannes Hölzl and Yury Kudryashov). Coordinate evaluation and coordinate
points are provided by the Scheme Properties formalization of Formal Frontier Agents.
The integrality proof uses Mathlib's reduced-plus-irreducible criterion (Andrew Yang)
and the Scheme Properties reducedness and irreducibility results, the latter following
the Stacks Project, [Tag 004W](https://stacks.math.columbia.edu/tag/004W).
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u
universe v

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Proj

/-- The polynomial projective spectrum over a nontrivial ring is nonempty when there
is a coordinate: a coefficient prime gives its coordinate point. -/
theorem nonempty_mvPolynomial (σ : Type v) (R : Type u)
    [CommRing R] [Nonempty σ] [Nontrivial R] :
    Nonempty (Proj (MvPolynomial.homogeneousSubmodule σ R)) := by
  let i : σ := Classical.choice inferInstance
  let p : PrimeSpectrum R := Classical.choice inferInstance
  exact ⟨coordinatePoint i p⟩

/-- The polynomial projective spectrum over a domain is integral when there is a
coordinate, by reducedness and irreducibility of Proj and Mathlib's scheme criterion. -/
theorem isIntegral_mvPolynomial (σ : Type v) (R : Type u)
    [CommRing R] [Nonempty σ] [IsDomain R] :
    IsIntegral (Proj (MvPolynomial.homogeneousSubmodule σ R)) := by
  let := nonempty_mvPolynomial σ R
  exact isIntegral_of_irreducibleSpace_of_isReduced
    (Proj (MvPolynomial.homogeneousSubmodule σ R))

end Proj

/-- Projective `n`-space over `R`, defined by the total-degree polynomial grading. -/
abbrev PolynomialProjectiveSpace (R : Type u) [CommRing R] (n : ℕ) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)

namespace PolynomialProjectiveSpace

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The coefficient morphism from projective space to `Spec R`. -/
def toSpec : PolynomialProjectiveSpace R n ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0)))

/-- The coefficient morphism factors through the spectrum of the degree-zero subring. -/
theorem toSpec_def :
    toSpec R n =
      Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0))) := rfl

/-- The coordinate morphism defined by evaluation in the affine chart at `X i`. -/
def coordinateSection (i : Fin (n + 1)) :
    Spec (CommRingCat.of R) ⟶ PolynomialProjectiveSpace R n :=
  Spec.map (CommRingCat.ofHom (Proj.coordinateAwayEval (R := R) i)) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (m := 1) ((MvPolynomial.mem_homogeneousSubmodule (R := R) 1 (MvPolynomial.X i)).2
        (MvPolynomial.isHomogeneous_X R i)) Nat.zero_lt_one

/-- The coordinate morphism factors through its standard affine chart. -/
theorem coordinateSection_def (i : Fin (n + 1)) :
    coordinateSection R n i =
      Spec.map (CommRingCat.ofHom (Proj.coordinateAwayEval (R := R) i)) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
          (m := 1) ((MvPolynomial.mem_homogeneousSubmodule (R := R) 1 (MvPolynomial.X i)).2
            (MvPolynomial.isHomogeneous_X R i)) Nat.zero_lt_one := rfl

/-- On coefficient primes, the coordinate morphism gives the corresponding coordinate point. -/
@[simp] theorem coordinateSection_apply (i : Fin (n + 1)) (p : PrimeSpectrum R) :
    coordinateSection R n i p = Proj.coordinatePoint i p := rfl

/-- Every coordinate morphism is a section of the coefficient morphism, as an
identity of scheme morphisms, including over the zero ring. -/
theorem coordinateSection_toSpec (i : Fin (n + 1)) :
    coordinateSection R n i ≫ toSpec R n = 𝟙 (Spec (CommRingCat.of R)) := by
  calc
    coordinateSection R n i ≫ toSpec R n =
        Spec.map (CommRingCat.ofHom
          (((Proj.coordinateAwayEval (R := R) i).comp
            (HomogeneousLocalization.fromZeroRingHom
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
              (Submonoid.powers (MvPolynomial.X i)))).comp
            (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0)))) := by
      rw [coordinateSection_def, toSpec_def, Category.assoc,
        Proj.awayι_toSpecZero_assoc]
      simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    _ = 𝟙 _ := by
      rw [Proj.coordinateAwayEval_comp_fromZeroRingHom,
        CommRingCat.ofHom_id, Spec.map_id]

/-- Projective `n`-space over a nontrivial ring is nonempty, also for `n = 0`. -/
theorem nonempty (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ) :
    Nonempty (PolynomialProjectiveSpace R n) :=
  Proj.nonempty_mvPolynomial (Fin (n + 1)) R

/-- Projective `n`-space over a domain is integral. -/
instance isIntegral (R : Type u) [CommRing R] [IsDomain R] (n : ℕ) :
    IsIntegral (PolynomialProjectiveSpace R n) :=
  Proj.isIntegral_mvPolynomial (Fin (n + 1)) R

end PolynomialProjectiveSpace

end AlgebraicGeometry
