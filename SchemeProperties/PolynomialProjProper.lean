/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import MultivariatePolynomials.GradeZero

/-!
# Polynomial Proj over its coefficient ring

For a finite variable type, the projective spectrum of the total-degree grading
of a multivariate polynomial ring is proper over the coefficient ring. The
structural morphism is `Proj.toSpecZero` followed by the spectrum isomorphism
induced by `MvPolynomial.gradeZeroAlgEquiv`. Its target is the spectrum of the
original coefficient ring, not a replacement degree-zero ring.

The coefficient ring may be zero and the variable type may be empty. The universe
convention `R : Type (max u v)`, `σ : Type v` keeps the projective spectrum and
`Spec R` in the same scheme category; taking `σ = Fin n` allows every coefficient
universe and every `n`, including zero.

## References

This statement uses Mathlib's projective-spectrum and proper-morphism APIs and
Multivariate Polynomials' canonical degree-zero coefficient equivalence. See
`docs/PolynomialProjProper.md` for the coefficient-map orientation and examples.
-/

@[expose] public section

open CategoryTheory

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Proj

/-- The total-degree projective spectrum of a polynomial ring in finitely many
variables is proper over its original coefficient ring. The second factor is
induced by the forward coefficient equivalence `R ≃ₐ[R] ↥(homogeneousSubmodule σ R 0)`;
contravariance of `Spec` gives the displayed direction without inverting that
equivalence. No nontriviality or nonemptiness assumption is required. -/
theorem isProper_toSpec_mvPolynomial
    (R : Type (max u v)) (σ : Type v) [CommRing R] [Finite σ] :
    IsProper
      (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule σ R) ≫
        (Scheme.Spec.mapIso
          (MvPolynomial.gradeZeroAlgEquiv σ R).toRingEquiv.toCommRingCatIso.op).hom :
        Proj (MvPolynomial.homogeneousSubmodule σ R) ⟶ Spec (CommRingCat.of R)) := by
  let : Algebra.FiniteType R (MvPolynomial σ R) := inferInstance
  let :
      IsScalarTower R ↥(MvPolynomial.homogeneousSubmodule σ R 0)
        (MvPolynomial σ R) :=
    IsScalarTower.of_algebraMap_eq
      (R := R) (S := ↥(MvPolynomial.homogeneousSubmodule σ R 0))
      (A := MvPolynomial σ R) (fun _ => rfl)
  let :
      Algebra.FiniteType
        ↥(MvPolynomial.homogeneousSubmodule σ R 0)
        (MvPolynomial σ R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType
      R ↥(MvPolynomial.homogeneousSubmodule σ R 0)
      (MvPolynomial σ R)
  infer_instance

end AlgebraicGeometry.Proj
