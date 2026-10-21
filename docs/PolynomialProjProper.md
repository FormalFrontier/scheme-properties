# Polynomial projective spectra over the coefficient ring

Let `R` be a commutative ring and let `σ` be a finite variable type. Put
`A = MvPolynomial σ R` and `𝒜 = MvPolynomial.homogeneousSubmodule σ R`.
These are the total-degree homogeneous pieces: membership in `𝒜 d` means
homogeneity of degree `d`, not equality of total degree with `d`. In particular,
the zero polynomial belongs to every homogeneous piece.

## The coefficient morphism

The [properness statement](../SchemeProperties/PolynomialProjProper.lean) concerns
this composition of existing morphisms:

```lean
Proj.toSpecZero (MvPolynomial.homogeneousSubmodule σ R) ≫
  (Scheme.Spec.mapIso
    (MvPolynomial.gradeZeroAlgEquiv σ R).toRingEquiv.toCommRingCatIso.op).hom
```

Write `G₀ = ↥(𝒜 0)`. Multivariate Polynomials supplies the canonical algebra
equivalence `e : R ≃ₐ[R] G₀`. Its forward map is the coefficient inclusion:
`gradeZeroAlgEquiv_apply` identifies it with `algebraMap R G₀`, and
`coe_gradeZeroAlgEquiv` identifies its ambient polynomial with `C r`. Its inverse
is the constant coefficient, as expressed by `gradeZeroAlgEquiv_symm_apply`.
Thus the second factor above goes from `Spec G₀` to **`Spec R`**. The opposite
isomorphism reverses the endpoints before `Scheme.Spec.mapIso` is applied;
using `e.symm` instead would give the wrong direction.

The grading dictionary is the fixed `MvPolynomial.gradedAlgebra`, selected as a
local instance in the two modules. Neither the grading nor the coefficient
algebra is a parameter chosen by a caller. There is no additional morphism
definition to unfold: the statement and its applications use the composition
itself. Mathlib's properness of `Proj.toSpecZero` is the general antecedent;
the coefficient equivalence identifies the base for this polynomial case.

## Universes and hypotheses

The finite-index statement uses `R : Type (max u v)` and `σ : Type v`. Then
`A`, `G₀` and `R` are rings in the same universe, and both scheme endpoints
belong to `Scheme.{max u v}`. Taking `σ = Fin n` and `v = 0` recovers every
`R : Type u` and every natural number `n` without a smallness hypothesis or
universe transport. This does not assert a morphism between independently
sized scheme categories for arbitrary `R : Type u` and `σ : Type v`.

There is no assumption that `R` is nontrivial, Noetherian, reduced, a domain,
finite dimensional or algebraic over another ring. There is no nonemptiness
assumption on `σ`, no field structure on `G₀`, and no chosen model or properness
hypothesis on the displayed composition.

## A nonempty projective-line example

Over a field `K`, the variable type `Fin 2` gives the usual projective line.
Here is a mathematical description of its point `[1:0]`, independent of any
properness assertion. Consider the coefficient-preserving map

`q : K[X₀,X₁] → K[T]`, with `q(X₀) = T` and `q(X₁) = 0`.

It can be expressed using `MvPolynomial.eval₂Hom`; its coefficient and variable
laws are `eval₂Hom_C` and `eval₂Hom_X'`. The map is surjective: its image contains
the coefficients and `T`, which generate `K[T]`. Its kernel is `(X₁)`.
For a homogeneous polynomial of degree `d`, the image is a scalar multiple of
`T^d`. The uniqueness of the degree decomposition in `K[T]` then shows that
every homogeneous component of an element of the kernel is again in the
kernel. Hence the kernel is homogeneous. It is prime because the quotient is
`K[T]`, a domain. Finally `X₀` has positive degree and is not in the kernel,
since `T ≠ 0`. The irrelevant ideal is therefore not contained in this kernel.

These are exactly the mathematical data of a relevant homogeneous prime,
representing `[1:0]`. They give a genuinely nonempty example, not a conditional
construction assuming `Nonempty (Proj 𝒜)`. This paragraph is a paper argument,
not an elaborated Lean point constructor or a theorem identifying the scheme's
carrier. The [three applications](../SchemePropertiesTest/PolynomialProjProper.lean)
instantiate the properness statement; they do not formalize this point argument.

## Empty boundary cases

- With variable type `Fin 0`, every polynomial is constant and every
  positive-degree homogeneous piece is zero. The irrelevant ideal is zero,
  hence is contained in every homogeneous prime. There are no relevant primes,
  so Proj is empty, even when `R` is a field. The coefficient morphism remains
  part of the statement for every commutative `R`.
- If `R` is the zero ring, `MvPolynomial σ R` is zero and has no prime ideals.
  Both its Proj and `Spec R` are empty. The application with `[Subsingleton R]`
  includes every such coefficient ring for every `Fin n`.

These emptiness arguments explain the boundaries mathematically; the application
module asserts properness of the same coefficient composition in each case,
not additional Lean emptiness results. Neither empty case substitutes for the
nonempty field example.

## Credit

The constructions are imported APIs, not copied proof implementations:
[Mathlib](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/ProjectiveSpectrum)
supplies the graded projective spectrum, its degree-zero structural morphism and
general properness theory, and
[Multivariate Polynomials](https://github.com/FormalFrontier/multivariate-polynomials/blob/602ba00e0d71b83ecc78adebffef1a494b2a47b1/MultivariatePolynomials/GradeZero.lean)
supplies `MvPolynomial.gradeZeroAlgEquiv` and its coefficient laws. The displayed
composition, applications and exposition are original project expression; see
[CREDITS.md](CREDITS.md) for collective authorship and licensing.
