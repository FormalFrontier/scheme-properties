/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Defs
public import GroupTheory.GroupAction.Integral
public import GroupTheory.Topology.Cofinite
public import MultivariatePolynomials.PolynomialClosedPointLoci
public import SchemeProperties.Topology.ClosedPointCofinite

/-!
# Automorphism-orbit topology on polynomial closed points

For an algebraic closure `L` of a field `K`, the automorphism-orbit equivalence
with the maximal spectrum of `K[X]` is a homeomorphism. The topology on the
original field `L` is cofinite, and its orbit space carries the quotient topology.
The maximal spectrum carries its Zariski topology, induced from the prime spectrum.

The underlying equivalence is `Polynomial.algAutOrbitEquivMaximalSpectrum`.
Composing it with the orbit projection gives the evaluation-kernel classifier,
which is a quotient map. Thus the closed-point Zariski topology is the quotient
of the cofinite topology on the algebraic closure. The statements hold over every
field, without separability or infinitude assumptions on the base field.

## References

This module uses the orbit correspondence and evaluation-kernel formulas from
`MultivariatePolynomials.PolynomialClosedPoints` and
`MultivariatePolynomials.PolynomialClosedPointLoci`. It uses Mathlib's quotient,
algebraicity-to-integrality, and homeomorphism APIs. Finite orbits of integral
elements are supplied by `IsIntegral.finite_orbit` in
`GroupTheory.GroupAction.Integral`, and the coinduced-topology equality is supplied
by `CofiniteTopology.coinduced_eq_cofinite_of_finite_fibers` in
`GroupTheory.Topology.Cofinite`. The target topology is identified by
`MaximalSpectrum.topologicalSpace_polynomial_eq_cofinite` in
`SchemeProperties.Topology.ClosedPointCofinite`.
-/

@[expose] public section

universe u v

namespace Polynomial

/-- The evaluation-kernel classifier from the algebraic closure to the polynomial
maximal spectrum is a quotient map from the cofinite topology to the Zariski
topology. Its value at `a` has ideal the kernel of evaluation at `a`, by
`algAutOrbitEquivMaximalSpectrum_asIdeal_ker_aeval`. -/
theorem isQuotientMap_algAutOrbitEquivMaximalSpectrum_mk
    (K : Type u) (L : Type v) [Field K] [Field L]
    [givenAlgebra : Algebra K L] [IsAlgClosure K L] :
    @Topology.IsQuotientMap L (MaximalSpectrum (Polynomial K))
      (TopologicalSpace.cofinite (X := L))
      (MaximalSpectrum.zariskiTopology (R := Polynomial K))
      (fun a : L =>
        algAutOrbitEquivMaximalSpectrum K L
          (Quotient.mk (MulAction.orbitRel (L ≃ₐ[K] L) L) a)) := by
  let : TopologicalSpace L := TopologicalSpace.cofinite
  let f : L → MaximalSpectrum (Polynomial K) := fun a =>
    algAutOrbitEquivMaximalSpectrum K L
      (Quotient.mk (MulAction.orbitRel (L ≃ₐ[K] L) L) a)
  have hsurj : Function.Surjective f := by
    intro m
    obtain ⟨q, rfl⟩ := (algAutOrbitEquivMaximalSpectrum K L).surjective m
    obtain ⟨a, rfl⟩ := Quotient.exists_rep q
    exact ⟨a, rfl⟩
  have hfinite : ∀ m, (f ⁻¹' {m}).Finite := by
    intro m
    obtain ⟨a, rfl⟩ := hsurj m
    have ha : IsIntegral K a := Algebra.IsIntegral.isIntegral a
    refine (ha.finite_orbit (M := L ≃ₐ[K] L)).subset ?_
    intro b hb
    change f b = f a at hb
    exact Quotient.exact ((algAutOrbitEquivMaximalSpectrum K L).injective hb)
  refine ⟨⟨?_⟩, hsurj⟩
  exact (MaximalSpectrum.topologicalSpace_polynomial_eq_cofinite K).trans
    (CofiniteTopology.coinduced_eq_cofinite_of_finite_fibers f hsurj hfinite).symm

/-- The automorphism-orbit space of an algebraic closure is homeomorphic to the
maximal spectrum of the base polynomial ring. The source has the quotient
topology induced by the cofinite topology on the original closure field, and
the target has its Zariski topology. The underlying equivalence is
`algAutOrbitEquivMaximalSpectrum`. -/
noncomputable def algAutOrbitHomeomorphMaximalSpectrum
    (K : Type u) (L : Type v) [Field K] [Field L]
    [givenAlgebra : Algebra K L] [IsAlgClosure K L] :
    @Homeomorph
      (MulAction.orbitRel.Quotient (L ≃ₐ[K] L) L)
      (MaximalSpectrum (Polynomial K))
      (@instTopologicalSpaceQuotient L
        (MulAction.orbitRel (L ≃ₐ[K] L) L)
        (TopologicalSpace.cofinite (X := L)))
      (MaximalSpectrum.zariskiTopology (R := Polynomial K)) := by
  letI : TopologicalSpace L := TopologicalSpace.cofinite
  have hquot : Topology.IsQuotientMap
      (Quotient.mk (MulAction.orbitRel (L ≃ₐ[K] L) L) :
        L → MulAction.orbitRel.Quotient (L ≃ₐ[K] L) L) :=
    isQuotientMap_quotient_mk'
  have hclassifier := isQuotientMap_algAutOrbitEquivMaximalSpectrum_mk K L
  refine
    { toEquiv := algAutOrbitEquivMaximalSpectrum K L
      continuous_toFun := hquot.continuous_iff.mpr hclassifier.continuous
      continuous_invFun := ?_ }
  apply hclassifier.continuous_iff.mpr
  simpa only [Function.comp_def, Equiv.invFun_as_coe, Equiv.symm_apply_apply] using
    hquot.continuous

/-- The orbit-space homeomorphism retains the orbit-to-closed-point equivalence,
including its forward and inverse maps. -/
@[simp]
theorem algAutOrbitHomeomorphMaximalSpectrum_toEquiv
    (K : Type u) (L : Type v) [Field K] [Field L]
    [givenAlgebra : Algebra K L] [IsAlgClosure K L] :
    @Homeomorph.toEquiv
      (MulAction.orbitRel.Quotient (L ≃ₐ[K] L) L)
      (MaximalSpectrum (Polynomial K))
      (@instTopologicalSpaceQuotient L
        (MulAction.orbitRel (L ≃ₐ[K] L) L)
        (TopologicalSpace.cofinite (X := L)))
      (MaximalSpectrum.zariskiTopology (R := Polynomial K))
      (algAutOrbitHomeomorphMaximalSpectrum K L) =
        algAutOrbitEquivMaximalSpectrum K L := by
  rfl

end Polynomial
