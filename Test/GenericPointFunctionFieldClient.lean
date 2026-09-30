/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.GenericPointFunctionField
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Algebra.Polynomial.RingDivision

set_option warningAsError true

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SchemePropertiesTest.GenericPointFunctionField

private abbrev affineLine := Spec (CommRingCat.of (Polynomial ℚ))

private instance affineLine_nontrivial : Nontrivial affineLine := by
  change Nontrivial (PrimeSpectrum (Polynomial ℚ))
  let generic : PrimeSpectrum (Polynomial ℚ) := ⟨⊥, inferInstance⟩
  let origin : PrimeSpectrum (Polynomial ℚ) :=
    ⟨Ideal.span {Polynomial.X},
      (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X⟩
  refine ⟨⟨generic, origin, ?_⟩⟩
  intro heq
  have hideals : (⊥ : Ideal (Polynomial ℚ)) = Ideal.span {Polynomial.X} :=
    congrArg PrimeSpectrum.asIdeal heq
  have hX : (Polynomial.X : Polynomial ℚ) ∈ (⊥ : Ideal (Polynomial ℚ)) := by
    rw [hideals]
    exact Ideal.subset_span (Set.mem_singleton _)
  simp at hX

private theorem affineLine_functionFieldMap_isIso :
    IsIso (affineLine.fromSpecStalk (genericPoint affineLine)).toRationalMap.functionFieldMap :=
  inferInstance

private theorem affineLine_canonical_readback :
    Spec.map (affineLine.fromSpecStalk (genericPoint affineLine)).toRationalMap.functionFieldMap =
      (Spec affineLine.functionField).fromSpecStalk
        (genericPoint (Spec affineLine.functionField)) :=
  Scheme.genericPoint_functionFieldMap_specMap affineLine

private theorem affineLine_generic_not_lft :
    ¬ LocallyOfFiniteType (affineLine.fromSpecStalk (genericPoint affineLine)) :=
  Scheme.not_locallyOfFiniteType_fromSpecStalk_genericPoint affineLine

private def affineLineToPoint : affineLine ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ))

private theorem affineLineToPoint_finiteType : LocallyOfFiniteType affineLineToPoint := by
  unfold affineLineToPoint
  apply (HasRingHomProperty.Spec_iff).2
  change (Polynomial.C : ℚ →+* Polynomial ℚ).FiniteType
  have hC : (Polynomial.C : ℚ →+* Polynomial ℚ) =
      algebraMap ℚ (Polynomial ℚ) :=
    RingHom.ext fun element => Polynomial.C_eq_algebraMap element
  rw [hC, RingHom.finiteType_algebraMap]
  infer_instance

private theorem affineLine_generic_relative_not_lft :
    ¬ LocallyOfFiniteType
      (affineLine.fromSpecStalk (genericPoint affineLine) ≫ affineLineToPoint) :=
  Scheme.not_locallyOfFiniteType_fromSpecStalk_genericPoint_comp affineLine affineLineToPoint

private theorem point_functionFieldMap_isIso :
    IsIso ((Spec (CommRingCat.of ℚ)).fromSpecStalk
      (genericPoint (Spec (CommRingCat.of ℚ)))).toRationalMap.functionFieldMap :=
  inferInstance

end SchemePropertiesTest.GenericPointFunctionField
