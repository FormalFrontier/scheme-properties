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

example : Nontrivial (Spec (CommRingCat.of (Polynomial ℚ))) := by
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

example :
    IsIso ((Spec (CommRingCat.of (Polynomial ℚ))).fromSpecStalk
      (genericPoint (Spec (CommRingCat.of (Polynomial ℚ))))).toRationalMap.functionFieldMap :=
  inferInstance

example :
    Spec.map ((Spec (CommRingCat.of (Polynomial ℚ))).fromSpecStalk
      (genericPoint (Spec (CommRingCat.of (Polynomial ℚ))))).toRationalMap.functionFieldMap =
      (Spec (Spec (CommRingCat.of (Polynomial ℚ))).functionField).fromSpecStalk
        (genericPoint (Spec (Spec (CommRingCat.of (Polynomial ℚ))).functionField)) :=
  Scheme.genericPoint_functionFieldMap_specMap (Spec (CommRingCat.of (Polynomial ℚ)))

example :
    ¬ LocallyOfFiniteType ((Spec (CommRingCat.of (Polynomial ℚ))).fromSpecStalk
      (genericPoint (Spec (CommRingCat.of (Polynomial ℚ))))) := by
  let : Nontrivial (Spec (CommRingCat.of (Polynomial ℚ))) := by
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
  exact Scheme.not_locallyOfFiniteType_fromSpecStalk_genericPoint
    (Spec (CommRingCat.of (Polynomial ℚ)))

example : Spec (CommRingCat.of (Polynomial ℚ)) ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ))

example : LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ))) := by
  apply (HasRingHomProperty.Spec_iff).2
  change (Polynomial.C : ℚ →+* Polynomial ℚ).FiniteType
  have hC : (Polynomial.C : ℚ →+* Polynomial ℚ) =
      algebraMap ℚ (Polynomial ℚ) :=
    RingHom.ext fun element => Polynomial.C_eq_algebraMap element
  rw [hC, RingHom.finiteType_algebraMap]
  infer_instance

example :
    ¬ LocallyOfFiniteType
      ((Spec (CommRingCat.of (Polynomial ℚ))).fromSpecStalk
        (genericPoint (Spec (CommRingCat.of (Polynomial ℚ)))) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ))) := by
  let : Nontrivial (Spec (CommRingCat.of (Polynomial ℚ))) := by
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
  exact Scheme.not_locallyOfFiniteType_fromSpecStalk_genericPoint_comp
    (Spec (CommRingCat.of (Polynomial ℚ)))
    (Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ)))

example :
    IsIso ((Spec (CommRingCat.of ℚ)).fromSpecStalk
      (genericPoint (Spec (CommRingCat.of ℚ)))).toRationalMap.functionFieldMap :=
  inferInstance

end SchemePropertiesTest.GenericPointFunctionField
