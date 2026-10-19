/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import SchemeProperties.Normal
public import SchemeProperties.RationalFunctionFieldPullback
import SchemeProperties.RationalFunctionFieldNaturality

public section

/-!
# Integral morphisms with invertible function-field maps

For integral schemes, the birationality condition on a dominant morphism is
expressed by invertibility of the function-field map of its associated rational
map. The target is required to be normal; integrality of the morphism does not
include a finite-type hypothesis.

## References

* A. Grothendieck, with J. Dieudonné, *Éléments de géométrie algébrique II:
  Étude globale élémentaire de quelques classes de morphismes*, Publications
  Mathématiques de l'IHÉS 8 (1961), Corollary 6.1.15 and its affine argument,
  p. 114. Compare its rational-section formulation with the function-field-map
  condition below. Definition 6.1.1 and Proposition 6.1.4, p. 110, distinguish
  integral morphisms from finite morphisms: the latter additionally have finite
  type.
* Mathlib, `Mathlib.AlgebraicGeometry.Morphisms.Integral` (Andrew Yang): integral
  morphisms of schemes.
* Mathlib, `Mathlib.AlgebraicGeometry.Birational.RationalMap` (Andrew Yang): the
  rational map associated to a scheme morphism.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An integral dominant morphism between integral schemes with normal target
is an isomorphism if its induced canonical function-field map is invertible.

Compare the rational-section formulation in EGA II, Corollary 6.1.15 (p. 114).
That corollary assumes a rational section, rather than the invertibility of
`f.toRationalMap.functionFieldMap` used here. Its affine argument identifies an
integral extension of an integrally closed domain with that domain when their
fraction fields agree; neither finiteness nor a Noetherian hypothesis is required. -/
theorem isIso_of_isIntegralHom_of_isIso_functionFieldMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (f : X ⟶ Y) [IsIntegralHom f] [IsDominant f]
    [IsIso f.toRationalMap.functionFieldMap] : IsIso f := by
  classical
  let φ := f.toRationalMap.functionFieldMap
  haveI : IsIso φ := inferInstance
  change MorphismProperty.isomorphisms Scheme f
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
  intro y
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  letI : Nonempty U := ⟨⟨y, hyU⟩⟩
  letI : Nonempty (f ⁻¹ᵁ U) := f.nonempty_preimage_of_isDominant U
  refine ⟨U, hyU, ?_⟩
  change IsIso (f ∣_ U)
  apply (isIso_morphismRestrict_iff_isIso_app f hU).mpr
  let A : CommRingCat.{u} := Γ(Y, U)
  let B : CommRingCat.{u} := Γ(X, f ⁻¹ᵁ U)
  haveI : IsOpenImmersion hU.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec hU
  haveI : IsNormal (Spec A) := isNormal_of_isOpenImmersion hU.fromSpec
  haveI : IsLocallyNormalRing A := isLocallyNormalRing_of_isNormal_spec A
  haveI : IsIntegrallyClosed A :=
    IsIntegrallyClosed.of_localization_maximal fun P _ _ ↦
      IsLocallyNormalRing.isIntegrallyClosed_atPrime ⟨P, inferInstance⟩
  haveI : IsFractionRing A Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  have hsquare : f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) =
      Y.germToFunctionField U ≫ φ :=
    f.app_germToFunctionField U
  have hcomm : f.app U ≫ (X.germToFunctionField (f ⁻¹ᵁ U) ≫ inv φ) =
      Y.germToFunctionField U := by
    rw [← Category.assoc, hsquare, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  letI : Algebra A B := (f.app U).hom.toAlgebra
  letI : Algebra B Y.functionField :=
    (X.germToFunctionField (f ⁻¹ᵁ U) ≫ inv φ).hom.toAlgebra
  haveI : IsScalarTower A B Y.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    exact congrArg CommRingCat.Hom.hom hcomm.symm
  haveI : Algebra.IsIntegral A B :=
    algebraMap_isIntegral_iff.mp (f.isIntegral_app U hU)
  have hinj : Function.Injective (algebraMap B Y.functionField) := by
    change Function.Injective (fun b ↦ inv φ (X.germToFunctionField (f ⁻¹ᵁ U) b))
    exact (ConcreteCategory.bijective_of_isIso (inv φ)).1.comp
      (X.germToFunctionField_injective (f ⁻¹ᵁ U))
  apply (ConcreteCategory.isIso_iff_bijective (f.app U)).mpr
  constructor
  · intro a a' ha
    have ha' : algebraMap A B a = algebraMap A B a' := by
      simpa only [RingHom.algebraMap_toAlgebra] using ha
    apply Y.germToFunctionField_injective U
    change algebraMap A Y.functionField a = algebraMap A Y.functionField a'
    simpa only [IsScalarTower.algebraMap_apply A B Y.functionField] using
      congrArg (algebraMap B Y.functionField) ha'
  · intro b
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
      (R := A) (K := Y.functionField)
      (_root_.IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := A) b))
    refine ⟨a, hinj ?_⟩
    change algebraMap B Y.functionField (algebraMap A B a) =
      algebraMap B Y.functionField b
    rw [← IsScalarTower.algebraMap_apply A B Y.functionField]
    exact ha

end AlgebraicGeometry.Scheme.Hom
