/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.IntegralDominantRationalCategory
public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

@[expose] public section

/-!
# Function fields and dominant rational maps

Dominant quotient rational maps of integral schemes induce homomorphisms of
function fields in the opposite direction. The generic-point image of Mathlib's
`RationalMap.fromFunctionField` lets its closed-point stalk map construct the
reversed homomorphism. Composition uses the inverse-image dense-open domain of
rational composition, without a finite-type or separatedness premise.

## References

* Mathlib, `Mathlib.AlgebraicGeometry.Birational.RationalMap` (Andrew Yang) and
  `Mathlib.AlgebraicGeometry.Birational.Composition` (Justus Springer): the
  quotient-invariant map from a function-field spectrum and partial-map
  composition on inverse-image domains.
* Mathlib, `Mathlib.AlgebraicGeometry.Stalk` (Andrew Yang, Fangming Li): the
  closed-point stalk map and its factorization through the stalk spectrum.
-/

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

private theorem partial_generic_image (p : X.PartialMap Y) [IsDominant p.hom] :
    p.fromFunctionField (closedPoint X.functionField) = genericPoint Y := by
  letI : Nonempty p.domain := ⟨⟨p.dense_domain.nonempty.choose,
    p.dense_domain.nonempty.choose_spec⟩⟩
  have hmem : genericPoint X ∈ p.domain :=
    (genericPoint_spec X).mem_open_set_iff p.domain.isOpen |>.mpr
      ⟨p.dense_domain.nonempty.choose, trivial,
        p.dense_domain.nonempty.choose_spec⟩
  have hdomain :
      p.domain.fromSpecStalkOfMem (genericPoint X) hmem
        (closedPoint X.functionField) = genericPoint (p.domain : Scheme) := by
    apply Subtype.ext
    have h := congrArg (fun f : Spec X.functionField ⟶ X =>
      f (closedPoint X.functionField))
      (p.domain.fromSpecStalkOfMem_ι (genericPoint X) hmem)
    rw [Hom.comp_apply, fromSpecStalk_closedPoint] at h
    simpa only [Opens.ι_apply] using
      h.trans (genericPoint_eq_of_isOpenImmersion p.domain.ι).symm
  have himage : p.hom (genericPoint (p.domain : Scheme)) = genericPoint Y := by
    apply ((genericPoint_spec Y).eq _).symm
    convert (genericPoint_spec (p.domain : Scheme)).image p.hom.continuous using 1
    simpa [Set.image_univ] using p.hom.denseRange.closure_eq.symm
  change (p.domain.fromSpecStalkOfMem (genericPoint X) hmem ≫ p.hom)
    (closedPoint X.functionField) = genericPoint Y
  rw [Hom.comp_apply, hdomain]
  exact himage

/-- The map from the source function field sends its closed point to the
generic point of the target of a dominant rational map. -/
theorem RationalMap.fromFunctionField_closedPoint (r : X ⤏ Y) [r.IsDominant] :
    r.fromFunctionField (closedPoint X.functionField) = genericPoint Y := by
  obtain ⟨p, rfl⟩ := PartialMap.toRationalMap_surjective r
  haveI : IsDominant p.hom := (p.isDominant_toRationalMap_iff).mp inferInstance
  exact partial_generic_image p

/-- The reversed homomorphism of function fields induced by a dominant rational
map, using Mathlib's closed-point stalk map on `r.fromFunctionField`. -/
noncomputable def RationalMap.functionFieldMap (r : X ⤏ Y) [r.IsDominant] :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (.of_eq r.fromFunctionField_closedPoint.symm)).hom ≫
    Scheme.stalkClosedPointTo r.fromFunctionField

private theorem stalkClosedPointTo_congr {R : CommRingCat.{u}} [IsLocalRing R]
    (f g : Spec R ⟶ Y) (e : f = g)
    (hf : f (closedPoint R) = genericPoint Y) (hg : g (closedPoint R) = genericPoint Y) :
    (Y.presheaf.stalkCongr (.of_eq hf.symm)).hom ≫ Scheme.stalkClosedPointTo f =
      (Y.presheaf.stalkCongr (.of_eq hg.symm)).hom ≫ Scheme.stalkClosedPointTo g := by
  subst g
  rfl

/-- Identical quotient-invariant maps out of the source function-field spectrum
induce identical function-field homomorphisms. -/
theorem RationalMap.functionFieldMap_eq_of_fromFunctionField_eq
    (r s : X ⤏ Y) [r.IsDominant] [s.IsDominant]
    (e : r.fromFunctionField = s.fromFunctionField) :
    r.functionFieldMap = s.functionFieldMap := by
  exact stalkClosedPointTo_congr r.fromFunctionField s.fromFunctionField e
    r.fromFunctionField_closedPoint s.fromFunctionField_closedPoint

private theorem spec_factorization (f : Spec X.functionField ⟶ Y)
    (hf : f (closedPoint X.functionField) = genericPoint Y) :
    Spec.map ((Y.presheaf.stalkCongr (.of_eq hf.symm)).hom ≫
      Scheme.stalkClosedPointTo f) ≫ Y.fromSpecStalk (genericPoint Y) = f := by
  rw [Spec.map_comp_assoc]
  change _ ≫ Spec.map (Y.presheaf.stalkSpecializes (specializes_of_eq hf)) ≫ _ = _
  rw [SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (f := f)

private theorem partial_comp_fromFunctionField {Z : Scheme.{u}}
    (p : X.PartialMap Y) [IsDominant p.hom] (q : Y.PartialMap Z) :
    (p.comp q).fromFunctionField =
      Spec.map p.toRationalMap.functionFieldMap ≫ q.fromFunctionField := by
  have hq : genericPoint Y ∈ q.domain :=
    (genericPoint_spec Y).mem_open_set_iff q.domain.isOpen |>.mpr
      ⟨q.dense_domain.nonempty.choose, trivial,
        q.dense_domain.nonempty.choose_spec⟩
  have hw : genericPoint X ∈ (p.comp q).domain :=
    (genericPoint_spec X).mem_open_set_iff (p.comp q).domain.isOpen |>.mpr
      ⟨(p.comp q).dense_domain.nonempty.choose, trivial,
        (p.comp q).dense_domain.nonempty.choose_spec⟩
  have hp : genericPoint X ∈ p.domain :=
    (genericPoint_spec X).mem_open_set_iff p.domain.isOpen |>.mpr
      ⟨p.dense_domain.nonempty.choose, trivial,
        p.dense_domain.nonempty.choose_spec⟩
  have hW : (p.comp q).domain ≤ p.domain := by
    change p.domain.ι ''ᵁ p.hom ⁻¹ᵁ q.domain ≤ p.domain
    exact p.domain.ι_image_le _
  have hsource :
      (p.comp q).domain.fromSpecStalkOfMem (genericPoint X) hw ≫ X.homOfLE hW =
        p.domain.fromSpecStalkOfMem (genericPoint X) hp := by
    rw [← cancel_mono p.domain.ι, Category.assoc, X.homOfLE_ι,
      Opens.fromSpecStalkOfMem_ι, Opens.fromSpecStalkOfMem_ι]
  have hfactor := spec_factorization p.fromFunctionField (partial_generic_image p)
  have hleft :
      (p.comp q).domain.fromSpecStalkOfMem (genericPoint X) hw ≫
          (p.domain.ι.isoImage (p.hom ⁻¹ᵁ q.domain)).inv ≫ p.hom ∣_ q.domain =
        Spec.map p.toRationalMap.functionFieldMap ≫
          q.domain.fromSpecStalkOfMem (genericPoint Y) hq := by
    change genericPoint X ∈ p.domain.ι ''ᵁ p.hom ⁻¹ᵁ q.domain at hw
    change p.domain.ι ''ᵁ p.hom ⁻¹ᵁ q.domain ≤ p.domain at hW
    rw [← cancel_mono q.domain.ι]
    change (p.domain.ι ''ᵁ p.hom ⁻¹ᵁ q.domain).fromSpecStalkOfMem
        (genericPoint X) hw ≫ (p.domain.ι.isoImage _).inv ≫
          p.hom ∣_ q.domain ≫ q.domain.ι = _
    rw [morphismRestrict_ι]
    rw [Category.assoc]
    rw [Opens.isoImage_ι_inv_ι_assoc]
    simp only [PartialMap.comp_domain] at hsource
    rw [← Category.assoc, hsource]
    rw [Opens.fromSpecStalkOfMem_ι]
    exact hfactor.symm
  change (p.comp q).domain.fromSpecStalkOfMem (genericPoint X) hw ≫
      (p.domain.ι.isoImage (p.hom ⁻¹ᵁ q.domain)).inv ≫ p.hom ∣_ q.domain ≫ q.hom =
    Spec.map p.toRationalMap.functionFieldMap ≫
      (q.domain.fromSpecStalkOfMem (genericPoint Y) hq ≫ q.hom)
  simp only [← Category.assoc, hleft]

/-- Rational composition on the source function-field spectrum factors through
the reversed function-field homomorphism of its first arrow, using Mathlib's
inverse-image dense-open composition of partial maps. -/
theorem RationalMap.fromFunctionField_comp {Z : Scheme.{u}}
    (r : X ⤏ Y) [r.IsDominant] (s : Y ⤏ Z) :
    (r.comp s).fromFunctionField =
      Spec.map r.functionFieldMap ≫ s.fromFunctionField := by
  obtain ⟨p, rfl⟩ := PartialMap.toRationalMap_surjective r
  obtain ⟨q, rfl⟩ := PartialMap.toRationalMap_surjective s
  haveI : IsDominant p.hom := (p.isDominant_toRationalMap_iff).mp inferInstance
  simpa only [RationalMap.toRationalMap_comp,
    RationalMap.fromFunctionField_toRationalMap] using
    partial_comp_fromFunctionField p q

/-- Pullback reverses composition of quotient rational maps. -/
@[simp] theorem RationalMap.functionFieldMap_comp {Z : Scheme.{u}} [IsIntegral Z]
    (r : X ⤏ Y) [r.IsDominant] (s : Y ⤏ Z) [s.IsDominant] :
    (r.comp s).functionFieldMap = s.functionFieldMap ≫ r.functionFieldMap := by
  apply Spec.map_injective
  rw [← cancel_mono (Z.fromSpecStalk (genericPoint Z))]
  calc
    Spec.map (r.comp s).functionFieldMap ≫ Z.fromSpecStalk (genericPoint Z) =
        (r.comp s).fromFunctionField :=
      spec_factorization _ (RationalMap.fromFunctionField_closedPoint _)
    _ = Spec.map r.functionFieldMap ≫ s.fromFunctionField :=
      RationalMap.fromFunctionField_comp r s
    _ = Spec.map r.functionFieldMap ≫ Spec.map s.functionFieldMap ≫
        Z.fromSpecStalk (genericPoint Z) := by
      rw [← spec_factorization s.fromFunctionField
        (RationalMap.fromFunctionField_closedPoint s)]
      rfl
    _ = Spec.map (s.functionFieldMap ≫ r.functionFieldMap) ≫
        Z.fromSpecStalk (genericPoint Z) := by rw [Spec.map_comp_assoc]

/-- The identity rational map acts identically on the function field. -/
@[simp] theorem RationalMap.functionFieldMap_id :
    (RationalMap.id X).functionFieldMap = 𝟙 X.functionField := by
  have hid : (RationalMap.id X).fromFunctionField =
      X.fromSpecStalk (genericPoint X) := by
    change ((𝟙 X : X ⟶ X).toPartialMap).fromSpecStalkOfMem _ = _
    rw [PartialMap.fromSpecStalkOfMem_toPartialMap, Category.comp_id]
  change (X.presheaf.stalkCongr
      (.of_eq (RationalMap.fromFunctionField_closedPoint (RationalMap.id X)).symm)).hom ≫
      Scheme.stalkClosedPointTo (RationalMap.id X).fromFunctionField = 𝟙 X.functionField
  rw [stalkClosedPointTo_congr (R := X.functionField)
    (RationalMap.id X).fromFunctionField (X.fromSpecStalk (genericPoint X)) hid
    (RationalMap.fromFunctionField_closedPoint (RationalMap.id X))
    fromSpecStalk_closedPoint]
  rw [Scheme.stalkClosedPointTo_fromSpecStalk]
  simp

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.IntegralDominantRationalScheme

/-- Function fields as a contravariant functor on integral schemes and dominant rational maps. -/
noncomputable def functionFieldFunctor :
    IntegralDominantRationalScheme.{u}ᵒᵖ ⥤ CommRingCat.{u} where
  obj X := X.unop.toScheme.functionField
  map f := f.unop.toRationalMap.functionFieldMap
  map_id X := by
    change (Scheme.RationalMap.id X.unop.toScheme).functionFieldMap =
      𝟙 X.unop.toScheme.functionField
    exact Scheme.RationalMap.functionFieldMap_id
  map_comp f g := by
    change (g.unop.toRationalMap.comp f.unop.toRationalMap).functionFieldMap =
      f.unop.toRationalMap.functionFieldMap ≫
        g.unop.toRationalMap.functionFieldMap
    exact Scheme.RationalMap.functionFieldMap_comp _ _

end AlgebraicGeometry.IntegralDominantRationalScheme
