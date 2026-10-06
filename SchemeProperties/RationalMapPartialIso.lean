/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Justus Springer, Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Birational.Composition

public section

set_option warningAsError true

/-!
# Exact rational inverses as partial isomorphisms

Two independently chosen dominant rational maps inverse to one another admit a
partial isomorphism representing both exact quotient classes. Compatibility with
independently chosen structure maps requires only the forward quotient equation.

## References

- [Mathlib, `AlgebraicGeometry/Birational/Composition.lean`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Birational/Composition.lean#L46-L55):
  Justus Springer's partial-composition domain expression is adapted when
  constructing the exact inverse on dense opens.
- [Mathlib, `AlgebraicGeometry/Birational/RationalMap.lean`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Birational/RationalMap.lean#L370-L415):
  Andrew Yang's partial-map quotient and representative contracts are used.
- [Mathlib, `AlgebraicGeometry/Birational/Birational.lean`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Birational/Birational.lean#L37-L49):
  the native `Scheme.PartialIso` is the target interface, not an adapted proof
  of the exact two-sided realization.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private noncomputable def partialMapCompFirst {X Y Z : Scheme.{u}}
    [PreirreducibleSpace X] [Nonempty Y]
    (forward : X.PartialMap Y) [IsDominant forward.hom] (reverse : Y.PartialMap Z) :
    (forward.comp reverse).domain.toScheme ⟶ reverse.domain.toScheme :=
  (forward.domain.ι.isoImage (forward.hom ⁻¹ᵁ reverse.domain)).inv ≫
    forward.hom ∣_ reverse.domain

set_option backward.isDefEq.respectTransparency false in
private theorem partialMapCompFirst_fac {X Y Z : Scheme.{u}}
    [PreirreducibleSpace X] [Nonempty Y]
    (forward : X.PartialMap Y) [IsDominant forward.hom] (reverse : Y.PartialMap Z) :
    partialMapCompFirst forward reverse ≫ reverse.domain.ι =
      X.homOfLE (forward.domain.ι_image_le _) ≫ forward.hom := by
  dsimp only [partialMapCompFirst, PartialMap.comp_domain]
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
    Scheme.Opens.isoImage_ι_inv_ι]

private theorem partialMapComp_hom {X Y Z : Scheme.{u}}
    [PreirreducibleSpace X] [Nonempty Y]
    (forward : X.PartialMap Y) [IsDominant forward.hom] (reverse : Y.PartialMap Z) :
    (forward.comp reverse).hom = partialMapCompFirst forward reverse ≫ reverse.hom := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem partialMapComp_restrict_hom {X Y Z : Scheme.{u}}
    [PreirreducibleSpace X] [Nonempty Y]
    (forward : X.PartialMap Y) [IsDominant forward.hom] (reverse : Y.PartialMap Z)
    {U : X.Opens} (hU : U ≤ (forward.comp reverse).domain)
    {V : Y.Opens} (hV : V ≤ reverse.domain) (lift : U.toScheme ⟶ V.toScheme)
    (hlift : lift ≫ V.ι =
      X.homOfLE (hU.trans (forward.domain.ι_image_le _)) ≫ forward.hom) :
    X.homOfLE hU ≫ (forward.comp reverse).hom =
      lift ≫ Y.homOfLE hV ≫ reverse.hom := by
  have hfirst : X.homOfLE hU ≫ partialMapCompFirst forward reverse =
      lift ≫ Y.homOfLE hV := by
    rw [← cancel_mono reverse.domain.ι]
    simp only [Category.assoc, partialMapCompFirst_fac, Scheme.homOfLE_ι]
    rw [← Category.assoc, Scheme.homOfLE_homOfLE]
    exact hlift.symm
  rw [partialMapComp_hom, ← Category.assoc, hfirst, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem partialIso_of_partialMap_inverse {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X.PartialMap Y) (g : Y.PartialMap X)
    [IsDominant f.hom] [IsDominant g.hom]
    (hfg : f.toRationalMap.comp g.toRationalMap = RationalMap.id X)
    (hgf : g.toRationalMap.comp f.toRationalMap = RationalMap.id Y) :
    ∃ p : X.PartialIso Y,
      (∃ h : p.source ≤ f.domain,
        p.toPartialMap.hom = X.homOfLE h ≫ f.hom) ∧
      p.toRationalMap = f.toRationalMap ∧ p.symm.toRationalMap = g.toRationalMap := by
  have efg : (f.comp g).toRationalMap = (PartialMap.id X).toRationalMap := by
    simpa only [← RationalMap.toRationalMap_comp] using hfg
  have egf : (g.comp f).toRationalMap = (PartialMap.id Y).toRationalMap := by
    simpa only [← RationalMap.toRationalMap_comp] using hgf
  obtain ⟨A, hA, hAf, hAid, eA⟩ := PartialMap.toRationalMap_eq_iff.mp efg
  obtain ⟨B, hB, hBg, hBid, eB⟩ := PartialMap.toRationalMap_eq_iff.mp egf
  have hAf' : A ≤ f.domain := hAf.trans (f.domain.ι_image_le _)
  have hBg' : B ≤ g.domain := hBg.trans (g.domain.ι_image_le _)
  have hAeq : X.homOfLE hAf ≫ (f.comp g).hom = A.ι := by
    exact eA.trans (by
      change X.homOfLE hAid ≫ (X.topIso.hom ≫ 𝟙 X) = A.ι
      rw [Category.comp_id, Scheme.topIso_hom]
      exact Scheme.homOfLE_ι X hAid)
  have hBeq : Y.homOfLE hBg ≫ (g.comp f).hom = B.ι := by
    exact eB.trans (by
      change Y.homOfLE hBid ≫ (Y.topIso.hom ≫ 𝟙 Y) = B.ι
      rw [Category.comp_id, Scheme.topIso_hom]
      exact Scheme.homOfLE_ι Y hBid)
  let CX : X.Opens := f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ B)
  let CY : Y.Opens := g.domain.ι ''ᵁ (g.hom ⁻¹ᵁ A)
  have hCX : Dense (CX : Set X) := by
    simpa only [CX, PartialMap.comp_domain, PartialMap.restrict_domain] using
      (f.comp (g.restrict B hB hBg')).dense_domain
  have hCY : Dense (CY : Set Y) := by
    simpa only [CY, PartialMap.comp_domain, PartialMap.restrict_domain] using
      (g.comp (f.restrict A hA hAf')).dense_domain
  let U : X.Opens := A ⊓ CX
  let V : Y.Opens := B ⊓ CY
  have hU : Dense (U : Set X) := hA.inter_of_isOpen_right hCX CX.2
  have hV : Dense (V : Set Y) := hB.inter_of_isOpen_right hCY CY.2
  have hUA : U ≤ A := inf_le_left
  have hVB : V ≤ B := inf_le_left
  have hUf : U ≤ f.domain := hUA.trans hAf'
  have hVg : V ≤ g.domain := hVB.trans hBg'
  have hUfg : U ≤ (f.comp g).domain := hUA.trans hAf
  have hVgf : V ≤ (g.comp f).domain := hVB.trans hBg
  have hUeq : X.homOfLE hUfg ≫ (f.comp g).hom = U.ι := by
    calc
      _ = X.homOfLE hUA ≫ (X.homOfLE hAf ≫ (f.comp g).hom) := by
        rw [← Category.assoc, Scheme.homOfLE_homOfLE]
      _ = U.ι := by rw [hAeq, Scheme.homOfLE_ι]
  have hVeq : Y.homOfLE hVgf ≫ (g.comp f).hom = V.ι := by
    calc
      _ = Y.homOfLE hVB ≫ (Y.homOfLE hBg ≫ (g.comp f).hom) := by
        rw [← Category.assoc, Scheme.homOfLE_homOfLE]
      _ = V.ι := by rw [hBeq, Scheme.homOfLE_ι]
  let first : U.toScheme ⟶ g.domain.toScheme :=
    X.homOfLE hUfg ≫ partialMapCompFirst f g
  let second : V.toScheme ⟶ f.domain.toScheme :=
    Y.homOfLE hVgf ≫ partialMapCompFirst g f
  have hfirst_fac : first ≫ g.domain.ι = X.homOfLE hUf ≫ f.hom := by
    dsimp only [first]
    rw [Category.assoc, partialMapCompFirst_fac, ← Category.assoc,
      Scheme.homOfLE_homOfLE]
  have hsecond_fac : second ≫ f.domain.ι = Y.homOfLE hVg ≫ g.hom := by
    dsimp only [second]
    rw [Category.assoc, partialMapCompFirst_fac, ← Category.assoc,
      Scheme.homOfLE_homOfLE]
  have hfirst_reverse : first ≫ g.hom = U.ι := by
    dsimp only [first]
    rw [Category.assoc, ← partialMapComp_hom, hUeq]
  have hsecond_forward : second ≫ f.hom = V.ι := by
    dsimp only [second]
    rw [Category.assoc, ← partialMapComp_hom, hVeq]
  have hforward_range : Set.range (X.homOfLE hUf ≫ f.hom) ⊆ Set.range V.ι := by
    rintro _ ⟨point, rfl⟩
    have hmemberB : ((X.homOfLE hUf ≫ f.hom) point) ∈ B := by
      have hmemberCX : (X.homOfLE hUf point).1 ∈ (CX : Set X) := by
        simpa only [Scheme.homOfLE_apply] using point.property.2
      exact (Scheme.Opens.mem_ι_image_iff (U := f.domain)
        (x := X.homOfLE hUf point) (V := f.hom ⁻¹ᵁ B)).mp hmemberCX
    have hmemberCY : ((X.homOfLE hUf ≫ f.hom) point) ∈ CY := by
      rw [← hfirst_fac]
      change (first point).1 ∈ CY
      apply (Scheme.Opens.mem_ι_image_iff (U := g.domain)
        (x := first point) (V := g.hom ⁻¹ᵁ A)).mpr
      change g.hom (first point) ∈ A
      have hpoint : g.hom (first point) = (point.1 : X) := by
        have heq := congrArg (fun morphism : U.toScheme ⟶ X => morphism point)
          hfirst_reverse
        simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using heq
      rw [hpoint]
      exact hUA point.property
    rw [Scheme.Opens.range_ι, SetLike.mem_coe]
    exact ⟨hmemberB, hmemberCY⟩
  have hreverse_range : Set.range (Y.homOfLE hVg ≫ g.hom) ⊆ Set.range U.ι := by
    rintro _ ⟨point, rfl⟩
    have hmemberA : ((Y.homOfLE hVg ≫ g.hom) point) ∈ A := by
      have hmemberCY : (Y.homOfLE hVg point).1 ∈ (CY : Set Y) := by
        simpa only [Scheme.homOfLE_apply] using point.property.2
      exact (Scheme.Opens.mem_ι_image_iff (U := g.domain)
        (x := Y.homOfLE hVg point) (V := g.hom ⁻¹ᵁ A)).mp hmemberCY
    have hmemberCX : ((Y.homOfLE hVg ≫ g.hom) point) ∈ CX := by
      rw [← hsecond_fac]
      change (second point).1 ∈ CX
      apply (Scheme.Opens.mem_ι_image_iff (U := f.domain)
        (x := second point) (V := f.hom ⁻¹ᵁ B)).mpr
      change f.hom (second point) ∈ B
      have hpoint : f.hom (second point) = (point.1 : Y) := by
        have heq := congrArg (fun morphism : V.toScheme ⟶ Y => morphism point)
          hsecond_forward
        simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using heq
      rw [hpoint]
      exact hVB point.property
    rw [Scheme.Opens.range_ι, SetLike.mem_coe]
    exact ⟨hmemberA, hmemberCX⟩
  let liftForward : U.toScheme ⟶ V.toScheme :=
    IsOpenImmersion.lift V.ι (X.homOfLE hUf ≫ f.hom) hforward_range
  let liftReverse : V.toScheme ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι (Y.homOfLE hVg ≫ g.hom) hreverse_range
  have hforward_fac : liftForward ≫ V.ι = X.homOfLE hUf ≫ f.hom :=
    IsOpenImmersion.lift_fac V.ι _ hforward_range
  have hreverse_fac : liftReverse ≫ U.ι = Y.homOfLE hVg ≫ g.hom :=
    IsOpenImmersion.lift_fac U.ι _ hreverse_range
  have hforward_reverse : liftForward ≫ liftReverse = 𝟙 U.toScheme := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc, Category.id_comp, hreverse_fac]
    exact (partialMapComp_restrict_hom f g hUfg hVg liftForward hforward_fac).symm.trans
      hUeq
  have hreverse_forward : liftReverse ≫ liftForward = 𝟙 V.toScheme := by
    rw [← cancel_mono V.ι]
    simp only [Category.assoc, Category.id_comp, hforward_fac]
    exact (partialMapComp_restrict_hom g f hVgf hUf liftReverse hreverse_fac).symm.trans
      hVeq
  let partialIso : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := V
      dense_target := hV
      iso :=
        { hom := liftForward
          inv := liftReverse
          hom_inv_id := hforward_reverse
          inv_hom_id := hreverse_forward } }
  have hforward_map : partialIso.toPartialMap = f.restrict U hU hUf := by
    refine PartialMap.ext partialIso.toPartialMap (f.restrict U hU hUf)
      (by change U = U; rfl) ?_
    simpa only [Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp,
      PartialIso.toPartialMap_hom, PartialMap.restrict_hom] using hforward_fac
  have hreverse_map : partialIso.symm.toPartialMap = g.restrict V hV hVg := by
    refine PartialMap.ext partialIso.symm.toPartialMap (g.restrict V hV hVg)
      (by change V = V; rfl) ?_
    rw [Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp]
    change liftReverse ≫ U.ι = Y.homOfLE hVg ≫ g.hom
    exact hreverse_fac
  refine ⟨partialIso, ⟨hUf, hforward_fac⟩, ?_, ?_⟩
  · rw [show partialIso.toRationalMap = (f.restrict U hU hUf).toRationalMap from
      congrArg PartialMap.toRationalMap hforward_map]
    exact f.restrict_toRationalMap U hU hUf
  · rw [show partialIso.symm.toRationalMap = (g.restrict V hV hVg).toRationalMap from
      congrArg PartialMap.toRationalMap hreverse_map]
    exact g.restrict_toRationalMap V hV hVg

namespace RationalMap

/-- Dominant rational inverses are represented by a partial isomorphism on dense opens.
The two readbacks are the specified rational maps, not merely some birational witness. -/
theorem exists_partialIso_of_inverse {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (forward : X ⤏ Y) (reverse : Y ⤏ X) [forward.IsDominant] [reverse.IsDominant]
    (hforward_reverse : forward.comp reverse = RationalMap.id X)
    (hreverse_forward : reverse.comp forward = RationalMap.id Y) :
    ∃ partialIso : X.PartialIso Y,
      partialIso.toRationalMap = forward ∧ partialIso.symm.toRationalMap = reverse := by
  obtain ⟨partialIso, _, hforward, hreverse⟩ :=
    partialIso_of_partialMap_inverse forward.representative reverse.representative
      (by simpa only [RationalMap.toRationalMap_representative] using hforward_reverse)
      (by simpa only [RationalMap.toRationalMap_representative] using hreverse_forward)
  exact ⟨partialIso, by simpa using hforward, by simpa using hreverse⟩

section ChosenBase

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- A single quotient equation over independently chosen structure maps realizes
both prescribed rational inverses as a literal partial isomorphism over the base. -/
theorem exists_partialIso_of_inverse_over {X Y S : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    (sX : X ⟶ S) (sY : Y ⟶ S)
    (forward : X ⤏ Y) (reverse : Y ⤏ X)
    [forward.IsDominant] [reverse.IsDominant]
    (hforward_reverse : forward.comp reverse = RationalMap.id X)
    (hreverse_forward : reverse.comp forward = RationalMap.id Y)
    (hbase : forward.compHom sY = sX.toRationalMap) :
    ∃ partialIso : X.PartialIso Y,
      partialIso.toRationalMap = forward ∧
      partialIso.symm.toRationalMap = reverse ∧ partialIso.IsOver sX sY := by
  letI : X.Over S := .ofHom sX
  letI : Y.Over S := .ofHom sY
  have hreverse_base : reverse.compHom sX = sY.toRationalMap := by
    calc
      reverse.compHom sX = reverse.comp sX.toRationalMap :=
        (RationalMap.comp_toRationalMap reverse sX).symm
      _ = reverse.comp (forward.compHom sY) := by rw [hbase]
      _ = reverse.comp (forward.comp sY.toRationalMap) := by
        rw [RationalMap.comp_toRationalMap]
      _ = (reverse.comp forward).comp sY.toRationalMap :=
        (RationalMap.comp_assoc reverse forward sY.toRationalMap).symm
      _ = (RationalMap.id Y).comp sY.toRationalMap := by
        simp only [hreverse_forward]
      _ = sY.toRationalMap := RationalMap.id_comp _
  letI : forward.IsOver S := RationalMap.isOver_iff.mpr hbase
  letI : reverse.IsOver S := RationalMap.isOver_iff.mpr hreverse_base
  obtain ⟨forwardMap, hforwardOver, hforward_eq⟩ := forward.exists_partialMap_over S
  obtain ⟨reverseMap, hreverseOver, hreverse_eq⟩ := reverse.exists_partialMap_over S
  letI : forwardMap.IsOver S := hforwardOver
  haveI : IsDominant forwardMap.hom :=
    forwardMap.isDominant_toRationalMap_iff.mp (hforward_eq.symm ▸ inferInstance)
  haveI : IsDominant reverseMap.hom :=
    reverseMap.isDominant_toRationalMap_iff.mp (hreverse_eq.symm ▸ inferInstance)
  obtain ⟨partialIso, ⟨hsource, hhom⟩, hforward_eq', hreverse_eq'⟩ :=
    partialIso_of_partialMap_inverse forwardMap reverseMap
      (by simpa only [hforward_eq, hreverse_eq] using hforward_reverse)
      (by simpa only [hforward_eq, hreverse_eq] using hreverse_forward)
  have hforward_fac : forwardMap.hom ≫ sY = forwardMap.domain.ι ≫ sX :=
    (PartialMap.isOver_iff (S := S) (f := forwardMap)).mp hforwardOver
  have hover : partialIso.IsOver sX sY := by
    change partialIso.toPartialMap.hom ≫ sY = partialIso.source.ι ≫ sX
    rw [hhom, Category.assoc, hforward_fac, ← Category.assoc,
      Scheme.homOfLE_ι]
  exact ⟨partialIso, hforward_eq'.trans hforward_eq,
    hreverse_eq'.trans hreverse_eq, hover⟩

end ChosenBase

end RationalMap

namespace PartialIso

set_option linter.style.haveILetI false in
private instance isDominant_toPartialMap_hom {X Y : Scheme.{u}}
    (partialIso : X.PartialIso Y) : IsDominant partialIso.toPartialMap.hom := by
  change IsDominant (partialIso.iso.hom ≫ partialIso.target.ι)
  haveI : IsDominant partialIso.target.ι :=
    Opens.isDominant_ι partialIso.dense_target
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem toPartialMap_comp_symm {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (partialIso : X.PartialIso Y) :
    partialIso.toPartialMap.comp partialIso.symm.toPartialMap =
      (PartialMap.id X).restrict partialIso.source partialIso.dense_source (by simp) := by
  have hd : (partialIso.toPartialMap.comp partialIso.symm.toPartialMap).domain =
      partialIso.source := by
    simp [PartialMap.comp_domain, PartialIso.toPartialMap, PartialIso.symm]
  have hfirst : partialMapCompFirst partialIso.toPartialMap partialIso.symm.toPartialMap =
      X.homOfLE (partialIso.source.ι_image_le _) ≫ partialIso.iso.hom := by
    rw [← cancel_mono partialIso.target.ι]
    have hfac := partialMapCompFirst_fac partialIso.toPartialMap partialIso.symm.toPartialMap
    change partialMapCompFirst partialIso.toPartialMap partialIso.symm.toPartialMap ≫
      partialIso.target.ι = X.homOfLE (partialIso.source.ι_image_le _) ≫
      (partialIso.iso.hom ≫ partialIso.target.ι) at hfac
    simpa only [Category.assoc] using hfac
  have hcomp : (partialIso.toPartialMap.comp partialIso.symm.toPartialMap).hom =
      (partialIso.toPartialMap.comp partialIso.symm.toPartialMap).domain.ι := by
    calc
      _ = (X.homOfLE (partialIso.source.ι_image_le _) ≫ partialIso.iso.hom) ≫
          (partialIso.iso.inv ≫ partialIso.source.ι) := by
            rw [partialMapComp_hom, hfirst]
            rfl
      _ = (partialIso.toPartialMap.comp partialIso.symm.toPartialMap).domain.ι := by
        calc
          _ = (X.homOfLE (partialIso.source.ι_image_le _) ≫
              (partialIso.iso.hom ≫ partialIso.iso.inv)) ≫ partialIso.source.ι := by
                simp only [Category.assoc]
          _ = X.homOfLE (partialIso.source.ι_image_le _) ≫ partialIso.source.ι := by
                rw [partialIso.iso.hom_inv_id, Category.comp_id]
          _ = _ := Scheme.homOfLE_ι X _
  refine PartialMap.ext _ _ hd ?_
  have hid : ((PartialMap.id X).restrict partialIso.source partialIso.dense_source
      (by simp)).hom = partialIso.source.ι := by
    change X.homOfLE (by simp : partialIso.source ≤ (⊤ : X.Opens)) ≫
      (X.topIso.hom ≫ 𝟙 X) = partialIso.source.ι
    rw [Category.comp_id, Scheme.topIso_hom]
    exact Scheme.homOfLE_ι X _
  rw [hcomp, hid]
  exact (Scheme.isoOfEq_hom_ι X hd).symm

/-- The exact forward rational quotient of a partial isomorphism is dominant. -/
instance toRationalMap_isDominant {X Y : Scheme.{u}} (partialIso : X.PartialIso Y) :
    partialIso.toRationalMap.IsDominant :=
  partialIso.toPartialMap.isDominant_toRationalMap_iff.mpr inferInstance

/-- Forward composition with the exact reverse quotient is the rational identity. -/
theorem toRationalMap_comp_symm {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (partialIso : X.PartialIso Y) :
    partialIso.toRationalMap.comp partialIso.symm.toRationalMap = RationalMap.id X := by
  change partialIso.toPartialMap.toRationalMap.comp partialIso.symm.toPartialMap.toRationalMap =
    (PartialMap.id X).toRationalMap
  rw [RationalMap.toRationalMap_comp, partialIso.toPartialMap_comp_symm,
    PartialMap.restrict_toRationalMap]

/-- Reverse composition with the exact forward quotient is the rational identity. -/
theorem symm_toRationalMap_comp {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (partialIso : X.PartialIso Y) :
    partialIso.symm.toRationalMap.comp partialIso.toRationalMap = RationalMap.id Y := by
  have hs : partialIso.symm.symm = partialIso := by
    cases partialIso
    simp [PartialIso.symm]
  simpa only [hs] using partialIso.symm.toRationalMap_comp_symm

section ChosenBase

set_option linter.style.haveILetI false

/-- Literal compatibility of a partial isomorphism with two independently chosen
structure maps implies compatibility of its exact forward rational quotient. -/
theorem toRationalMap_compHom_of_isOver {X Y S : Scheme.{u}}
    (partialIso : X.PartialIso Y) (sX : X ⟶ S) (sY : Y ⟶ S)
    (hover : partialIso.IsOver sX sY) :
    partialIso.toRationalMap.compHom sY = sX.toRationalMap := by
  letI : X.Over S := .ofHom sX
  letI : Y.Over S := .ofHom sY
  haveI : partialIso.toPartialMap.IsOver S := ⟨hover⟩
  exact RationalMap.isOver_iff.mp inferInstance

/-- Literal over-base compatibility also holds on the exact reverse rational quotient. -/
theorem symm_toRationalMap_compHom_of_isOver {X Y S : Scheme.{u}}
    (partialIso : X.PartialIso Y) (sX : X ⟶ S) (sY : Y ⟶ S)
    (hover : partialIso.IsOver sX sY) :
    partialIso.symm.toRationalMap.compHom sX = sY.toRationalMap :=
  partialIso.symm.toRationalMap_compHom_of_isOver sY sX hover.symm

end ChosenBase

end PartialIso

end AlgebraicGeometry.Scheme
