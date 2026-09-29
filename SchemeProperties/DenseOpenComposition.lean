/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenPullback

@[expose] public section

/-!
# Composition controlled by dense-open pullback

The first partial or rational map need only pull back every dense open in its target
to a dense open in its ambient source. No dominance or irreducibility is required.
The construction uses the domain and morphism of mathlib's native composition.
-/

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

namespace PartialMap

/-- Compose partial maps when the first map pulls back dense opens densely. -/
@[simps]
noncomputable def compOfPullsDenseOpens (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) : X.PartialMap Z where
  domain := f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain)
  dense_domain := hf g.domain g.dense_domain
  hom := (f.domain.ι.isoImage _).inv ≫ f.hom ∣_ g.domain ≫ g.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma compOfPullsDenseOpens_restrict_left (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U ≤ f.domain)
    (g : Y.PartialMap Z) :
    (f.restrict U hU hU').compOfPullsDenseOpens
      ((f.pullsDenseOpens_restrict_iff U hU hU').2 hf) g =
      (f.compOfPullsDenseOpens hf g).restrict
        (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain) ⊓ U)
        ((f.compOfPullsDenseOpens hf g).dense_domain.inter_of_isOpen_right hU U.2)
        inf_le_left := by
  ext
  · simp [ι_image_homOfLE_eq_ι_image_inf]
  · simp [morphismRestrict_comp, isoImage_ι_inv_morphismRestrict_homOfLE_assoc, isoOfEq_hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma compOfPullsDenseOpens_restrict_right (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) (V : Y.Opens) (hV : Dense (V : Set Y)) (hV' : V ≤ g.domain) :
    f.compOfPullsDenseOpens hf (g.restrict V hV hV') =
      (f.compOfPullsDenseOpens hf g).restrict (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ V))
        (hf V hV) (f.domain.ι.image_mono (f.hom.preimage_mono hV')) := by
  ext
  · simp
  · simp [← f.domain.ι.isoImage_inv_homOfLE_assoc _ _ (f.hom.preimage_mono hV'),
      ← morphismRestrict_homOfLE_assoc f.hom _ _ hV']

set_option backward.defeqAttrib.useBackward true in
/-- Equivalence of first representatives is preserved by controlled composition. -/
theorem compOfPullsDenseOpens_equiv_of_equiv_left {f₁ f₂ : X.PartialMap Y}
    (hf₁ : f₁.PullsDenseOpens) (hf₂ : f₂.PullsDenseOpens) (h : f₁.equiv f₂)
    (g : Y.PartialMap Z) :
    (f₁.compOfPullsDenseOpens hf₁ g).equiv (f₂.compOfPullsDenseOpens hf₂ g) := by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  have e : f₁.restrict W hW hW₁ = f₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa using e)
  have heq :
      (f₁.restrict W hW hW₁).compOfPullsDenseOpens
          ((f₁.pullsDenseOpens_restrict_iff W hW hW₁).2 hf₁) g =
        (f₂.restrict W hW hW₂).compOfPullsDenseOpens
          ((f₂.pullsDenseOpens_restrict_iff W hW hW₂).2 hf₂) g := by
    simp only [← e]
  rw [compOfPullsDenseOpens_restrict_left (f := f₁) (hf := hf₁),
    compOfPullsDenseOpens_restrict_left (f := f₂) (hf := hf₂)] at heq
  exact equiv_of_restrict_eq _ _ heq

set_option backward.defeqAttrib.useBackward true in
/-- Equivalence of second representatives is preserved on a pulled-back dense open. -/
theorem compOfPullsDenseOpens_equiv_of_equiv_right (f : X.PartialMap Y)
    (hf : f.PullsDenseOpens) {g₁ g₂ : Y.PartialMap Z} (h : g₁.equiv g₂) :
    (f.compOfPullsDenseOpens hf g₁).equiv (f.compOfPullsDenseOpens hf g₂) := by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  have e : g₁.restrict W hW hW₁ = g₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa using e)
  have heq := congrArg (f.compOfPullsDenseOpens hf) e
  rw [compOfPullsDenseOpens_restrict_right,
    compOfPullsDenseOpens_restrict_right] at heq
  exact equiv_of_restrict_eq _ _ heq

/-- Controlled composition respects equivalence in both arguments. -/
theorem compOfPullsDenseOpens_equiv_of_equiv (f₁ f₂ : X.PartialMap Y)
    (hf₁ : f₁.PullsDenseOpens) (hf₂ : f₂.PullsDenseOpens) (h : f₁.equiv f₂)
    (g₁ g₂ : Y.PartialMap Z) (hg : g₁.equiv g₂) :
    (f₁.compOfPullsDenseOpens hf₁ g₁).equiv
      (f₂.compOfPullsDenseOpens hf₂ g₂) :=
  (compOfPullsDenseOpens_equiv_of_equiv_left hf₁ hf₂ h g₁).trans
    (compOfPullsDenseOpens_equiv_of_equiv_right f₂ hf₂ hg)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A total second morphism gives the existing partial-map composition. -/
theorem compOfPullsDenseOpens_toPartialMap (f : X.PartialMap Y)
    (hf : f.PullsDenseOpens) (g : Y ⟶ Z) :
    f.compOfPullsDenseOpens hf g.toPartialMap = f.compHom g := by
  ext1
  · simp
  · simp_rw [compOfPullsDenseOpens_hom, Hom.toPartialMap_domain,
      Hom.toPartialMap_hom, compHom_hom, topIso_hom, morphismRestrict_ι_assoc,
      f.domain.isoImage_ι_inv_ι_assoc, isoOfEq_hom]

/-- Under the original native assumptions, this is exactly native partial composition. -/
theorem compOfPullsDenseOpens_eq_comp [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) : f.compOfPullsDenseOpens hf g = f.comp g := by
  apply PartialMap.ext _ _ rfl
  dsimp [compOfPullsDenseOpens, comp]
  simp

end PartialMap

namespace RationalMap

/-- Compose existing quotient rational maps using an explicit first-map condition. -/
noncomputable def compOfPullsDenseOpens (f : X ⤏ Y) (hf : f.PullsDenseOpens)
    (g : Y ⤏ Z) : X ⤏ Z :=
  Quotient.liftOn g
    (fun h => (f.representative.compOfPullsDenseOpens
      (f.pullsDenseOpens_representative_iff.mpr hf) h).toRationalMap)
    (fun _ _ h => PartialMap.toRationalMap_eq_iff.mpr
      (PartialMap.compOfPullsDenseOpens_equiv_of_equiv_right _ _ h))

/-- The second partial-map representative computes the quotient composition. -/
theorem compOfPullsDenseOpens_def (f : X ⤏ Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) :
    f.compOfPullsDenseOpens hf g.toRationalMap =
      (f.representative.compOfPullsDenseOpens
        (f.pullsDenseOpens_representative_iff.mpr hf) g).toRationalMap := rfl

/-- The composite is independent of the first representative too. -/
theorem toRationalMap_compOfPullsDenseOpens (f : X.PartialMap Y)
    (hf : f.PullsDenseOpens) (g : Y.PartialMap Z) :
    f.toRationalMap.compOfPullsDenseOpens
        (f.pullsDenseOpens_toRationalMap_iff.mpr hf) g.toRationalMap =
      (f.compOfPullsDenseOpens hf g).toRationalMap := by
  rw [RationalMap.compOfPullsDenseOpens_def, PartialMap.toRationalMap_eq_iff]
  exact PartialMap.compOfPullsDenseOpens_equiv_of_equiv_left
    ((f.toRationalMap.pullsDenseOpens_representative_iff).mpr
      (f.pullsDenseOpens_toRationalMap_iff.mpr hf)) hf
    f.representative_toRationalMap_equiv g

/-- A total second morphism gives the existing rational-map composition. -/
theorem compOfPullsDenseOpens_toRationalMap (f : X ⤏ Y)
    (hf : f.PullsDenseOpens) (g : Y ⟶ Z) :
    f.compOfPullsDenseOpens hf g.toRationalMap = f.compHom g := by
  change f.compOfPullsDenseOpens hf g.toPartialMap.toRationalMap = f.compHom g
  rw [compOfPullsDenseOpens_def, PartialMap.compOfPullsDenseOpens_toPartialMap,
    RationalMap.compHom_toRationalMap, f.toRationalMap_representative]

/-- Under the native premises, the explicit-condition operation is native composition. -/
theorem compOfPullsDenseOpens_eq_comp [PreirreducibleSpace X] [Nonempty Y]
    (f : X ⤏ Y) [f.IsDominant] (hf : f.PullsDenseOpens) (g : Y ⤏ Z) :
    f.compOfPullsDenseOpens hf g = f.comp g := by
  induction g using Quotient.inductionOn with
  | _ g =>
    change f.compOfPullsDenseOpens hf g.toRationalMap = f.comp g.toRationalMap
    rw [compOfPullsDenseOpens_def, comp_def,
      PartialMap.compOfPullsDenseOpens_eq_comp]

end RationalMap

end AlgebraicGeometry.Scheme
