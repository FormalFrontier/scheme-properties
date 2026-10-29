/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.MaximalPointSpace

/-!
# Characterizing the maximal-point structure sheaf

A full sheaf of commutative rings on the maximal-point space is determined by
its coordinate-ring action and its localization property on principal opens.
The comparison is constructed by the universal property of localization and
extended by Mathlib's basis-extension theorem. In particular, a full sheaf
comparison is a conclusion rather than part of the input. Coordinate compatibility
on every open follows by the sheaf's local equality criterion. No reducedness or
nonemptiness hypothesis is imposed; the empty principal opens are included.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory TopCat TopologicalSpace Opposite

namespace AlgebraicGeometry.Spec

variable (R : Type u) [CommRing R] [IsJacobsonRing R]

set_option backward.isDefEq.respectTransparency false in
/-- The principal opens form a basis on the maximal-point subspace. -/
lemma maximalPointBasicOpen_isBasis :
    Opens.IsBasis (Set.range (maximalPointBasicOpen R)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  have hx' : (x.val : PrimeSpectrum R) ∈
      (Opens.closedPointsOrderIso (PrimeSpectrum R)).symm U :=
    Opens.val_mem_closedPointsOrderIso_symm_apply.mpr hx
  obtain ⟨V, ⟨f, rfl⟩, hxf, hfU⟩ :=
    (Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) hx'
  refine ⟨maximalPointBasicOpen R f, ⟨f, rfl⟩, hxf, ?_⟩
  intro y hy
  exact Opens.val_mem_closedPointsOrderIso_symm_apply.mp (hfU hy)

variable (F : Sheaf CommRingCat.{u} (maximalPointSpace R).toTopCat)
variable [∀ U, Algebra R (F.obj.obj U)]
variable [∀ f : R, IsLocalization.Away f (F.obj.obj (op (maximalPointBasicOpen R f)))]
variable (hF : ∀ {U V : Opens (maximalPointSpace R)} (i : U ⟶ V) (r : R),
  F.obj.map i.op (algebraMap R _ r) = algebraMap R _ r)

/-- The localization data determine the comparison algebra isomorphism on a
principal open. -/
def localizationSheafBasicOpenIso (f : R) :
    (maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R f)) ≃ₐ[R]
      F.obj.obj (op (maximalPointBasicOpen R f)) :=
  IsLocalization.algEquiv (Submonoid.powers f) _ _

/-- The principal-open comparison preserves coordinates through its underlying
ring homomorphism. -/
lemma localizationSheafBasicOpenIso_algebraMap (f r : R) :
    (localizationSheafBasicOpenIso R F f).toRingHom
        (algebraMap R ((maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R f))) r) =
      algebraMap R (F.obj.obj (op (maximalPointBasicOpen R f))) r :=
  (localizationSheafBasicOpenIso R F f).commutes r

include hF in
set_option backward.isDefEq.respectTransparency false in
/-- The principal-open comparison commutes with restriction whenever the supplied
coordinate actions commute with restriction. -/
@[reassoc]
lemma localizationSheafBasicOpenIso_naturality (f g : R)
    (i : maximalPointBasicOpen R g ⟶ maximalPointBasicOpen R f) :
    (maximalPointSpace R).presheaf.map i.op ≫
        CommRingCat.ofHom
          (R := (maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R g)))
          (S := F.obj.obj (op (maximalPointBasicOpen R g)))
          (localizationSheafBasicOpenIso R F g).toRingHom =
      CommRingCat.ofHom
        (R := (maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R f)))
        (S := F.obj.obj (op (maximalPointBasicOpen R f)))
        (localizationSheafBasicOpenIso R F f).toRingHom ≫ F.obj.map i.op := by
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
    (S := (maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R f)))
  ext r
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  calc
    _ = (localizationSheafBasicOpenIso R F g).toRingHom
        (algebraMap R ((maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R g))) r) :=
      congrArg (localizationSheafBasicOpenIso R F g).toRingHom
        (maximalPoint_map_algebraMap R i r)
    _ = algebraMap R (F.obj.obj (op (maximalPointBasicOpen R g))) r :=
      localizationSheafBasicOpenIso_algebraMap R F g r
    _ = F.obj.map i.op (algebraMap R (F.obj.obj (op (maximalPointBasicOpen R f))) r) :=
      (hF i r).symm
    _ = _ := congrArg (F.obj.map i.op) (localizationSheafBasicOpenIso_algebraMap R F f r).symm

set_option backward.isDefEq.respectTransparency false in
/-- The comparison constructed from coordinate-linear localization data on a basis. -/
def localizationSheafComparison : (maximalPointSpace R).sheaf ⟶ F :=
  ObjectProperty.homMk
    (TopCat.Sheaf.restrictHomEquivHom (maximalPointSpace R).presheaf F
      (maximalPointBasicOpen_isBasis R)
      { app f := CommRingCat.ofHom
          (localizationSheafBasicOpenIso R F (show R from f.unop)).toRingHom
        naturality {f g} i := localizationSheafBasicOpenIso_naturality R F hF
          (show R from f.unop) (show R from g.unop) i.unop.hom })

/-- On each principal open the comparison is the unique localization algebra isomorphism. -/
@[simp]
lemma localizationSheafComparison_app (f : R) :
    (localizationSheafComparison R F hF).hom.app (op (maximalPointBasicOpen R f)) =
      CommRingCat.ofHom (localizationSheafBasicOpenIso R F f).toRingHom := by
  dsimp only [localizationSheafComparison]
  exact TopCat.Sheaf.extend_hom_app (maximalPointSpace R).presheaf F
    (maximalPointBasicOpen_isBasis R) _ f

instance localizationSheafComparison_isIso : IsIso (localizationSheafComparison R F hF) := by
  refine TopCat.Sheaf.isIso_iff_isIso_basis (φ := localizationSheafComparison R F hF)
    (maximalPointBasicOpen_isBasis R) (fun f ↦ ?_)
  rw [localizationSheafComparison_app]
  exact (localizationSheafBasicOpenIso R F f).toRingEquiv.toCommRingCatIso.isIso_hom

/-- A full sheaf with compatible coordinate actions and localization basic-open rings
is isomorphic to the maximal-point structure sheaf. -/
def localizationSheafIso : (maximalPointSpace R).sheaf ≅ F :=
  asIso (localizationSheafComparison R F hF)

set_option backward.isDefEq.respectTransparency false in
/-- The extended full sheaf comparison preserves coordinates on every open. -/
@[simp]
lemma localizationSheafComparison_algebraMap (W : Opens (maximalPointSpace R)) (r : R) :
    CommRingCat.Hom.hom (R := (maximalPointSpace R).presheaf.obj (op W))
        ((localizationSheafComparison R F hF).hom.app (op W))
        (algebraMap R ((maximalPointSpace R).presheaf.obj (op W)) r) =
      algebraMap R (F.obj.obj (op W)) r := by
  apply TopCat.Presheaf.IsSheaf.section_ext (F := F.obj) F.property
  intro x hx
  obtain ⟨V, ⟨f, rfl⟩, hxV, hVW⟩ :=
    (Opens.isBasis_iff_nbhd.mp (maximalPointBasicOpen_isBasis R)) hx
  refine ⟨_, hVW, hxV, ?_⟩
  have h := congrArg
    (fun e : (maximalPointSpace R).presheaf.obj (op W) ⟶
        F.obj.obj (op (maximalPointBasicOpen R f)) =>
      e (algebraMap R ((maximalPointSpace R).presheaf.obj (op W)) r))
    ((localizationSheafComparison R F hF).hom.naturality (homOfLE hVW).op)
  calc
    _ = (localizationSheafComparison R F hF).hom.app (op (maximalPointBasicOpen R f))
        ((maximalPointSpace R).presheaf.map (homOfLE hVW).op
          (algebraMap R ((maximalPointSpace R).presheaf.obj (op W)) r)) := by
      simpa only [CommRingCat.comp_apply, SheafedSpace.sheaf_obj] using h.symm
    _ = (localizationSheafComparison R F hF).hom.app (op (maximalPointBasicOpen R f))
        (algebraMap R ((maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R f))) r) :=
      congrArg ((localizationSheafComparison R F hF).hom.app (op (maximalPointBasicOpen R f)))
        (maximalPoint_map_algebraMap R (homOfLE hVW) r)
    _ = algebraMap R (F.obj.obj (op (maximalPointBasicOpen R f))) r := by
      rw [localizationSheafComparison_app]
      exact localizationSheafBasicOpenIso_algebraMap R F f r
    _ = _ := (hF (homOfLE hVW) r).symm

/-- The comparison is an algebra isomorphism on every open, and hence also
preserves any compatible base scalar action. -/
def localizationSheafOpenIso (W : Opens (maximalPointSpace R)) :
    (maximalPointSpace R).presheaf.obj (op W) ≃ₐ[R] F.obj.obj (op W) where
  __ := (((TopCat.Sheaf.forget CommRingCat.{u} (maximalPointSpace R).toTopCat).mapIso
    (localizationSheafIso R F hF)).app (op W)).commRingCatIsoToRingEquiv
  commutes' r := localizationSheafComparison_algebraMap R F hF W r

/-- The open algebra isomorphism has the constructed comparison as its underlying map. -/
@[simp]
lemma localizationSheafOpenIso_apply (W : Opens (maximalPointSpace R))
    (s : (maximalPointSpace R).presheaf.obj (op W)) :
    localizationSheafOpenIso R F hF W s =
      (localizationSheafComparison R F hF).hom.app (op W) s := rfl

/-- A coordinate-linear map on each principal open is forced to be the comparison. -/
lemma localizationSheafComparison_unique
    (ψ : (maximalPointSpace R).sheaf ⟶ F)
    (hψ : ∀ f : R, ((ψ.hom.app (op (maximalPointBasicOpen R f))).hom).comp
      (algebraMap R ((maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R f)))) =
        algebraMap R (F.obj.obj (op (maximalPointBasicOpen R f)))) :
    ψ = localizationSheafComparison R F hF := by
  apply ObjectProperty.hom_ext
  apply TopCat.Sheaf.hom_ext (maximalPointSpace R).presheaf F
    (maximalPointBasicOpen_isBasis R)
  intro f
  rw [localizationSheafComparison_app]
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
    (S := (maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R f)))
  refine (hψ f).trans ?_
  ext r
  exact (localizationSheafBasicOpenIso_algebraMap R F f r).symm

end AlgebraicGeometry.Spec
