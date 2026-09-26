/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
public import Mathlib.Topology.Sheaves.Abelian

public section

set_option warningAsError true

/-!
# The abelian category of quasicoherent modules

For an arbitrary scheme `X`, this file proves that the native full subcategory
cut out by `SheafOfModules.isQuasicoherent X.ringCatSheaf` contains zero and is
closed under finite products, kernels, and cokernels. The generic full-subcategory
theorem therefore equips it with an abelian-category instance.

The key affine input is that `AlgebraicGeometry.tilde.functor R` preserves finite
limits. Its essential image is the quasicoherent modules on `Spec R`. The result
is then transported over the affine opens of an arbitrary scheme using the
affine-open-cover criterion from `SchemeProperties.Quasicoherent`.
-/

open CategoryTheory Limits TopologicalSpace ZeroObject

namespace AlgebraicGeometry

universe u w

private noncomputable def actualToStalk (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) (x : Spec R) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M ⟶
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := Spec R) x).obj
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} (Spec R)).obj
          ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tilde M))) :=
  (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map (tilde.toStalk M x)

set_option backward.isDefEq.respectTransparency.types false in
private theorem actualToStalk_naturality (R : CommRingCat.{u})
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (x : Spec R) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map f ≫ actualToStalk R N x =
      actualToStalk R M x ≫
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := Spec R) x).map
        (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map
          ((tilde.functor R).map f)).hom)) := by
  ext m
  let φ := (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map
    ((tilde.functor R).map f)).hom)
  have h := TopCat.Presheaf.stalkFunctor_map_germ (C := AddCommGrpCat.{u})
    (f := φ) ⊤ x (by simp)
  have hm := congrArg (fun q ↦ q.hom (StructureSheaf.toOpenₗ R M ⊤ m)) h
  have htop : φ.app (.op ⊤) (StructureSheaf.toOpenₗ R M ⊤ m) =
      StructureSheaf.toOpenₗ R N ⊤ (f m) := by
    dsimp [φ, SheafOfModules.toSheaf, tilde.functor, tilde.map,
      SpecModulesToSheafFullyFaithful, tilde.modulesSpecToSheafIso]
    change (StructureSheaf.comapₗ f.hom ⊤ ⊤ (by simp))
      (StructureSheaf.toOpenₗ R M ⊤ m) = StructureSheaf.toOpenₗ R N ⊤ (f m)
    simpa [StructureSheaf.toOpenₗ_eq_const] using
      (StructureSheaf.comapₗ_const f.hom ⊤ ⊤ (by simp) m 1 (by simp))
  dsimp [actualToStalk, tilde.toStalk, StructureSheaf.toStalkₗ]
  exact (congrArg (fun z ↦
    (TopCat.Presheaf.germ
      ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj
        ((tilde.functor R).obj N)).obj ⊤ x (by simp)).hom z) htop.symm).trans hm.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option linter.style.haveILetI false in
private noncomputable def tildeGermLinear (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) (U : (Spec R).Opens) (x : Spec R) (hxU : x ∈ U) :
    (tilde M).presheaf.obj (.op U) →ₗ[R] (tilde M).presheaf.stalk x where
  toFun := (TopCat.Presheaf.germ (tilde M).presheaf U x hxU).hom
  map_add' := by simp
  map_smul' r m := by
    let R' : TopCat.Presheaf CommRingCat.{u} (Spec R) := (Spec R).presheaf
    let M' : PresheafOfModules (R' ⋙ forget₂ CommRingCat RingCat) := (tilde M).val
    letI : Module ↑(TopCat.Presheaf.stalk (C := CommRingCat.{u}) R' x)
        ↑((tilde M).presheaf.stalk x) := by
      change Module ↑(TopCat.Presheaf.stalk (C := CommRingCat.{u}) R' x)
        ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M'.presheaf x)
      infer_instance
    let a : R'.obj (.op U) := algebraMap R (R'.obj (.op U)) r
    have hmorph : CommRingCat.ofHom (algebraMap R (R'.obj (.op U))) ≫
          TopCat.Presheaf.germ (C := CommRingCat.{u}) R' U x hxU =
        StructureSheaf.toStalk R x := by
      dsimp [R']
      rw [Category.assoc, TopCat.Presheaf.germ_res]
      rfl
    have hring : (TopCat.Presheaf.germ (C := CommRingCat.{u}) R' U x hxU).hom a =
        StructureSheaf.toStalk R x r := congrArg (fun q ↦ q.hom r) hmorph
    calc
      TopCat.Presheaf.germ (tilde M).presheaf U x hxU (r • m) =
          TopCat.Presheaf.germ (tilde M).presheaf U x hxU (a • m) := by congr 1
      _ = (TopCat.Presheaf.germ (C := CommRingCat.{u}) R' U x hxU).hom a •
          TopCat.Presheaf.germ (tilde M).presheaf U x hxU m := M'.germ_smul x U hxU _ _
      _ = r • TopCat.Presheaf.germ (tilde M).presheaf U x hxU m := by
        rw [hring]
        rfl

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def tildeStalkLinearEquiv (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) (x : Spec R) :
    (tilde M).presheaf.stalk x ≃ₗ[R]
      (modulesSpecToSheaf.obj (tilde M)).presheaf.stalk x where
  __ := (colimit.isoColimitCocone
    ⟨_, isColimitOfPreserves (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
      (colimit.isColimit ((OpenNhds.inclusion x).op ⋙
        (modulesSpecToSheaf.obj (tilde M)).presheaf))⟩).addCommGroupIsoToAddEquiv
  map_smul' r m := by
    let α : (tilde M).presheaf.stalk x ≅
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
          ((modulesSpecToSheaf.obj (tilde M)).presheaf.stalk x) :=
      colimit.isoColimitCocone
        ⟨_, isColimitOfPreserves (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
          (colimit.isColimit ((OpenNhds.inclusion x).op ⋙
            (modulesSpecToSheaf.obj (tilde M)).presheaf))⟩
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ m
    have hα : TopCat.Presheaf.germ (tilde M).presheaf U x hxU ≫ α.hom =
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
          ((modulesSpecToSheaf.obj (tilde M)).presheaf.germ U x hxU) :=
      colimit.isoColimitCocone_ι_hom (C := AddCommGrpCat.{u}) ..
    have hs (m : _) : α.hom (TopCat.Presheaf.germ (tilde M).presheaf U x hxU m) =
        (modulesSpecToSheaf.obj (tilde M)).presheaf.germ U x hxU m := congr($hα m)
    change α.hom (r • tildeGermLinear R M U x hxU s) =
      r • (show (modulesSpecToSheaf.obj (tilde M)).presheaf.stalk x from _)
    rw [← map_smul]
    refine (hs _).trans ?_
    dsimp [StructureSheaf.toStalk]
    erw [hs]
    exact ((modulesSpecToSheaf.obj (tilde M)).presheaf.germ U x hxU).hom.map_smul _ _

set_option backward.isDefEq.respectTransparency.types false in
private theorem tildeStalkLinearEquiv_germ (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) (x : Spec R) (U : (Spec R).Opens) (hxU : x ∈ U)
    (s : (tilde M).presheaf.obj (.op U)) :
    tildeStalkLinearEquiv R M x
        (TopCat.Presheaf.germ (tilde M).presheaf U x hxU s) =
      (modulesSpecToSheaf.obj (tilde M)).presheaf.germ U x hxU s := by
  let α : (tilde M).presheaf.stalk x ≅
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        ((modulesSpecToSheaf.obj (tilde M)).presheaf.stalk x) :=
    colimit.isoColimitCocone
      ⟨_, isColimitOfPreserves (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
        (colimit.isColimit ((OpenNhds.inclusion x).op ⋙
          (modulesSpecToSheaf.obj (tilde M)).presheaf))⟩
  change α.hom (TopCat.Presheaf.germ (tilde M).presheaf U x hxU s) = _
  have hα : TopCat.Presheaf.germ (tilde M).presheaf U x hxU ≫ α.hom =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((modulesSpecToSheaf.obj (tilde M)).presheaf.germ U x hxU) :=
    colimit.isoColimitCocone_ι_hom (C := AddCommGrpCat.{u}) ..
  exact congr($hα s)

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def tildeStalkMap (R : CommRingCat.{u})
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (x : Spec R) :
    (tilde M).presheaf.stalk x →ₗ[R] (tilde N).presheaf.stalk x :=
  (tildeStalkLinearEquiv R N x).symm.toLinearMap.comp <|
    (((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) (X := Spec R) x).map
      (modulesSpecToSheaf.map ((tilde.functor R).map f)).hom).hom.comp
        (tildeStalkLinearEquiv R M x).toLinearMap)

set_option backward.isDefEq.respectTransparency.types false in
private theorem tildeStalkMap_apply (R : CommRingCat.{u})
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (x : Spec R) :
    ∀ m, tildeStalkMap R f x m =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := Spec R) x).map
        (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map
          ((tilde.functor R).map f)).hom)).hom m := by
  intro m
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (tilde M).presheaf m
  dsimp [tildeStalkMap]
  apply (tildeStalkLinearEquiv R N x).injective
  rw [LinearEquiv.apply_symm_apply]
  have hfixed := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (C := ModuleCat.{u} R) U x hxU (modulesSpecToSheaf.map ((tilde.functor R).map f)).hom s
  have hadd := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (C := AddCommGrpCat.{u}) U x hxU
      (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map ((tilde.functor R).map f)).hom) s
  change (((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) (X := Spec R) x).map
      (modulesSpecToSheaf.map ((tilde.functor R).map f)).hom).hom
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.germ U x hxU s)) =
    (modulesSpecToSheaf.obj (tilde N)).presheaf.germ U x hxU
      ((modulesSpecToSheaf.map ((tilde.functor R).map f)).hom.app (.op U) s) at hfixed
  change (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := Spec R) x).map
      (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map
        ((tilde.functor R).map f)).hom)).hom
      (TopCat.Presheaf.germ (tilde M).presheaf U x hxU s)) =
    TopCat.Presheaf.germ (tilde N).presheaf U x hxU
      ((((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map
        ((tilde.functor R).map f)).hom.app (.op U)) s) at hadd
  change (((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) (X := Spec R) x).map
      (modulesSpecToSheaf.map ((tilde.functor R).map f)).hom).hom
      (tildeStalkLinearEquiv R M x
        (TopCat.Presheaf.germ (tilde M).presheaf U x hxU s))) =
    tildeStalkLinearEquiv R N x
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := Spec R) x).map
        (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map
          ((tilde.functor R).map f)).hom)).hom
        (TopCat.Presheaf.germ (tilde M).presheaf U x hxU s))
  rw [tildeStalkLinearEquiv_germ, hfixed, hadd, tildeStalkLinearEquiv_germ]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem tildeStalkMap_eq_localizedMap (R : CommRingCat.{u})
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (x : Spec R) :
    tildeStalkMap R f x =
      IsLocalizedModule.map x.asIdeal.primeCompl (tilde.toStalk M x).hom
        (tilde.toStalk N x).hom f.hom := by
  apply IsLocalizedModule.ext x.asIdeal.primeCompl (tilde.toStalk M x).hom
    (IsLocalizedModule.map_units (tilde.toStalk N x).hom)
  ext m
  rw [LinearMap.comp_apply, LinearMap.comp_apply, IsLocalizedModule.map_apply,
    tildeStalkMap_apply]
  have h := actualToStalk_naturality R f x
  have hm := congrArg (fun q ↦ q.hom m) h
  change (tilde.toStalk N x).hom (f.hom m) =
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := Spec R) x).map
      (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map
        ((tilde.functor R).map f)).hom)).hom ((tilde.toStalk M x).hom m) at hm
  exact hm.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option linter.style.haveILetI false in
private theorem tildeFunctorPreservesMonomorphisms (R : CommRingCat.{u}) :
    (tilde.functor R).PreservesMonomorphisms where
  preserves {M N} f hf := by
    apply (SheafOfModules.toSheaf (Spec R).ringCatSheaf).mono_of_mono_map
    letI (x : Spec R) : Mono
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := Spec R) x).map
          (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map
            ((tilde.functor R).map f)).hom)) := by
      apply ConcreteCategory.mono_of_injective
      intro a b hab
      apply (show Function.Injective (tildeStalkMap R f x) by
        rw [tildeStalkMap_eq_localizedMap]
        exact IsLocalizedModule.map_injective x.asIdeal.primeCompl
          (tilde.toStalk M x).hom (tilde.toStalk N x).hom f.hom
          ((ModuleCat.mono_iff_injective f).mp hf))
      rw [tildeStalkMap_apply, tildeStalkMap_apply]
      exact hab
    exact TopCat.Presheaf.mono_of_stalk_mono _

set_option linter.style.haveILetI false in
/-- The affine tilde functor preserves finite limits. -/
noncomputable instance tildeFunctor_preservesFiniteLimits (R : CommRingCat.{u}) :
    PreservesFiniteLimits (tilde.functor R) := by
  letI : (tilde.functor R).PreservesMonomorphisms := tildeFunctorPreservesMonomorphisms R
  letI : (tilde.functor R).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact Functor.preservesFiniteLimits_of_preservesHomology _

namespace Scheme.Modules

set_option linter.style.haveILetI false in
/-- Restriction of modules along an open immersion preserves finite limits. -/
noncomputable instance restrictFunctor_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (restrictFunctor f) where
  preservesFiniteLimits J _ _ := by
    letI : HasLimitsOfShape J Y.Modules := HasFiniteLimits.out J
    constructor
    intro K
    letI : HasLimit K := (inferInstance : HasLimitsOfShape J Y.Modules).has_limit K
    let c : Cone K := limit.cone K
    let hc : IsLimit c := limit.isLimit K
    apply preservesLimit_of_preserves_limit_cone hc
    let hReflect : ReflectsLimit (K ⋙ restrictFunctor f)
        (SheafOfModules.forget X.ringCatSheaf) :=
      (fullyFaithful_reflectsLimits
        (SheafOfModules.forget X.ringCatSheaf)).reflectsLimitsOfShape.reflectsLimit
    refine (hReflect.reflects ?_).some
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro V
    letI : PreservesLimit K (SheafOfModules.evaluation Y.ringCatSheaf
        ((Scheme.Hom.opensFunctor f).op.obj V)) :=
      SheafOfModules.evaluationPreservesLimit _ _
    change IsLimit ((ModuleCat.restrictScalars _).mapCone
      ((SheafOfModules.evaluation Y.ringCatSheaf _).mapCone c))
    exact isLimitOfPreserves (ModuleCat.restrictScalars _) <|
      ((SheafOfModules.evaluationPreservesLimit K _).preserves hc).some

set_option backward.isDefEq.respectTransparency.types false in
set_option linter.style.haveILetI false in
/-- A finite limit of quasicoherent modules on an arbitrary scheme is
quasicoherent. -/
theorem isQuasicoherent_of_isLimit (X : Scheme.{u}) {J : Type w}
    [SmallCategory J] [FinCategory J] {F : J ⥤ X.Modules} {c : Cone F}
    (hc : IsLimit c) (hF : ∀ j, (F.obj j).IsQuasicoherent) :
    c.pt.IsQuasicoherent := by
  let U : X.affineOpens → X.Opens := fun V ↦ V.1
  let hU : IsOpenCover U := iSup_affineOpens_eq_top X
  let hUaff : ∀ i, IsAffineOpen (U i) := fun i ↦ i.2
  letI (i : X.affineOpens) :
      IsIso ((((c.pt.restrict (U i).ι).restrict (hUaff i).isoSpec.inv).fromTildeΓ)) := by
    rw [← AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ]
    let G := restrictFunctor (U i).ι ⋙ restrictFunctor (hUaff i).isoSpec.inv
    letI : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
    letI : PreservesLimit F G := inferInstance
    letI : (SheafOfModules.isQuasicoherent
        (Spec Γ(X, U i)).ringCatSheaf).IsClosedUnderLimitsOfShape J := by
      rw [← AlgebraicGeometry.essImage_tilde]
      exact instIsClosedUnderLimitsOfShapeEssImageOfHasLimitsOfShapeOfPreservesLimitsOfShapeOfFullOfFaithful
        (tilde.functor Γ(X, U i))
    change (SheafOfModules.isQuasicoherent (Spec Γ(X, U i)).ringCatSheaf) (G.obj c.pt)
    apply (SheafOfModules.isQuasicoherent (Spec Γ(X, U i)).ringCatSheaf).prop_of_isLimit
      (isLimitOfPreserves G hc)
    intro j
    letI : (F.obj j).IsQuasicoherent := hF j
    dsimp [G]
    infer_instance
  exact @isQuasicoherent_of_affineOpenCover_isIso_fromTildeΓ
    X c.pt X.affineOpens U hU hUaff inferInstance

set_option backward.isDefEq.respectTransparency.types false in
set_option linter.style.haveILetI false in
/-- A finite colimit of quasicoherent modules on an arbitrary scheme is
quasicoherent. -/
theorem isQuasicoherent_of_isColimit (X : Scheme.{u}) {J : Type w}
    [SmallCategory J] [FinCategory J] {F : J ⥤ X.Modules} {c : Cocone F}
    (hc : IsColimit c) (hF : ∀ j, (F.obj j).IsQuasicoherent) :
    c.pt.IsQuasicoherent := by
  let U : X.affineOpens → X.Opens := fun V ↦ V.1
  let hU : IsOpenCover U := iSup_affineOpens_eq_top X
  let hUaff : ∀ i, IsAffineOpen (U i) := fun i ↦ i.2
  letI (i : X.affineOpens) :
      IsIso ((((c.pt.restrict (U i).ι).restrict (hUaff i).isoSpec.inv).fromTildeΓ)) := by
    rw [← AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ]
    let G := restrictFunctor (U i).ι ⋙ restrictFunctor (hUaff i).isoSpec.inv
    letI : PreservesFiniteColimits G := comp_preservesFiniteColimits _ _
    letI : PreservesColimit F G := inferInstance
    letI : (SheafOfModules.isQuasicoherent
        (Spec Γ(X, U i)).ringCatSheaf).IsClosedUnderColimitsOfShape J := by
      rw [← AlgebraicGeometry.essImage_tilde]
      exact instIsClosedUnderColimitsOfShapeEssImageOfHasColimitsOfShapeOfPreservesColimitsOfShapeOfFullOfFaithful
        (tilde.functor Γ(X, U i))
    change (SheafOfModules.isQuasicoherent (Spec Γ(X, U i)).ringCatSheaf) (G.obj c.pt)
    apply (SheafOfModules.isQuasicoherent (Spec Γ(X, U i)).ringCatSheaf).prop_of_isColimit
      (isColimitOfPreserves G hc)
    intro j
    letI : (F.obj j).IsQuasicoherent := hF j
    dsimp [G]
    infer_instance
  exact @isQuasicoherent_of_affineOpenCover_isIso_fromTildeΓ
    X c.pt X.affineOpens U hU hUaff inferInstance

/-- Quasicoherent modules on an arbitrary scheme are closed under finite
limits. -/
noncomputable instance isQuasicoherent_isClosedUnderFiniteLimits (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape J _ _ := by
    constructor
    rintro M ⟨p⟩
    exact isQuasicoherent_of_isLimit X p.isLimit p.prop_diag_obj

/-- Quasicoherent modules on an arbitrary scheme are closed under finite
colimits. -/
noncomputable instance isQuasicoherent_isClosedUnderFiniteColimits (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderFiniteColimits where
  isClosedUnderColimitsOfShape J _ _ := by
    constructor
    rintro M ⟨p⟩
    exact isQuasicoherent_of_isColimit X p.isColimit p.prop_diag_obj

/-- The quasicoherent-module property on an arbitrary scheme contains a zero
object. -/
noncomputable instance isQuasicoherent_containsZero (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero where
  exists_zero :=
    ⟨0, isZero_zero _,
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isTerminal
        0 (isZero_zero _).isTerminal⟩

/-- Quasicoherent modules on an arbitrary scheme are closed under kernels. -/
noncomputable instance isQuasicoherent_isClosedUnderKernels (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    apply isQuasicoherent_of_isLimit X hk
    rintro (_ | _)
    · exact hX
    · exact hY

/-- Quasicoherent modules on an arbitrary scheme are closed under cokernels. -/
noncomputable instance isQuasicoherent_isClosedUnderCokernels (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    apply isQuasicoherent_of_isColimit X hk
    rintro (_ | _)
    · exact hX
    · exact hY

end Scheme.Modules

end AlgebraicGeometry
