/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.QcqsModuleLocalization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Localization.Algebra

public section

set_option warningAsError true

/-!
# Ideal sheaves as submodules of the structure sheaf

This file packages an `IdealSheafData` as the sectionwise kernel of its canonical
quotient map.  It identifies sections on affine opens with the ideals supplied by
the data and proves that the resulting module is quasicoherent.
-/

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable {X : Scheme.{u}}

namespace IdealSheafData

set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise kernel of a morphism of sheaves of modules. -/
private noncomputable def kernelSubmodule {M N : X.Modules} (f : M ⟶ N) : M.Submodule where
  toSubmodule :=
    { obj := fun U ↦ LinearMap.ker (f.val.app U).hom
      map := by
        intro U V g x hx
        rw [LinearMap.mem_ker] at hx
        change f.val.app V (M.val.map g x) = 0
        have h := ConcreteCategory.congr_hom (f.val.naturality g) x
        change f.val.app V (M.val.map g x) = N.val.map g (f.val.app U x) at h
        rw [h, hx, map_zero] }
  isSheaf := by
    intro U s hs
    rw [LinearMap.mem_ker]
    let P := N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat
    have hP : Presieve.IsSheaf (Opens.grothendieckTopology X) P := by
      rw [← isSheaf_iff_isSheaf_of_type]
      exact GrothendieckTopology.HasSheafCompose.isSheaf _ N.isSheaf
    apply (hP _ hs).isSeparatedFor.ext
    intro V g hg
    change N.val.map g.op (f.val.app U s) = N.val.map g.op 0
    have h := ConcreteCategory.congr_hom (f.val.naturality g.op) s
    change f.val.app (op V) (M.val.map g.op s) =
      N.val.map g.op (f.val.app U s) at h
    rw [map_zero, ← h]
    exact LinearMap.mem_ker.mp hg

set_option backward.isDefEq.respectTransparency false in
/-- An ideal sheaf as a submodule of the structure sheaf. -/
@[expose]
noncomputable def toSubmodule (I : X.IdealSheafData) :
    (SheafOfModules.unit X.ringCatSheaf).Submodule :=
  let kernelSubmoduleLocal {M N : X.Modules} (f : M ⟶ N) : M.Submodule :=
    { toSubmodule :=
        { obj := fun U ↦ LinearMap.ker (f.val.app U).hom
          map := by
            intro U V g x hx
            rw [LinearMap.mem_ker] at hx
            change f.val.app V (M.val.map g x) = 0
            have h := ConcreteCategory.congr_hom (f.val.naturality g) x
            change f.val.app V (M.val.map g x) = N.val.map g (f.val.app U x) at h
            rw [h, hx, map_zero] }
      isSheaf := by
        intro U s hs
        rw [LinearMap.mem_ker]
        let P := N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat
        have hP : Presieve.IsSheaf (Opens.grothendieckTopology X) P := by
          rw [← isSheaf_iff_isSheaf_of_type]
          exact GrothendieckTopology.HasSheafCompose.isSheaf _ N.isSheaf
        apply (hP _ hs).isSeparatedFor.ext
        intro V g hg
        change N.val.map g.op (f.val.app U s) = N.val.map g.op 0
        have h := ConcreteCategory.congr_hom (f.val.naturality g.op) s
        change f.val.app (op V) (M.val.map g.op s) =
          N.val.map g.op (f.val.app U s) at h
        rw [map_zero, ← h]
        exact LinearMap.mem_ker.mp hg }
  kernelSubmoduleLocal
    (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)

private theorem toSubmodule_eq_oldConstruction (I : X.IdealSheafData) :
    I.toSubmodule = kernelSubmodule
      (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom) := by
  rfl

/-- The sheaf of modules underlying an ideal sheaf. -/
@[expose]
noncomputable def toModule (I : X.IdealSheafData) : X.Modules :=
  I.toSubmodule.toSheafOfModules

/-- The canonical inclusion of an ideal sheaf module into the structure sheaf. -/
@[expose]
noncomputable def toModuleι (I : X.IdealSheafData) :
    I.toModule ⟶ SheafOfModules.unit X.ringCatSheaf :=
  I.toSubmodule.ι

/-- The canonical inclusion of an ideal sheaf module is a monomorphism. -/
noncomputable instance toModuleι_mono (I : X.IdealSheafData) : Mono I.toModuleι := by
  constructor
  intro Z g h e
  apply SheafOfModules.hom_ext
  ext U x
  apply Subtype.ext
  have h := congr_arg (fun k ↦ k.val.app U x) e
  exact h

/-- An ideal sheaf as a subobject of the structure sheaf. -/
@[expose]
noncomputable def toModuleSubobject (I : X.IdealSheafData) :
    @Subobject X.Modules (inferInstance : Category X.Modules)
      (SheafOfModules.unit X.ringCatSheaf) := by
  letI : Mono I.toModuleι := toModuleι_mono I
  exact Subobject.mk I.toModuleι

set_option backward.isDefEq.respectTransparency false in
/-- On an affine open, sections of the ideal sheaf module are the specified ideal. -/
@[expose]
noncomputable def affineSectionsEquiv (I : X.IdealSheafData) (U : X.affineOpens) :
    Γ(I.toModule, U.1) ≃ₗ[Γ(X, U.1)] I.ideal U where
  toFun s := ⟨s.1, by
    rw [← I.ker_subschemeι_app U]
    exact s.2⟩
  invFun s := ⟨s.1, by
    change (SheafOfModules.unitToPushforwardObjUnit
      I.subschemeι.toRingCatSheafHom).val.app (op U.1) s.1 = 0
    change I.subschemeι.app U s.1 = 0
    rw [← RingHom.mem_ker, I.ker_subschemeι_app U]
    exact s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The affine-sections equivalence is literally compatible with inclusion into
the structure sheaf. -/
@[simp]
theorem affineSectionsEquiv_apply (I : X.IdealSheafData) (U : X.affineOpens)
    (s : Γ(I.toModule, U.1)) :
    ((I.affineSectionsEquiv U s : I.ideal U) : Γ(X, U.1)) = I.toModuleι.app U.1 s :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of an ideal sheaf module from an affine open to a basic open is
localization away from the section defining the basic open. -/
theorem toModule_isLocalizedModule_basicOpen (I : X.IdealSheafData)
    (U : X.affineOpens) (f : Γ(X, U.1)) :
    letI : Module Γ(X, U.1) Γ(I.toModule, X.basicOpen f) :=
      Module.compHom _ (algebraMap _ _)
    IsLocalizedModule.Away f (Scheme.Modules.basicOpenRestriction I.toModule f) := by
  let _ : Module Γ(X, U.1) Γ(I.toModule, X.basicOpen f) :=
    Module.compHom Γ(I.toModule, X.basicOpen f)
      (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f))
  let e₀ := I.affineSectionsEquiv U
  let e₁S : Γ(I.toModule, X.basicOpen f) ≃ₗ[Γ(X, X.basicOpen f)]
      (I.ideal U).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) := {
    toFun s := ⟨s.1, by
      have hAlg : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
          algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) := rfl
      rw [← hAlg, I.map_ideal_basicOpen U f]
      exact (I.affineSectionsEquiv (X.affineBasicOpen f) s).2⟩
    invFun s := ⟨s.1, by
      change (SheafOfModules.unitToPushforwardObjUnit
        I.subschemeι.toRingCatSheafHom).val.app (op (X.basicOpen f)) s.1 = 0
      change I.subschemeι.app (X.affineBasicOpen f) s.1 = 0
      have hAlg : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
          algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) := rfl
      rw [← RingHom.mem_ker, I.ker_subschemeι_app,
        ← I.map_ideal_basicOpen U f, hAlg]
      exact s.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let e₁ : Γ(I.toModule, X.basicOpen f) ≃ₗ[Γ(X, U.1)]
      (I.ideal U).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) :=
    { e₁S.toEquiv with
      map_add' := e₁S.map_add
      map_smul' := by
        intro r s
        change e₁S ((algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) r) • s) = _
        rw [e₁S.map_smul]
        rfl }
  let φ := Algebra.idealMap Γ(X, X.basicOpen f) (I.ideal U)
  let _ : IsLocalization.Away f Γ(X, X.basicOpen f) :=
    U.2.isLocalization_basicOpen f
  have hφ : IsLocalizedModule.Away f φ := inferInstance
  let ψ := e₁.symm.toLinearMap.comp (φ.comp e₀.toLinearMap)
  have hψ : IsLocalizedModule.Away f ψ := by
    let _ : IsLocalizedModule.Away f φ := hφ
    let _ : IsLocalizedModule.Away f (φ.comp e₀.toLinearMap) :=
      IsLocalizedModule.of_linearEquiv_right _ φ e₀
    exact IsLocalizedModule.of_linearEquiv _ (φ.comp e₀.toLinearMap) e₁.symm
  rw [show ψ = Scheme.Modules.basicOpenRestriction I.toModule f by
    ext s
    apply Subtype.ext
    dsimp only [ψ, e₁, e₁S, φ, e₀, LinearMap.comp_apply,
      LinearEquiv.coe_coe, Function.comp_apply]
    dsimp [affineSectionsEquiv]
    rw [Algebra.idealMap_apply_coe]
    have hAlg : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
        algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) := rfl
    rw [← hAlg]
    dsimp only [Scheme.Modules.basicOpenRestriction, toModuleι]
    change X.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (I.toModuleι.app U.1 s) =
      I.toModuleι.app (X.basicOpen f)
        (I.toModule.presheaf.map (homOfLE (X.basicOpen_le f)).op s)
    have h := ConcreteCategory.congr_hom
      (I.toModuleι.val.naturality (homOfLE (X.basicOpen_le f)).op) s
    exact h.symm] at hψ
  exact hψ

set_option backward.isDefEq.respectTransparency false in
/-- Sections on the top open after transporting an affine chart to its spectrum. -/
private noncomputable def affineTopSectionsLinearEquiv (M : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(M.restrict hU.fromSpec, ⊤) ≃ₗ[Γ(X, U)] Γ(M, U) := by
  let htop : U = hU.fromSpec ''ᵁ ⊤ := by simp [hU.opensRange_fromSpec]
  let l : Γ(M.restrict hU.fromSpec, ⊤) →ₗ[Γ(X, U)] Γ(M, U) :=
    { toFun := fun x ↦ M.presheaf.map (eqToHom htop).op
          ((M.restrictAppIso hU.fromSpec ⊤).hom x)
      map_add' := map_add _
      map_smul' := by
        intro r x
        let r' : Γ(Spec Γ(X, U), ⊤) :=
          (Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
            ((Scheme.ΓSpecIso Γ(X, U)).inv r)
        rw [show r • x = r' • x from Scheme.Modules.smul_Spec_def r x]
        rw [show (M.restrictAppIso hU.fromSpec ⊤).hom (r' • x) =
          (hU.fromSpec.appIso ⊤).inv r' •
            (M.restrictAppIso hU.fromSpec ⊤).hom x from
          Scheme.Modules.smul_restrictAppIso_hom_apply hU.fromSpec M ⊤ r' x]
        rw [M.map_smul]
        congr 1
        dsimp [r']
        let _ : IsIso (hU.fromSpec.app U) :=
          hU.fromSpec.isIso_app U (by rw [hU.opensRange_fromSpec])
        apply (ConcreteCategory.bijective_of_isIso (hU.fromSpec.app U)).1
        rw [← ConcreteCategory.comp_apply, hU.fromSpec.naturality]
        rw [ConcreteCategory.comp_apply]
        rw [Scheme.Hom.appIso_inv_app_apply]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rw [hU.fromSpec_app_self_apply]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl }
  apply LinearEquiv.ofBijective l
  exact (ConcreteCategory.bijective_of_isIso
    (M.presheaf.mapIso (eqToIso htop).op).hom).comp
      (ConcreteCategory.bijective_of_isIso (M.restrictAppIso hU.fromSpec ⊤).hom)

set_option backward.isDefEq.respectTransparency false in
/-- Sections on a basic open after transporting an affine chart to its spectrum. -/
private noncomputable def affineBasicOpenSectionsLinearEquiv (M : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) :
    letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
      Module.compHom Γ(M, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
    Γ(M.restrict hU.fromSpec, PrimeSpectrum.basicOpen f) ≃ₗ[Γ(X, U)]
      Γ(M, X.basicOpen f) := by
  letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom Γ(M, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
  let V : (Spec Γ(X, U)).Opens := PrimeSpectrum.basicOpen f
  let hbasic : X.basicOpen f = hU.fromSpec ''ᵁ V :=
    hU.fromSpec_image_basicOpen f |>.symm
  let l : Γ(M.restrict hU.fromSpec, PrimeSpectrum.basicOpen f) →ₗ[Γ(X, U)]
      Γ(M, X.basicOpen f) :=
    { toFun := fun x ↦ M.presheaf.map (eqToHom hbasic).op
          ((M.restrictAppIso hU.fromSpec V).hom x)
      map_add' := map_add _
      map_smul' := by
        intro r x
        let r' : Γ(Spec Γ(X, U), V) :=
          (Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
            ((Scheme.ΓSpecIso Γ(X, U)).inv r)
        rw [show r • x = r' • x from Scheme.Modules.smul_Spec_def r x]
        rw [show (M.restrictAppIso hU.fromSpec V).hom (r' • x) =
          (hU.fromSpec.appIso V).inv r' •
            (M.restrictAppIso hU.fromSpec V).hom x from
          Scheme.Modules.smul_restrictAppIso_hom_apply hU.fromSpec M V r' x]
        rw [M.map_smul]
        congr 1
        dsimp [r']
        let _ : IsIso (hU.fromSpec.app (X.basicOpen f)) :=
          hU.fromSpec.isIso_app _ (by
            rw [hU.opensRange_fromSpec]
            exact X.basicOpen_le f)
        apply (ConcreteCategory.bijective_of_isIso
          (hU.fromSpec.app (X.basicOpen f))).1
        rw [← ConcreteCategory.comp_apply, hU.fromSpec.naturality]
        rw [ConcreteCategory.comp_apply, Scheme.Hom.appIso_inv_app_apply]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        change _ = hU.fromSpec.app (X.basicOpen f)
          (X.presheaf.map (homOfLE (X.basicOpen_le f)).op r)
        conv_rhs => rw [← ConcreteCategory.comp_apply]
        rw [hU.fromSpec.naturality]
        rw [ConcreteCategory.comp_apply, hU.fromSpec_app_self_apply]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl }
  apply LinearEquiv.ofBijective l
  exact (ConcreteCategory.bijective_of_isIso
    (M.presheaf.mapIso (eqToIso hbasic).op).hom).comp
      (ConcreteCategory.bijective_of_isIso (M.restrictAppIso hU.fromSpec V).hom)

set_option maxHeartbeats 800000 in
-- The affine-cover quasicoherence proof involves expensive sheaf computations.
set_option backward.isDefEq.respectTransparency false in
/-- The module associated to any ideal sheaf data is quasicoherent. -/
theorem toModule_isQuasicoherent (I : X.IdealSheafData) :
    I.toModule.IsQuasicoherent := by
  let U : X.affineOpens → X.Opens := fun V ↦ V.1
  let hU : IsOpenCover U := iSup_affineOpens_eq_top X
  let hUaff : ∀ i, IsAffineOpen (U i) := fun i ↦ i.2
  refine @Scheme.Modules.isQuasicoherent_of_affineOpenCover_isIso_fromTildeΓ
    X I.toModule X.affineOpens U hU hUaff ?_
  intro i
  let N := I.toModule.restrict (hUaff i).fromSpec
  have hNfrom : IsIso N.fromTildeΓ := by
    rw [AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing]
    intro f
    let _ : Module Γ(X, U i) Γ(I.toModule, X.basicOpen f) :=
      Module.compHom Γ(I.toModule, X.basicOpen f)
        (algebraMap Γ(X, U i) Γ(X, X.basicOpen f))
    let V : (Spec Γ(X, U i)).Opens := PrimeSpectrum.basicOpen f
    let φ : Γ(N, ⊤) →ₗ[Γ(X, U i)] Γ(N, V) :=
      ((AlgebraicGeometry.modulesSpecToSheaf.obj N).obj.map (homOfLE le_top).op).hom
    let e₀ := affineTopSectionsLinearEquiv I.toModule (hUaff i)
    let e₁ := affineBasicOpenSectionsLinearEquiv I.toModule (hUaff i) f
    have hcomm (y : Γ(N, ⊤)) :
        e₁ (φ y) = Scheme.Modules.basicOpenRestriction I.toModule f (e₀ y) := by
      dsimp [φ, e₀, e₁, affineTopSectionsLinearEquiv,
        affineBasicOpenSectionsLinearEquiv]
      change I.toModule.presheaf.map _
        ((I.toModule.restrictAppIso (hUaff i).fromSpec V).hom
          (N.presheaf.map (homOfLE le_top).op y)) = _
      rw [Scheme.Modules.map_restrictAppIso_hom_apply]
      dsimp [Scheme.Modules.basicOpenRestriction]
      simp only [← ConcreteCategory.comp_apply, Category.assoc]
      congr 1
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
    let ψ := e₁.symm.toLinearMap.comp
      ((Scheme.Modules.basicOpenRestriction I.toModule f).comp e₀.toLinearMap)
    have hψ : IsLocalizedModule.Away f ψ := by
      let hres : IsLocalizedModule.Away f
          (Scheme.Modules.basicOpenRestriction I.toModule f) :=
        I.toModule_isLocalizedModule_basicOpen i f
      let _ : IsLocalizedModule.Away f
          (Scheme.Modules.basicOpenRestriction I.toModule f) := hres
      let _ : IsLocalizedModule.Away f
          ((Scheme.Modules.basicOpenRestriction I.toModule f).comp e₀.toLinearMap) :=
        IsLocalizedModule.of_linearEquiv_right _
          (Scheme.Modules.basicOpenRestriction I.toModule f) e₀
      exact IsLocalizedModule.of_linearEquiv _
        ((Scheme.Modules.basicOpenRestriction I.toModule f).comp e₀.toLinearMap) e₁.symm
    rw [show ψ = φ by
      ext y
      apply e₁.injective
      simpa [ψ] using (hcomm y).symm] at hψ
    exact hψ
  have hNqc : N.IsQuasicoherent :=
    (AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ N).mpr hNfrom
  let α := (Scheme.Modules.restrictFunctorComp (hUaff i).isoSpec.inv (U i).ι).app I.toModule
  have hDouble :
      ((I.toModule.restrict (U i).ι).restrict (hUaff i).isoSpec.inv).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, U i)).ringCatSheaf).prop_of_iso α hNqc
  exact (AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ _).mp hDouble

end IdealSheafData

/-- The nilradical ideal sheaf as a module over the structure sheaf. -/
@[expose]
noncomputable def nilradicalModule (X : Scheme.{u}) : X.Modules :=
  X.nilradical.toModule

/-- The inclusion of the nilradical module into the structure sheaf. -/
noncomputable def nilradicalModuleι (X : Scheme.{u}) :
    X.nilradicalModule ⟶ SheafOfModules.unit X.ringCatSheaf :=
  X.nilradical.toModuleι

/-- The nilradical ideal sheaf as a subobject of the structure sheaf. -/
noncomputable def nilradicalModuleSubobject (X : Scheme.{u}) :
    @Subobject X.Modules (inferInstance : Category X.Modules)
      (SheafOfModules.unit X.ringCatSheaf) :=
  X.nilradical.toModuleSubobject

/-- The nilradical module is quasicoherent. -/
theorem nilradicalModule_isQuasicoherent (X : Scheme.{u}) :
    X.nilradicalModule.IsQuasicoherent :=
  X.nilradical.toModule_isQuasicoherent

/-- Sections of the nilradical module on an affine open are the nilradical of
the ring of functions on that open. -/
noncomputable def nilradicalModuleAffineSections (X : Scheme.{u})
    (U : X.affineOpens) :
    Γ(X.nilradicalModule, U.1) ≃ₗ[Γ(X, U.1)] _root_.nilradical (Γ(X, U.1)) :=
  X.nilradical.affineSectionsEquiv U

end AlgebraicGeometry.Scheme

#lint- only unusedArguments docBlame
