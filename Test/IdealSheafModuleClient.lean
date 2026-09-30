/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.IdealSheafModule

set_option warningAsError true

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace IdealSheafModuleClient

open AlgebraicGeometry

noncomputable section

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData)

private def check_1 : (SheafOfModules.unit X.ringCatSheaf).Submodule := I.toSubmodule

private def check_2 : X.Modules := I.toModule

private def check_3 : I.toModule ⟶ SheafOfModules.unit X.ringCatSheaf := I.toModuleι

private theorem check_4 : Mono I.toModuleι := inferInstance

private def check_5 : @Subobject X.Modules (inferInstance : Category X.Modules)
    (SheafOfModules.unit X.ringCatSheaf) := I.toModuleSubobject

private def check_6 (U : X.affineOpens) :
    Γ(I.toModule, U.1) ≃ₗ[Γ(X, U.1)] I.ideal U :=
  I.affineSectionsEquiv U

private theorem check_7 (U : X.affineOpens) (s : Γ(I.toModule, U.1)) :
    ((I.affineSectionsEquiv U s : I.ideal U) : Γ(X, U.1)) = I.toModuleι.app U.1 s := by
  exact I.affineSectionsEquiv_apply U s

private theorem check_8 (U : X.affineOpens) (f : Γ(X, U.1)) :
    letI : Module Γ(X, U.1) Γ(I.toModule, X.basicOpen f) :=
      Module.compHom _ (algebraMap _ _)
    IsLocalizedModule.Away f (Scheme.Modules.basicOpenRestriction I.toModule f) :=
  I.toModule_isLocalizedModule_basicOpen U f

private theorem check_9 : I.toModule.IsQuasicoherent := I.toModule_isQuasicoherent

private def check_10 : X.Modules := X.nilradicalModule

private def check_11 : X.nilradicalModule ⟶ SheafOfModules.unit X.ringCatSheaf :=
  X.nilradicalModuleι

private def check_12 : @Subobject X.Modules (inferInstance : Category X.Modules)
    (SheafOfModules.unit X.ringCatSheaf) := X.nilradicalModuleSubobject

private theorem check_13 : X.nilradicalModule.IsQuasicoherent :=
  X.nilradicalModule_isQuasicoherent

private def check_14 (U : X.affineOpens) :
    Γ(X.nilradicalModule, U.1) ≃ₗ[Γ(X, U.1)]
      _root_.nilradical (Γ(X, U.1)) :=
  X.nilradicalModuleAffineSections U

/- A zero-ring affine scheme; its underlying space is empty. -/
abbrev X₀ : Scheme := Spec (.of (ZMod 1))

private theorem check_15 : X₀.nilradicalModule.IsQuasicoherent :=
  X₀.nilradicalModule_isQuasicoherent

private theorem check_16 [IsEmpty X] : X.nilradicalModule.IsQuasicoherent :=
  X.nilradicalModule_isQuasicoherent

/- The empty open is affine, so the affine-sections API applies literally. -/
private def check_17 :
    Γ(I.toModule, (⊥ : X.Opens)) ≃ₗ[Γ(X, (⊥ : X.Opens))]
      I.ideal ⟨⊥, isAffineOpen_bot X⟩ :=
  I.affineSectionsEquiv ⟨⊥, isAffineOpen_bot X⟩

private theorem check_18 [IsReduced X] :
    X.nilradicalModule = (⊥ : X.IdealSheafData).toModule := by
  rw [Scheme.nilradicalModule, Scheme.nilradical_eq_bot]

end

end IdealSheafModuleClient
