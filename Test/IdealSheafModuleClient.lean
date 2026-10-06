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

example : (SheafOfModules.unit X.ringCatSheaf).Submodule := I.toSubmodule

example : X.Modules := I.toModule

example : I.toModule ⟶ SheafOfModules.unit X.ringCatSheaf := I.toModuleι

example : Mono I.toModuleι := inferInstance

example : @Subobject X.Modules (inferInstance : Category X.Modules)
    (SheafOfModules.unit X.ringCatSheaf) := I.toModuleSubobject

example (U : X.affineOpens) :
    Γ(I.toModule, U.1) ≃ₗ[Γ(X, U.1)] I.ideal U :=
  I.affineSectionsEquiv U

example (U : X.affineOpens) (s : Γ(I.toModule, U.1)) :
    ((I.affineSectionsEquiv U s : I.ideal U) : Γ(X, U.1)) = I.toModuleι.app U.1 s := by
  exact I.affineSectionsEquiv_apply U s

example (U : X.affineOpens) (f : Γ(X, U.1)) :
    letI : Module Γ(X, U.1) Γ(I.toModule, X.basicOpen f) :=
      Module.compHom _ (algebraMap _ _)
    IsLocalizedModule.Away f (Scheme.Modules.basicOpenRestriction I.toModule f) :=
  I.toModule_isLocalizedModule_basicOpen U f

example : I.toModule.IsQuasicoherent := I.toModule_isQuasicoherent

example : X.Modules := X.nilradicalModule

example : X.nilradicalModule ⟶ SheafOfModules.unit X.ringCatSheaf :=
  X.nilradicalModuleι

example : @Subobject X.Modules (inferInstance : Category X.Modules)
    (SheafOfModules.unit X.ringCatSheaf) := X.nilradicalModuleSubobject

example : X.nilradicalModule.IsQuasicoherent :=
  X.nilradicalModule_isQuasicoherent

example (U : X.affineOpens) :
    Γ(X.nilradicalModule, U.1) ≃ₗ[Γ(X, U.1)]
      _root_.nilradical (Γ(X, U.1)) :=
  X.nilradicalModuleAffineSections U

/- A zero-ring affine scheme; its underlying space is empty. -/
example : (Spec (.of (ZMod 1)) : Scheme).nilradicalModule.IsQuasicoherent :=
  (Spec (.of (ZMod 1)) : Scheme).nilradicalModule_isQuasicoherent

example [IsEmpty X] : X.nilradicalModule.IsQuasicoherent :=
  X.nilradicalModule_isQuasicoherent

/- The empty open is affine, so the affine-sections API applies literally. -/
example :
    Γ(I.toModule, (⊥ : X.Opens)) ≃ₗ[Γ(X, (⊥ : X.Opens))]
      I.ideal ⟨⊥, isAffineOpen_bot X⟩ :=
  I.affineSectionsEquiv ⟨⊥, isAffineOpen_bot X⟩

example [IsReduced X] :
    X.nilradicalModule = (⊥ : X.IdealSheafData).toModule := by
  rw [Scheme.nilradicalModule, Scheme.nilradical_eq_bot]

end

end IdealSheafModuleClient
