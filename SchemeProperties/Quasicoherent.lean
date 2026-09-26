/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

public section

set_option warningAsError true

/-!
# Quasicoherent modules on affine open covers

This file connects the scheme-facing restriction API with the over-site API in
the definition of quasicoherence. It proves that quasicoherence can be checked
by the affine `fromTildeΓ` maps on any fixed affine open cover.
-/

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- A quasicoherent module, restricted to an affine open and transported to
the literal spectrum of the ring of sections on that open, is recovered from
its global sections by the affine `fromTildeΓ` map. -/
theorem isIso_fromTildeΓ_restrict_affineOpen
    (X : Scheme.{u}) (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso (((M.restrict U.ι).restrict hU.isoSpec.inv).fromTildeΓ) := by
  rw [← AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ]
  infer_instance

/-- An affine module recovered from its global sections has a global
presentation. -/
noncomputable def presentationOfIsIsoFromTildeΓ
    {R : CommRingCat.{u}} (N : (Spec R).Modules)
    [hN : IsIso N.fromTildeΓ] : N.Presentation := by
  let V : ModuleCat R :=
    (modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤)
  let P : (tilde V).Presentation :=
    presentationTilde V .univ (by simp) _ (Submodule.span_eq _)
  exact @SheafOfModules.Presentation.ofIsIso
    _ _ _ _ _ _ _ _ N.fromTildeΓ hN P

/-- The affine `fromTildeΓ` condition gives a presentation of the original
restriction to the affine open, before transport to the over-site. -/
noncomputable def presentationRestrictAffineOpenOfIsIsoFromTildeΓ
    (X : Scheme.{u}) (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)
    [hFrom : IsIso (((M.restrict U.ι).restrict hU.isoSpec.inv).fromTildeΓ)] :
    (M.restrict U.ι).Presentation := by
  let Mᵤ := M.restrict U.ι
  let N := Mᵤ.restrict hU.isoSpec.inv
  let hN : IsIso N.fromTildeΓ := by
    simpa [N, Mᵤ] using hFrom
  let P := presentationRestrict hU.isoSpec.hom
    (@presentationOfIsIsoFromTildeΓ _ N hN)
  let α :=
    ((restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).app Mᵤ).symm ≪≫
      (restrictFunctorCongr hU.isoSpec.hom_inv_id).app Mᵤ ≪≫
      restrictFunctorId.app Mᵤ
  exact @SheafOfModules.Presentation.ofIsIso
    _ _ _ _ _ _ _ _ α.hom α.isIso_hom P

/-- A presentation of the scheme-theoretic restriction to an open gives a
presentation on the corresponding over-site. -/
noncomputable def presentationOverOfPresentationRestrict
    (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) : (M.over U).Presentation := by
  let hPres : Limits.PreservesColimitsOfSize.{u, u}
      (overEquiv U).inverse :=
    (overEquiv U).toAdjunction'.leftAdjoint_preservesColimits
  let P' := @SheafOfModules.Presentation.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ P (overEquiv U).inverse hPres
      (TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit
        U X.ringCatSheaf).symm
  let e := overEquiv U
  let α : e.functor.obj (M.over U) ≅ M.restrict U.ι :=
    (overFunctorEquiv U).app M
  let β : M.over U ≅ e.inverse.obj (M.restrict U.ι) :=
    e.unitIso.app (M.over U) ≪≫ e.inverse.mapIso α
  exact P'.ofIsIso β.symm.hom

/-- Quasicoherence glues from presentations on an open cover, expressed in
the scheme-facing restriction API. -/
theorem isQuasicoherent_of_isOpenCover_presentation
    (X : Scheme.{u}) (M : X.Modules) {I : Type u}
    (U : I → X.Opens) (hU : IsOpenCover U)
    (P : ∀ i, (M.restrict (U i).ι).Presentation) :
    M.IsQuasicoherent := by
  let hqc (i : I) : (M.over (U i)).IsQuasicoherent :=
    (presentationOverOfPresentationRestrict X M (U i) (P i)).isQuasicoherent
  have hUTop : (Opens.grothendieckTopology X).CoversTop U := by
    rwa [Opens.coversTop_iff]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ M I U hUTop hqc

/-- It suffices to verify the affine `fromTildeΓ` condition on one affine
open cover. -/
theorem isQuasicoherent_of_affineOpenCover_isIso_fromTildeΓ
    (X : Scheme.{u}) (M : X.Modules) {I : Type u}
    (U : I → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    [hFrom : ∀ i,
      IsIso (((M.restrict (U i).ι).restrict (hUaff i).isoSpec.inv).fromTildeΓ)] :
    M.IsQuasicoherent := by
  apply isQuasicoherent_of_isOpenCover_presentation X M U hU
  intro i
  exact @presentationRestrictAffineOpenOfIsIsoFromTildeΓ
    X M (U i) (hUaff i) (hFrom i)

/-- On a fixed affine open cover, quasicoherence is equivalent to the affine
`fromTildeΓ` condition on every member of the cover. -/
theorem isQuasicoherent_iff_affineOpenCover_isIso_fromTildeΓ
    (X : Scheme.{u}) (M : X.Modules) {I : Type u}
    (U : I → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    M.IsQuasicoherent ↔
      ∀ i, IsIso
        (((M.restrict (U i).ι).restrict (hUaff i).isoSpec.inv).fromTildeΓ) := by
  constructor
  · intro hM i
    exact @isIso_fromTildeΓ_restrict_affineOpen X M hM (U i) (hUaff i)
  · intro hFrom
    exact @isQuasicoherent_of_affineOpenCover_isIso_fromTildeΓ
      X M I U hU hUaff hFrom

end AlgebraicGeometry.Scheme.Modules
