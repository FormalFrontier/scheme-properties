/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Quasicoherent

public section

set_option warningAsError true

/-!
# Quasicoherence of the structure sheaf

The structure sheaf, regarded as a sheaf of modules over itself, is
quasicoherent on every scheme.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The structure sheaf of any scheme is quasicoherent as a module over
itself. -/
theorem unit_isQuasicoherent (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := by
  let U : X.affineCover.I₀ → X.Opens := fun i ↦ (X.affineCover.f i).opensRange
  let hU : IsOpenCover U := X.affineCover.isOpenCover_opensRange
  let hUaff : ∀ i, IsAffineOpen (U i) := fun i ↦ isAffineOpen_opensRange _
  refine @isQuasicoherent_of_affineOpenCover_isIso_fromTildeΓ X _ _ U hU hUaff ?_
  intro i
  rw [← AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ]
  let e :=
    ((restrictFunctor (hUaff i).isoSpec.inv).mapIso
      (restrictUnitIso (U i).ι)) ≪≫
        restrictUnitIso (hUaff i).isoSpec.inv
  have hUnit :
      (SheafOfModules.unit (Spec Γ(X, U i)).ringCatSheaf).IsQuasicoherent :=
    (AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ _).mpr (by
      infer_instance)
  exact (SheafOfModules.isQuasicoherent
    (Spec Γ(X, U i)).ringCatSheaf).prop_of_iso e.symm hUnit

end AlgebraicGeometry.Scheme.Modules
