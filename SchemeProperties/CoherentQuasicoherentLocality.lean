/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.CoherentQuasicoherent

public section

set_option warningAsError true

/-!
# Locality of coherent quasicoherent modules

This file defines coherent quasicoherent modules on a scheme using the native
quasicoherent-module category.  It proves that the property can be checked on
any fixed affine open cover.

The reverse implication uses Mathlib's affine communication lemma together
with the Coherent Modules localization criteria for coherence on basic opens.
In particular, the cover need not be finite and no global compactness,
quasiseparatedness, or nonemptiness assumption is imposed.

## References

- Coherent Modules' `CoherentModules/Basic.lean`,
  `CoherentModules/ModuleCat.lean` and `CoherentModules/Localization.lean`
  supply the coherent-module predicate, affine object property and localization
  criteria used through `SchemeProperties.CoherentQuasicoherent`.
- Mathlib's `Mathlib/AlgebraicGeometry/AffineScheme.lean` supplies the affine
  communication lemma `of_affine_open_cover`.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- On an affine open, the native affine coherent property is equivalent to
coherence of the module of sections on that open. -/
lemma isCoherentOnSpec_restrict_affineOpen_iff
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (V : X.Opens) (hV : IsAffineOpen V) :
    isCoherentOnSpec Γ(X, V)
      (⟨(M.restrict V.ι).restrict hV.isoSpec.inv,
        by infer_instance⟩ :
        (SheafOfModules.isQuasicoherent
          (Spec Γ(X, V)).ringCatSheaf).FullSubcategory) ↔
      Module.IsCoherent Γ(X, V) Γ(M, V) := by
  rw [isCoherentOnSpec_iff]
  exact Module.IsCoherent.equiv_iff (affineOpenSectionsLinearEquiv M V hV)

/-- The object property of being a coherent quasicoherent module on a scheme.

The definition uses the existing native category of quasicoherent modules and
requires the corresponding affine module to be coherent on every affine open.
-/
def isCoherentQuasicoherent (X : Scheme.{u}) :
    ObjectProperty
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  fun Q ↦
    let M : X.Modules := Q.obj
    let _ : M.IsQuasicoherent := Q.property
    ∀ V : X.affineOpens,
      isCoherentOnSpec Γ(X, (V : X.Opens))
        (⟨(M.restrict V.1.ι).restrict V.2.isoSpec.inv,
          by infer_instance⟩ :
          (SheafOfModules.isQuasicoherent
            (Spec Γ(X, (V : X.Opens))).ringCatSheaf).FullSubcategory)

/-- Coherence of a quasicoherent module can be checked on any fixed affine open
cover. -/
theorem isCoherentQuasicoherent_iff_affineOpenCover
    (X : Scheme.{u})
    (Q : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    {I : Type u} (U : I → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    let M : X.Modules := Q.obj
    let _ : M.IsQuasicoherent := Q.property
    isCoherentQuasicoherent X Q ↔
      ∀ i, isCoherentOnSpec Γ(X, U i)
        (⟨(M.restrict (U i).ι).restrict (hUaff i).isoSpec.inv,
          by infer_instance⟩ :
          (SheafOfModules.isQuasicoherent
            (Spec Γ(X, U i)).ringCatSheaf).FullSubcategory) := by
  let M : X.Modules := Q.obj
  let _ : M.IsQuasicoherent := Q.property
  change (∀ V : X.affineOpens,
      isCoherentOnSpec Γ(X, (V : X.Opens))
        (⟨(M.restrict V.1.ι).restrict V.2.isoSpec.inv,
          by infer_instance⟩ :
          (SheafOfModules.isQuasicoherent
            (Spec Γ(X, (V : X.Opens))).ringCatSheaf).FullSubcategory)) ↔
    ∀ i, isCoherentOnSpec Γ(X, U i)
      (⟨(M.restrict (U i).ι).restrict (hUaff i).isoSpec.inv,
        by infer_instance⟩ :
        (SheafOfModules.isQuasicoherent
          (Spec Γ(X, U i)).ringCatSheaf).FullSubcategory)
  constructor
  · intro h i
    exact h ⟨U i, hUaff i⟩
  · intro h V
    rw [isCoherentOnSpec_restrict_affineOpen_iff M V.1 V.2]
    apply of_affine_open_cover
      (P := fun W ↦ Module.IsCoherent Γ(X, (W : X.Opens)) Γ(M, (W : X.Opens)))
      (fun i ↦ ⟨U i, hUaff i⟩) hU.iSup_eq_top V
    · intro W f hW
      exact isCoherent_basicOpen_of_qcqs M W.2.isCompact
        W.2.isQuasiSeparated f hW
    · intro W s hs hWs
      exact isCoherent_of_span_basicOpen_of_qcqs M W.2.isCompact
        W.2.isQuasiSeparated (s : Set Γ(X, (W : X.Opens))) hs hWs
    · intro i
      exact (isCoherentOnSpec_restrict_affineOpen_iff
        M (U i) (hUaff i)).mp (h i)

end AlgebraicGeometry.Scheme.Modules
