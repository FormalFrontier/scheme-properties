/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Localization
public import CoherentModules.ModuleCat
public import SchemeProperties.QcqsModuleLocalization

public section

set_option warningAsError true

/-!
# Coherent section modules of quasicoherent modules

This file connects coherent modules with the native quasicoherent-module API.
On a compact quasiseparated open, coherence of a quasicoherent module's section
module is preserved by restriction to a basic open.  Conversely, coherence can
be checked on any set-indexed family of basic opens whose defining sections
span the unit ideal.

The section module on a basic open is regarded both as a module over its own
structure ring and, by restriction of scalars, as a module over the ambient
section ring.  No finiteness or nonemptiness condition is imposed on the
spanning set.

## References

- `coherent-modules`, `CoherentModules/Localization.lean`:
  `Module.IsCoherent.of_isLocalizedModule` and
  `Module.IsCoherent.of_localizationSpan'` are applied to the project-local
  qcqs section-localization comparisons; the upstream theorems are used
  rather than their proofs being reproduced.
- `coherent-modules`, `CoherentModules/ModuleCat.lean`:
  `ModuleCat.isCoherent` supplies the object property transported to native
  quasicoherent modules on an affine spectrum.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

/-- Coherence of quasicoherent sections is preserved by restriction to a basic
open of a compact quasiseparated open, using `coherent-modules`'s
`Module.IsCoherent.of_isLocalizedModule` after the qcqs localization comparison. -/
theorem isCoherent_basicOpen_of_qcqs
    (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsCompact U.1)
    (hU' : IsQuasiSeparated U.1) (f : Γ(X, U))
    (hM : Module.IsCoherent Γ(X, U) Γ(M, U)) :
    Module.IsCoherent Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) := by
  let _ : Module.IsCoherent Γ(X, U) Γ(M, U) := hM
  let _ : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom Γ(M, X.basicOpen f)
      (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
  let _ : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
    IsScalarTower.of_compHom (A := Γ(X, X.basicOpen f))
      Γ(X, U) Γ(M, X.basicOpen f)
  let _ : IsLocalization.Away f Γ(X, X.basicOpen f) :=
    AlgebraicGeometry.isLocalization_basicOpen_of_qcqs hU hU' f
  let _ : IsLocalizedModule.Away f (basicOpenRestriction M f) :=
    isLocalizedModule_basicOpen_of_qcqs M hU hU' f
  exact Module.IsCoherent.of_isLocalizedModule (Submonoid.powers f)
    (basicOpenRestriction M f)

/-- The global-sections specialization of `isCoherent_basicOpen_of_qcqs`. -/
theorem isCoherent_basicOpen_of_qcqs_of_top
    (M : X.Modules) [M.IsQuasicoherent] [CompactSpace X] [QuasiSeparatedSpace X]
    (f : Γ(X, ⊤)) (hM : Module.IsCoherent Γ(X, ⊤) Γ(M, ⊤)) :
    Module.IsCoherent Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
  isCoherent_basicOpen_of_qcqs M CompactSpace.isCompact_univ
    isQuasiSeparated_univ f hM

/-- Coherence of the section module on a compact quasiseparated open descends
from any set-indexed spanning family of its basic opens, using
`coherent-modules`'s `Module.IsCoherent.of_localizationSpan'`. -/
theorem isCoherent_of_span_basicOpen_of_qcqs
    (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsCompact U.1)
    (hU' : IsQuasiSeparated U.1) (s : Set Γ(X, U)) (hs : Ideal.span s = ⊤)
    (h : ∀ g : s,
      Module.IsCoherent Γ(X, X.basicOpen g.1) Γ(M, X.basicOpen g.1)) :
    Module.IsCoherent Γ(X, U) Γ(M, U) := by
  let _ (g : s) : Module Γ(X, U) Γ(M, X.basicOpen g.1) :=
    Module.compHom Γ(M, X.basicOpen g.1)
      (algebraMap Γ(X, U) Γ(X, X.basicOpen g.1))
  let _ (g : s) : IsScalarTower Γ(X, U) Γ(X, X.basicOpen g.1)
      Γ(M, X.basicOpen g.1) :=
    IsScalarTower.of_compHom (A := Γ(X, X.basicOpen g.1))
      Γ(X, U) Γ(M, X.basicOpen g.1)
  let _ (g : s) : IsLocalization.Away g.1 Γ(X, X.basicOpen g.1) :=
    AlgebraicGeometry.isLocalization_basicOpen_of_qcqs hU hU' g.1
  let _ (g : s) : IsLocalizedModule.Away g.1 (basicOpenRestriction M g.1) :=
    isLocalizedModule_basicOpen_of_qcqs M hU hU' g.1
  exact Module.IsCoherent.of_localizationSpan' s hs
    (fun g ↦ basicOpenRestriction M g.1) h

/-- The global-sections specialization of
`isCoherent_of_span_basicOpen_of_qcqs`. -/
theorem isCoherent_of_span_basicOpen_of_qcqs_of_top
    (M : X.Modules) [M.IsQuasicoherent] [CompactSpace X] [QuasiSeparatedSpace X]
    (s : Set Γ(X, ⊤)) (hs : Ideal.span s = ⊤)
    (h : ∀ g : s,
      Module.IsCoherent Γ(X, X.basicOpen g.1) Γ(M, X.basicOpen g.1)) :
    Module.IsCoherent Γ(X, ⊤) Γ(M, ⊤) :=
  isCoherent_of_span_basicOpen_of_qcqs M CompactSpace.isCompact_univ
    isQuasiSeparated_univ s hs h

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

universe u

/-- The same-universe coherent-module property on the native category of
quasicoherent modules over an affine spectrum.

This is literally the inverse image of `ModuleCat.isCoherent` under the inverse
of `tildeEquiv`; it does not introduce a new notion of quasicoherence or identify
coherence with finite presentation. -/
def isCoherentOnSpec (R : CommRingCat.{u}) :
    ObjectProperty
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
  (ModuleCat.isCoherent.{u, u} R).inverseImage (tildeEquiv (R := R)).inverse

/-- Membership in `isCoherentOnSpec` is literally coherence of the module
obtained from affine global sections by `tildeEquiv.inverse`. -/
lemma isCoherentOnSpec_iff (R : CommRingCat.{u})
    (Q : (SheafOfModules.isQuasicoherent
      (Spec R).ringCatSheaf).FullSubcategory) :
    isCoherentOnSpec R Q ↔
      Module.IsCoherent R ((tildeEquiv (R := R)).inverse.obj Q) :=
  Iff.rfl

/-- A literal affine sheaf `tilde M` has the coherent affine property exactly
when `M` is a coherent module.  The statement follows the same-universe
boundary of mathlib's `tildeEquiv`. -/
lemma isCoherentOnSpec_tilde_iff (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    isCoherentOnSpec R
        (⟨tilde M, by
          change (tilde M).IsQuasicoherent
          infer_instance⟩ :
          (SheafOfModules.isQuasicoherent
            (Spec R).ringCatSheaf).FullSubcategory) ↔
      Module.IsCoherent R M := by
  change Module.IsCoherent R
      ((tildeEquiv (R := R)).inverse.obj
        ((tildeEquiv (R := R)).functor.obj M)) ↔ Module.IsCoherent R M
  exact (Module.IsCoherent.equiv_iff
    ((tildeEquiv (R := R)).unitIso.app M).toLinearEquiv).symm

end AlgebraicGeometry
