/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.CoherentQuasicoherent
import SchemeProperties.QuasicoherentAbelian

set_option warningAsError true

open CategoryTheory Limits TopologicalSpace ZeroObject
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

example (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1) (f : Γ(X, U))
    [Module.IsCoherent Γ(X, U) Γ(M, U)] :
    Module.IsCoherent Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
  isCoherent_basicOpen_of_qcqs M hU hU' f inferInstance

example (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    [Module.IsCoherent Γ(X, U) Γ(M, U)] :
    Module.IsCoherent Γ(X, X.basicOpen (0 : Γ(X, U)))
      Γ(M, X.basicOpen (0 : Γ(X, U))) :=
  isCoherent_basicOpen_of_qcqs M hU hU' 0 inferInstance

example (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    [Module.IsCoherent Γ(X, U) Γ(M, U)] :
    Module.IsCoherent Γ(X, X.basicOpen (1 : Γ(X, U)))
      Γ(M, X.basicOpen (1 : Γ(X, U))) :=
  isCoherent_basicOpen_of_qcqs M hU hU' 1 inferInstance

example {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (f : Γ(X, U)) :
    Module.IsCoherent Γ(X, X.basicOpen f)
      Γ((0 : X.Modules), X.basicOpen f) := by
  let _ : (0 : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_zero
  apply isCoherent_basicOpen_of_qcqs (0 : X.Modules) hU hU' f
  have hzero : IsZero ((0 : X.Modules).presheaf.obj (.op U)) :=
    ((CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat).obj (.op U)).map_isZero
      ((toPresheaf X).map_isZero (isZero_zero X.Modules))
  let _ : Subsingleton Γ((0 : X.Modules), U) :=
    AddCommGrpCat.subsingleton_of_isZero hzero
  infer_instance

example (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (s : Set Γ(X, U)) (hs : Ideal.span s = ⊤)
    (h : ∀ g : s,
      Module.IsCoherent Γ(X, X.basicOpen g.1) Γ(M, X.basicOpen g.1)) :
    Module.IsCoherent Γ(X, U) Γ(M, U) :=
  isCoherent_of_span_basicOpen_of_qcqs M hU hU' s hs h

/-- The empty spanning family is valid when the ambient section ring is the
zero ring; no artificial `Nonempty` premise is needed. -/
example (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    [Subsingleton Γ(X, U)] : Module.IsCoherent Γ(X, U) Γ(M, U) := by
  apply isCoherent_of_span_basicOpen_of_qcqs M hU hU'
      (∅ : Set Γ(X, U)) (Subsingleton.elim _ _)
  intro g
  exact g.property.elim

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

universe u

example (R : CommRingCat.{u})
    (Q : (SheafOfModules.isQuasicoherent
      (Spec R).ringCatSheaf).FullSubcategory) :
    isCoherentOnSpec R Q ↔
      Module.IsCoherent R ((tildeEquiv (R := R)).inverse.obj Q) :=
  isCoherentOnSpec_iff R Q

example (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    isCoherentOnSpec R
        (⟨tilde M, by
          change (tilde M).IsQuasicoherent
          infer_instance⟩ :
          (SheafOfModules.isQuasicoherent
            (Spec R).ringCatSheaf).FullSubcategory) ↔
      Module.IsCoherent R M :=
  isCoherentOnSpec_tilde_iff R M

end AlgebraicGeometry
