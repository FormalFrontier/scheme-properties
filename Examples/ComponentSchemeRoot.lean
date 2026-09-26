module

import SchemeProperties
import Mathlib.Algebra.DualNumber

/-! Root-import client checks for the component-scheme reflection. -/

set_option warningAsError true

open CategoryTheory

universe u

namespace AlgebraicGeometry.ComponentSchemeRootClient

noncomputable section

variable {K : Type u} [Field K]

/-- The disconnected finite-etale target is available from the aggregate root. -/
private theorem check_1 (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (f : X ⟶ specOver K (Fin 2 → K)) :
    ∃! g : componentScheme X ⟶ specOver K (Fin 2 → K),
      toComponentScheme X ≫ g = f := by
  apply componentScheme_universal X
  exact ⟨inferInstance, inferInstance⟩

/-- The nonreduced dual-number source is available from the aggregate root. -/
private theorem check_2 {B : Type u} [CommRing B] [Algebra K B]
    [LocallyOfFiniteType (specOver K (DualNumber K)).hom]
    [QuasiCompact (specOver K (DualNumber K)).hom]
    (hB : Algebra.IsFiniteEtale K B)
    (f : specOver K (DualNumber K) ⟶ specOver K B) :
    ∃! g : componentScheme (specOver K (DualNumber K)) ⟶ specOver K B,
      toComponentScheme (specOver K (DualNumber K)) ≫ g = f :=
  componentScheme_universal _ hB f

/-- A subsingleton/empty affine source is available from the aggregate root. -/
private theorem check_3 {Z : Type u} [CommRing Z] [Algebra K Z] [Subsingleton Z]
    [LocallyOfFiniteType (specOver K Z).hom]
    [QuasiCompact (specOver K Z).hom]
    (h0 : Algebra.IsFiniteEtale K Z)
    (f : specOver K Z ⟶ specOver K Z) :
    ∃! g : componentScheme (specOver K Z) ⟶ specOver K Z,
      toComponentScheme (specOver K Z) ≫ g = f :=
  componentScheme_universal _ h0 f

end

end AlgebraicGeometry.ComponentSchemeRootClient
