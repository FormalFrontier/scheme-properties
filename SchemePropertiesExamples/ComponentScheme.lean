/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.ComponentScheme
import Mathlib.Algebra.DualNumber

/-!
# Client checks for the component-scheme reflection

These checks exercise ordinary downstream use and the disconnected,
nonreduced, and empty affine cases without adding hypotheses to the public API.
-/

set_option warningAsError true

open CategoryTheory

universe u

namespace AlgebraicGeometry.ComponentSchemeClient

noncomputable section

variable {K B : Type u} [Field K] [CommRing B] [Algebra K B]

attribute [local instance] AlgebraicGeometry.globalSectionsAlgebraInstance

/-- Ordinary downstream use of the universal property. -/
example (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (hB : Algebra.IsFiniteEtale K B)
    (f : X ⟶ specOver K B) :
    ∃! g : componentScheme X ⟶ specOver K B,
      toComponentScheme X ≫ g = f :=
  componentScheme_universal X hB f

/-- The theorem applies to the disconnected algebra `Fin 2 → K`. -/
example (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (f : X ⟶ specOver K (Fin 2 → K)) :
    ∃! g : componentScheme X ⟶ specOver K (Fin 2 → K),
      toComponentScheme X ≫ g = f := by
  apply componentScheme_universal X
  exact ⟨inferInstance, inferInstance⟩

/-- No reducedness hypothesis is needed for the dual-number source. -/
example [LocallyOfFiniteType (specOver K (DualNumber K)).hom]
    [QuasiCompact (specOver K (DualNumber K)).hom]
    (hB : Algebra.IsFiniteEtale K B)
    (f : specOver K (DualNumber K) ⟶ specOver K B) :
    ∃! g : componentScheme (specOver K (DualNumber K)) ⟶ specOver K B,
      toComponentScheme (specOver K (DualNumber K)) ≫ g = f :=
  componentScheme_universal _ hB f

/-- A subsingleton algebra has empty affine spectrum; this case is included. -/
example {Z : Type u} [CommRing Z] [Algebra K Z] [Subsingleton Z]
    [LocallyOfFiniteType (specOver K Z).hom]
    [QuasiCompact (specOver K Z).hom]
    (h0 : Algebra.IsFiniteEtale K Z)
    (f : specOver K Z ⟶ specOver K Z) :
    ∃! g : componentScheme (specOver K Z) ⟶ specOver K Z,
      toComponentScheme (specOver K Z) ≫ g = f :=
  componentScheme_universal _ h0 f

/-- The chosen object agrees literally with any other greatest witness. -/
example (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (A : Subalgebra K Γ(X.left, ⊤))
    (hA : A.IsFiniteEtale)
    (hgreatest : ∀ C : Subalgebra K Γ(X.left, ⊤),
      C.IsFiniteEtale → C ≤ A) :
    componentSubalgebra X = A :=
  componentSubalgebra_eq_of_isGreatest X A hA hgreatest

end

end AlgebraicGeometry.ComponentSchemeClient
