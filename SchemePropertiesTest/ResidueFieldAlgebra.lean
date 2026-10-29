/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ResidueFieldAlgebra

/-!
# Residue-algebra API checks

These checks use arbitrary schemes and a specified structure morphism. They
exercise the canonical map and scalar readbacks without unfolding the data
constructors, and the equivalence for the identity over the same base.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

example (πX : X ⟶ Spec (CommRingCat.of R))
    (πY : Y ⟶ Spec (CommRingCat.of R)) (e : X ≅ Y)
    (he : e.hom ≫ πY = πX) (x : X) (r : R) :
    Scheme.residueFieldAlgEquiv πX πY e he x
        ((@algebraMap R (Y.residueField (e.hom x)) _ _
          (((Y.Γevaluation (e.hom x)).hom.comp
            (@algebraMap R Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra R))).toAlgebra)) r) =
      (@algebraMap R (X.residueField x) _ _
        (((X.Γevaluation x).hom.comp
          (@algebraMap R Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra R))).toAlgebra)) r := by
  let : Algebra R (Y.residueField (e.hom x)) :=
    (((Y.Γevaluation (e.hom x)).hom.comp
      (@algebraMap R Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra R))).toAlgebra)
  let : Algebra R (X.residueField x) :=
    (((X.Γevaluation x).hom.comp
      (@algebraMap R Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra R))).toAlgebra)
  exact (Scheme.residueFieldAlgEquiv πX πY e he x).commutes r

example (π : X ⟶ Spec (CommRingCat.of R)) (x : X) (a : X.residueField x) :
    Scheme.residueFieldAlgEquiv π π (Iso.refl X) (by simp) x a = a := by
  exact
    (Scheme.residueFieldAlgEquiv_apply π π (Iso.refl X) (by simp) x a).trans
      (congrArg (fun f : X.residueField x ⟶ X.residueField x => f a)
        (Scheme.residueFieldMap_id x))
