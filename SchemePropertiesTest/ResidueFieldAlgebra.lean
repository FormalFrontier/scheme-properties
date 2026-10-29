/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ResidueFieldAlgebra
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Residue-algebra API checks

These checks use arbitrary schemes and a specified structure morphism. They
exercise the canonical map and scalar readbacks without unfolding the data
constructors, and the equivalence for the identity over the same base. The
field-spectrum checks recover degree one for the identity extension and the
original integer scalars for the nonfield-base algebra `ℤ → ℚ`.
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

/-- The identity field extension has original residue finrank one at every point. -/
theorem spec_residueField_finrank_self (k : Type u) [Field k]
    (x : Spec (CommRingCat.of k)) :
    @Module.finrank k ((Spec (CommRingCat.of k)).residueField x) _ _
        (@Algebra.toModule k ((Spec (CommRingCat.of k)).residueField x) _ _
          ((((Spec (CommRingCat.of k)).Γevaluation x).hom.comp
            (@algebraMap k Γ(Spec (CommRingCat.of k), ⊤) _ _
              ((Spec.map
                (CommRingCat.ofHom (algebraMap k k))).globalSectionsAlgebra k))).toAlgebra)) = 1 :=
  (Scheme.Spec.residueField_finrank_eq k k x).trans (Module.finrank_self k)

/-- The canonical equivalence for `Spec ℚ` over `Spec ℤ` reads the original
integer scalar as the corresponding rational number. No field base is needed. -/
theorem spec_rat_residueField_intCast (x : Spec (CommRingCat.of ℚ)) (n : ℤ) :
    Scheme.Spec.residueFieldAlgEquiv ℤ ℚ x
        (((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))).appTop ≫
          (Spec (CommRingCat.of ℚ)).Γevaluation x) n) = (n : ℚ) :=
  Scheme.Spec.residueFieldAlgEquiv_algebraMap ℤ ℚ x n
