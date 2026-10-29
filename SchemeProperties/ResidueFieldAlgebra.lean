/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.GlobalSectionsBaseChange
public import SchemeProperties.ResidueField
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Residue algebras over a specified base

For a specified structure morphism `π : X ⟶ Spec R`, the original `R`-action on
`X.residueField x` is evaluation of `π.globalSectionsAlgebra R` at `x`. We keep
this action explicit: none of the declarations installs a global residue-field
algebra instance or replaces an existing action supplied by a consumer.

A morphism over `Spec R` induces an algebra homomorphism on these original
residue fields. A specified isomorphism over `Spec R` induces an algebra
equivalence, contravariantly, whose underlying ring map is exactly Mathlib's
`Scheme.Hom.residueFieldMap`. Its linear equivalence preserves cardinal module
rank and natural finrank over any commutative base ring, without a finiteness
hypothesis. Over a field, different original residue degrees therefore obstruct
an exchange of points. For infinite extensions, finrank can be zero; cardinal
rank retains the dimension.

The scalar readbacks identify the action both with global evaluation and with
the structure morphism's residue-field map. The construction reuses Mathlib's
residue-map naturality, the open-immersion `IsIso` instance, `asIso`, and
`AlgEquiv.ofRingEquiv`; no new inverse or monomorphism argument is needed.

## References

* Mathlib's canonical scheme residue fields and evaluation naturality.
* Mathlib's commutative-ring isomorphism and algebra-equivalence constructors.
* `Scheme.Hom.globalSectionsAlgebra` for the specified structure morphism.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- Evaluation of the given global-sections algebra is the original scalar map
`R → Γ(X, ⊤) → κ(x)`. The algebra arguments are fixed explicitly. -/
theorem Hom.algebraMap_residueField (π : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    @algebraMap R (X.residueField x) _ _
        (((X.Γevaluation x).hom.comp
          (@algebraMap R Γ(X, ⊤) _ _ (π.globalSectionsAlgebra R))).toAlgebra) =
      ((ΓSpecIso (CommRingCat.of R)).inv ≫ π.appTop ≫ X.Γevaluation x).hom :=
  rfl

/-- The original scalar action also factors through the residue field at the
image of the point in the specified base. -/
theorem Hom.algebraMap_residueField_eq_residueFieldMap
    (π : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    @algebraMap R (X.residueField x) _ _
        (((X.Γevaluation x).hom.comp
          (@algebraMap R Γ(X, ⊤) _ _ (π.globalSectionsAlgebra R))).toAlgebra) =
      ((ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec (CommRingCat.of R)).Γevaluation (π x) ≫ π.residueFieldMap x).hom := by
  rw [Hom.algebraMap_residueField, Γevaluation_naturality]

/-- Elementwise readback of the original scalar action through the base residue
field. No auxiliary field or independently chosen scalar action occurs. -/
theorem Hom.algebraMap_residueField_apply
    (π : X ⟶ Spec (CommRingCat.of R)) (x : X) (r : R) :
    (@algebraMap R (X.residueField x) _ _
        (((X.Γevaluation x).hom.comp
          (@algebraMap R Γ(X, ⊤) _ _ (π.globalSectionsAlgebra R))).toAlgebra)) r =
      π.residueFieldMap x
        ((Spec (CommRingCat.of R)).Γevaluation (π x)
          ((ΓSpecIso (CommRingCat.of R)).inv r)) :=
  congrArg (fun g : R →+* X.residueField x => g r)
    (π.algebraMap_residueField_eq_residueFieldMap x)

/-- A morphism over the specified affine base respects the original
structure maps on global sections. -/
theorem Hom.globalSectionsAlgebra_map (f : X ⟶ Y)
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (hf : f ≫ πY = πX) :
    f.appTop.hom.comp (@algebraMap R Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra R)) =
      @algebraMap R Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra R) := by
  change ((ΓSpecIso (CommRingCat.of R)).inv ≫ πY.appTop ≫ f.appTop).hom =
    ((ΓSpecIso (CommRingCat.of R)).inv ≫ πX.appTop).hom
  rw [← Hom.comp_appTop, hf]

/-- The canonical residue-field map of a base-compatible morphism respects the
original scalar actions obtained from its two specified structure morphisms. -/
theorem Hom.residueFieldMap_algebraMap (f : X ⟶ Y)
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (hf : f ≫ πY = πX) (x : X) :
    (f.residueFieldMap x).hom.comp
        (@algebraMap R (Y.residueField (f x)) _ _
          (((Y.Γevaluation (f x)).hom.comp
            (@algebraMap R Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra R))).toAlgebra)) =
      @algebraMap R (X.residueField x) _ _
        (((X.Γevaluation x).hom.comp
          (@algebraMap R Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra R))).toAlgebra) := by
  ext r
  change f.residueFieldMap x
      (Y.Γevaluation (f x)
        ((@algebraMap R Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra R)) r)) =
    X.Γevaluation x
      ((@algebraMap R Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra R)) r)
  rw [Γevaluation_naturality_apply]
  exact congrArg (fun s : Γ(X, ⊤) => X.Γevaluation x s)
    (congrArg (fun g : R →+* Γ(X, ⊤) => g r)
      (f.globalSectionsAlgebra_map πX πY hf))

/-- The canonical contravariant algebra homomorphism on original residue fields
of a morphism over the given `Spec R`. -/
def Hom.residueFieldAlgHom (f : X ⟶ Y)
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (hf : f ≫ πY = πX) (x : X) :
    @AlgHom R (Y.residueField (f x)) (X.residueField x) _ _ _
      (((Y.Γevaluation (f x)).hom.comp
        (@algebraMap R Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra R))).toAlgebra)
      (((X.Γevaluation x).hom.comp
        (@algebraMap R Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra R))).toAlgebra) := by
  letI := (((Y.Γevaluation (f x)).hom.comp
    (@algebraMap R Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra R))).toAlgebra)
  letI := (((X.Γevaluation x).hom.comp
    (@algebraMap R Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra R))).toAlgebra)
  exact
    { toRingHom := (f.residueFieldMap x).hom
      commutes' := fun r => congrArg (fun g : R →+* X.residueField x => g r)
        (f.residueFieldMap_algebraMap πX πY hf x) }

/-- The promoted algebra homomorphism retains exactly the canonical ring map. -/
@[simp]
theorem Hom.residueFieldAlgHom_toRingHom (f : X ⟶ Y)
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (hf : f ≫ πY = πX) (x : X) :
    (f.residueFieldAlgHom πX πY hf x : Y.residueField (f x) →+* X.residueField x) =
      (f.residueFieldMap x).hom :=
  rfl

/-- Elementwise readback of the promoted map, without unfolding its definition. -/
@[simp]
theorem Hom.residueFieldAlgHom_apply (f : X ⟶ Y)
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (hf : f ≫ πY = πX) (x : X) (a : Y.residueField (f x)) :
    f.residueFieldAlgHom πX πY hf x a = f.residueFieldMap x a :=
  rfl

/-- A specified base-compatible isomorphism gives the canonical contravariant
`R`-algebra equivalence on the original residue fields and original actions. -/
def residueFieldAlgEquiv
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (e : X ≅ Y) (he : e.hom ≫ πY = πX) (x : X) :
    @AlgEquiv R (Y.residueField (e.hom x)) (X.residueField x) _ _ _
      (((Y.Γevaluation (e.hom x)).hom.comp
        (@algebraMap R Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra R))).toAlgebra)
      (((X.Γevaluation x).hom.comp
        (@algebraMap R Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra R))).toAlgebra) := by
  letI := (((Y.Γevaluation (e.hom x)).hom.comp
    (@algebraMap R Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra R))).toAlgebra)
  letI := (((X.Γevaluation x).hom.comp
    (@algebraMap R Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra R))).toAlgebra)
  exact AlgEquiv.ofRingEquiv
    (f := (asIso (e.hom.residueFieldMap x)).commRingCatIsoToRingEquiv)
    (fun r => by
      simpa only [Hom.residueFieldAlgHom_apply, Iso.commRingCatIsoToRingEquiv,
        RingEquiv.ofRingHom_apply, asIso_hom]
        using (e.hom.residueFieldAlgHom πX πY he x).commutes r)

/-- The equivalence's forward ring map is the stock residue-field map, not an
unspecified field isomorphism. -/
@[simp]
theorem residueFieldAlgEquiv_toRingHom
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (e : X ≅ Y) (he : e.hom ≫ πY = πX) (x : X) :
    (residueFieldAlgEquiv πX πY e he x :
        Y.residueField (e.hom x) →+* X.residueField x) =
      (e.hom.residueFieldMap x).hom :=
  rfl

/-- Elementwise readback of the equivalence's canonical forward map. -/
@[simp]
theorem residueFieldAlgEquiv_apply
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (e : X ≅ Y) (he : e.hom ≫ πY = πX) (x : X)
    (a : Y.residueField (e.hom x)) :
    residueFieldAlgEquiv πX πY e he x a = e.hom.residueFieldMap x a :=
  rfl

section ModuleDimension

variable {k : Type u} [CommRing k]

/-- Cardinal module rank over the original commutative base ring is invariant
under a specified base-compatible isomorphism. No finiteness assumption is used. -/
theorem residueField_rank_eq
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k))
    (e : X ≅ Y) (he : e.hom ≫ πY = πX) (x : X) :
    @Module.rank k (Y.residueField (e.hom x)) _ _
        (@Algebra.toModule k (Y.residueField (e.hom x)) _ _
          (((Y.Γevaluation (e.hom x)).hom.comp
            (@algebraMap k Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra k))).toAlgebra)) =
      @Module.rank k (X.residueField x) _ _
        (@Algebra.toModule k (X.residueField x) _ _
          (((X.Γevaluation x).hom.comp
            (@algebraMap k Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra k))).toAlgebra)) := by
  let : Algebra k (Y.residueField (e.hom x)) :=
    (((Y.Γevaluation (e.hom x)).hom.comp
      (@algebraMap k Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra k))).toAlgebra)
  let : Algebra k (X.residueField x) :=
    (((X.Γevaluation x).hom.comp
      (@algebraMap k Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra k))).toAlgebra)
  exact (residueFieldAlgEquiv πX πY e he x).toLinearEquiv.rank_eq

/-- Natural module finrank over the original commutative base ring is invariant
under a specified base-compatible isomorphism. No finiteness assumption is used;
finrank is zero when the cardinal module rank is infinite. -/
theorem residueField_finrank_eq
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k))
    (e : X ≅ Y) (he : e.hom ≫ πY = πX) (x : X) :
    @Module.finrank k (Y.residueField (e.hom x)) _ _
        (@Algebra.toModule k (Y.residueField (e.hom x)) _ _
          (((Y.Γevaluation (e.hom x)).hom.comp
            (@algebraMap k Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra k))).toAlgebra)) =
      @Module.finrank k (X.residueField x) _ _
        (@Algebra.toModule k (X.residueField x) _ _
          (((X.Γevaluation x).hom.comp
            (@algebraMap k Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra k))).toAlgebra)) := by
  let : Algebra k (Y.residueField (e.hom x)) :=
    (((Y.Γevaluation (e.hom x)).hom.comp
      (@algebraMap k Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra k))).toAlgebra)
  let : Algebra k (X.residueField x) :=
    (((X.Γevaluation x).hom.comp
      (@algebraMap k Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra k))).toAlgebra)
  exact (residueFieldAlgEquiv πX πY e he x).toLinearEquiv.finrank_eq

end ModuleDimension

end AlgebraicGeometry.Scheme
