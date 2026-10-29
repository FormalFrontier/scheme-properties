/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.GlobalSectionsBaseChange
public import SchemeProperties.ResidueField
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

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

For a given algebra over a commutative ring `k` whose carrier `K` is a field,
`Spec.residueFieldAlgEquiv` identifies each original residue algebra of `Spec K`
with the given `k`-algebra `K`. It composes the scheme-to-ideal residue isomorphism
with the inverse of `Ideal.algEquivResidueFieldOfField`; the scalar bridge comes
from the naturality of `ΓSpecIso`. The module rank and finrank corollaries also
hold over any commutative base ring; they express residue-field degrees when the
base is a field.

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

/-- An open immersion induces an isomorphism on its canonical residue-field map.
This is an explicit-term form of the residue-field instance. -/
theorem Hom.isIso_residueFieldMap_of_isOpenImmersion (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) : IsIso (f.residueFieldMap x) :=
  inferInstance

/-- A base-compatible morphism whose residue map is an isomorphism at `x`
induces an algebra equivalence on the original residue algebras. -/
def Hom.residueFieldAlgEquiv (f : X ⟶ Y)
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (hf : f ≫ πY = πX) (x : X) [IsIso (f.residueFieldMap x)] :
    @AlgEquiv R (Y.residueField (f x)) (X.residueField x) _ _ _
      (((Y.Γevaluation (f x)).hom.comp
        (@algebraMap R Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra R))).toAlgebra)
      (((X.Γevaluation x).hom.comp
        (@algebraMap R Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra R))).toAlgebra) := by
  letI := (((Y.Γevaluation (f x)).hom.comp
    (@algebraMap R Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra R))).toAlgebra)
  letI := (((X.Γevaluation x).hom.comp
    (@algebraMap R Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra R))).toAlgebra)
  exact AlgEquiv.ofBijective (f.residueFieldAlgHom πX πY hf x)
    (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.bijective

/-- Promotion to an equivalence preserves the canonical algebra homomorphism. -/
@[simp]
theorem Hom.residueFieldAlgEquiv_toAlgHom (f : X ⟶ Y)
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (hf : f ≫ πY = πX) (x : X) [IsIso (f.residueFieldMap x)] :
    @AlgEquiv.toAlgHom R (Y.residueField (f x)) (X.residueField x) _ _ _
        (((Y.Γevaluation (f x)).hom.comp
          (@algebraMap R Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra R))).toAlgebra)
        (((X.Γevaluation x).hom.comp
          (@algebraMap R Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra R))).toAlgebra)
        (f.residueFieldAlgEquiv πX πY hf x) =
      f.residueFieldAlgHom πX πY hf x :=
  rfl

/-- The equivalence has the same underlying canonical residue-field ring map. -/
@[simp]
theorem Hom.residueFieldAlgEquiv_toRingHom (f : X ⟶ Y)
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (hf : f ≫ πY = πX) (x : X) [IsIso (f.residueFieldMap x)] :
    (f.residueFieldAlgEquiv πX πY hf x : Y.residueField (f x) →+* X.residueField x) =
      (f.residueFieldMap x).hom :=
  rfl

/-- Elementwise readback of the residue-algebra equivalence. -/
@[simp]
theorem Hom.residueFieldAlgEquiv_apply (f : X ⟶ Y)
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (hf : f ≫ πY = πX) (x : X) [IsIso (f.residueFieldMap x)]
    (a : Y.residueField (f x)) :
    f.residueFieldAlgEquiv πX πY hf x a = f.residueFieldMap x a :=
  rfl

/-- The promoted equivalence carries the original base scalar map to the
original base scalar map at the source point. -/
theorem Hom.residueFieldAlgEquiv_algebraMap (f : X ⟶ Y)
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (hf : f ≫ πY = πX) (x : X) [IsIso (f.residueFieldMap x)] (r : R) :
    f.residueFieldAlgEquiv πX πY hf x
        ((@algebraMap R (Y.residueField (f x)) _ _
          (((Y.Γevaluation (f x)).hom.comp
            (@algebraMap R Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra R))).toAlgebra)) r) =
      (@algebraMap R (X.residueField x) _ _
        (((X.Γevaluation x).hom.comp
          (@algebraMap R Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra R))).toAlgebra)) r := by
  let : Algebra R (Y.residueField (f x)) :=
    (((Y.Γevaluation (f x)).hom.comp
      (@algebraMap R Γ(Y, ⊤) _ _ (πY.globalSectionsAlgebra R))).toAlgebra)
  let : Algebra R (X.residueField x) :=
    (((X.Γevaluation x).hom.comp
      (@algebraMap R Γ(X, ⊤) _ _ (πX.globalSectionsAlgebra R))).toAlgebra)
  exact (f.residueFieldAlgHom πX πY hf x).commutes r

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

section SpecField

variable (k K : Type u) [CommRing k] [Field K] [Algebra k K]

/-- On the spectrum of a field extension, the original scalar map factors through
its given algebra map and the inverse of the scheme-to-ideal residue isomorphism. -/
theorem Spec.algebraMap_residueField (x : PrimeSpectrum K) :
    @algebraMap k ((Spec (CommRingCat.of K)).residueField x) _ _
        ((((Spec (CommRingCat.of K)).Γevaluation x).hom.comp
          (@algebraMap k Γ(Spec (CommRingCat.of K), ⊤) _ _
            ((Spec.map
              (CommRingCat.ofHom (algebraMap k K))).globalSectionsAlgebra k))).toAlgebra) =
      (CommRingCat.ofHom (algebraMap k K) ≫
        CommRingCat.ofHom (algebraMap K x.asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (CommRingCat.of K) x).inv).hom := by
  erw [Hom.algebraMap_residueField
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (show Spec (CommRingCat.of K) from x), ← ΓSpecIso_inv_naturality_assoc]
  exact congrArg
    (fun f : CommRingCat.of K ⟶ (Spec (CommRingCat.of K)).residueField x =>
      (CommRingCat.ofHom (algebraMap k K) ≫ f).hom)
    (Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of K) x).symm

/-- The canonical equivalence from the original residue algebra of `Spec K` over
`Spec k` to the given `k`-algebra `K`. Its ring equivalence is the scheme-to-ideal
residue isomorphism followed by the inverse of the field's residue equivalence. -/
def Spec.residueFieldAlgEquiv (x : PrimeSpectrum K) :
    @AlgEquiv k ((Spec (CommRingCat.of K)).residueField x) K _ _ _
      ((((Spec (CommRingCat.of K)).Γevaluation x).hom.comp
        (@algebraMap k Γ(Spec (CommRingCat.of K), ⊤) _ _
          ((Spec.map
            (CommRingCat.ofHom (algebraMap k K))).globalSectionsAlgebra k))).toAlgebra)
      inferInstance := by
  letI : Algebra k ((Spec (CommRingCat.of K)).residueField x) :=
    ((((Spec (CommRingCat.of K)).Γevaluation x).hom.comp
      (@algebraMap k Γ(Spec (CommRingCat.of K), ⊤) _ _
        ((Spec.map
          (CommRingCat.ofHom (algebraMap k K))).globalSectionsAlgebra k))).toAlgebra)
  let σ := (Scheme.Spec.residueFieldIso (CommRingCat.of K) x).commRingCatIsoToRingEquiv
  let τ := x.asIdeal.algEquivResidueFieldOfField
  apply AlgEquiv.ofRingEquiv (f := σ.trans τ.symm.toRingEquiv)
  intro r
  rw [Scheme.Spec.algebraMap_residueField k K x]
  change τ.symm (σ (σ.symm (algebraMap K x.asIdeal.ResidueField
    (algebraMap k K r)))) = algebraMap k K r
  rw [σ.apply_symm_apply,
    ← Ideal.algEquivResidueFieldOfField_apply x.asIdeal (algebraMap k K r),
    τ.symm_apply_apply]

/-- The underlying ring equivalence is the composite of the two canonical
residue-field equivalences. -/
theorem Spec.residueFieldAlgEquiv_toRingEquiv (x : PrimeSpectrum K) :
    @AlgEquiv.toRingEquiv k ((Spec (CommRingCat.of K)).residueField x) K _ _ _
        ((((Spec (CommRingCat.of K)).Γevaluation x).hom.comp
          (@algebraMap k Γ(Spec (CommRingCat.of K), ⊤) _ _
            ((Spec.map
              (CommRingCat.ofHom (algebraMap k K))).globalSectionsAlgebra k))).toAlgebra)
        inferInstance (Scheme.Spec.residueFieldAlgEquiv k K x) =
      (Scheme.Spec.residueFieldIso (CommRingCat.of K) x).commRingCatIsoToRingEquiv.trans
        x.asIdeal.algEquivResidueFieldOfField.symm.toRingEquiv :=
  rfl

/-- The forward ring map of the canonical equivalence, in terms of the scheme
residue isomorphism and the inverse field residue equivalence. -/
@[simp]
theorem Spec.residueFieldAlgEquiv_toRingHom (x : PrimeSpectrum K) :
    (Scheme.Spec.residueFieldAlgEquiv k K x :
        (Spec (CommRingCat.of K)).residueField x →+* K) =
      (x.asIdeal.algEquivResidueFieldOfField.symm : x.asIdeal.ResidueField →+* K).comp
        (Scheme.Spec.residueFieldIso (CommRingCat.of K) x).hom.hom :=
  rfl

/-- Evaluation of the canonical algebra equivalence on a residue-field element. -/
@[simp]
theorem Spec.residueFieldAlgEquiv_apply (x : PrimeSpectrum K)
    (a : (Spec (CommRingCat.of K)).residueField x) :
    Scheme.Spec.residueFieldAlgEquiv k K x a =
      x.asIdeal.algEquivResidueFieldOfField.symm
        ((Scheme.Spec.residueFieldIso (CommRingCat.of K) x).hom a) :=
  rfl

/-- The canonical equivalence carries the original scalar action to the given
scalar action on `K`. -/
theorem Spec.residueFieldAlgEquiv_algebraMap (x : PrimeSpectrum K) (r : k) :
    Scheme.Spec.residueFieldAlgEquiv k K x
        ((@algebraMap k ((Spec (CommRingCat.of K)).residueField x) _ _
          ((((Spec (CommRingCat.of K)).Γevaluation x).hom.comp
            (@algebraMap k Γ(Spec (CommRingCat.of K), ⊤) _ _
              ((Spec.map
                (CommRingCat.ofHom (algebraMap k K))).globalSectionsAlgebra k))).toAlgebra)) r) =
      algebraMap k K r := by
  let : Algebra k ((Spec (CommRingCat.of K)).residueField x) :=
    ((((Spec (CommRingCat.of K)).Γevaluation x).hom.comp
      (@algebraMap k Γ(Spec (CommRingCat.of K), ⊤) _ _
        ((Spec.map
          (CommRingCat.ofHom (algebraMap k K))).globalSectionsAlgebra k))).toAlgebra)
  exact (Scheme.Spec.residueFieldAlgEquiv k K x).commutes r

end SpecField

section SpecFieldDimension

variable (k K : Type u) [CommRing k] [Field K] [Algebra k K]

/-- Cardinal module rank of the original residue algebra of a field spectrum
agrees with that of the given algebra over the commutative base ring. -/
theorem Spec.residueField_rank_eq (x : PrimeSpectrum K) :
    @Module.rank k ((Spec (CommRingCat.of K)).residueField x) _ _
        (@Algebra.toModule k ((Spec (CommRingCat.of K)).residueField x) _ _
          ((((Spec (CommRingCat.of K)).Γevaluation x).hom.comp
            (@algebraMap k Γ(Spec (CommRingCat.of K), ⊤) _ _
              ((Spec.map
                (CommRingCat.ofHom (algebraMap k K))).globalSectionsAlgebra k))).toAlgebra)) =
      Module.rank k K := by
  let : Algebra k ((Spec (CommRingCat.of K)).residueField x) :=
    ((((Spec (CommRingCat.of K)).Γevaluation x).hom.comp
      (@algebraMap k Γ(Spec (CommRingCat.of K), ⊤) _ _
        ((Spec.map
          (CommRingCat.ofHom (algebraMap k K))).globalSectionsAlgebra k))).toAlgebra)
  exact (Scheme.Spec.residueFieldAlgEquiv k K x).toLinearEquiv.rank_eq

/-- Natural module finrank of the original residue algebra of a field spectrum
agrees with that of the given algebra over the commutative base ring. No finiteness
hypothesis is needed; both finranks are zero when the cardinal module rank is infinite. -/
theorem Spec.residueField_finrank_eq (x : PrimeSpectrum K) :
    @Module.finrank k ((Spec (CommRingCat.of K)).residueField x) _ _
        (@Algebra.toModule k ((Spec (CommRingCat.of K)).residueField x) _ _
          ((((Spec (CommRingCat.of K)).Γevaluation x).hom.comp
            (@algebraMap k Γ(Spec (CommRingCat.of K), ⊤) _ _
              ((Spec.map
                (CommRingCat.ofHom (algebraMap k K))).globalSectionsAlgebra k))).toAlgebra)) =
      Module.finrank k K := by
  let : Algebra k ((Spec (CommRingCat.of K)).residueField x) :=
    ((((Spec (CommRingCat.of K)).Γevaluation x).hom.comp
      (@algebraMap k Γ(Spec (CommRingCat.of K), ⊤) _ _
        ((Spec.map
          (CommRingCat.ofHom (algebraMap k K))).globalSectionsAlgebra k))).toAlgebra)
  exact (Scheme.Spec.residueFieldAlgEquiv k K x).toLinearEquiv.finrank_eq

end SpecFieldDimension

end AlgebraicGeometry.Scheme
