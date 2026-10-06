/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.FiniteTypeSingleCover
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Power images and single faithfully flat extensions

On finitely generated algebras over any commutative ring, including the zero
ring, the image of the `n`th-power map on units is one-cover dense for positive
`n`. An explicit cover adjoining one root of a unit is a finite free algebra.
Over a field and for `n ≥ 2`, this image is not the full functor and does not
satisfy singleton faithfully flat descent. In contrast, the zero subfunctor of
the additive affine-line functor is not one-cover dense over a field.

These examples distinguish one-cover density from objectwise surjectivity and
from descent for the subfunctor. The represented target in the extension theorem
does satisfy descent; its one-cover dense source need not.

## References

- J. S. Milne, *Algebraic Groups*, the example following Definition 5.6,
  for the power image of units. The zero-additive nonfat example is an
  independently derived boundary, not a printed example there.
- Mathlib's `AdjoinRoot`, `LaurentPolynomial`, `CommMonCat.units`, and `Subfunctor.range`.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

section General

variable (K : Type u) [CommRing K]

/-- Units of each finitely generated algebra, using Mathlib's functor of
units on commutative monoids. -/
def unitsPoints : FGAlgCat.{u} K ⥤ Type u :=
  ObjectProperty.ι (fun A : CommAlgCat.{u} K ↦ Algebra.FiniteType K A) ⋙
    forget₂ (CommAlgCat.{u} K) CommRingCat.{u} ⋙
    forget₂ CommRingCat.{u} CommMonCat.{u} ⋙
    CommMonCat.units.{u} ⋙ forget CommGrpCat.{u}

/-- Units of a test algebra are the values of the unit functor at that algebra. -/
theorem unitsPoints_obj (A : FGAlgCat.{u} K) :
    (unitsPoints K).obj A = (A.obj : Type u)ˣ := rfl

/-- The `n`th-power transformation on units of finite-type test algebras. -/
def unitsPowerMap (n : ℕ) : unitsPoints K ⟶ unitsPoints K where
  app A := ↾(fun a : (A.obj : Type u)ˣ ↦ a ^ n)
  naturality X Y f := by
    ext a
    change (Units.map f.hom.hom.toMonoidHom (show (X.obj : Type u)ˣ from a)) ^ n =
      Units.map f.hom.hom.toMonoidHom ((show (X.obj : Type u)ˣ from a) ^ n)
    exact (map_pow _ _ n).symm

/-- The power transformation acts by taking `n`th powers on units. -/
@[simp]
theorem unitsPowerMap_apply (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) :
    (unitsPowerMap K n).app A a = a ^ n := rfl

/-- Units viewed as a presheaf on the opposite category of affine tests. -/
def unitsTestPoints : ((FGAlgCat.{u} K)ᵒᵖ)ᵒᵖ ⥤ Type u :=
  unopUnop (FGAlgCat.{u} K) ⋙ unitsPoints K

/-- The image of the `n`th-power map, not a pointwise-surjectivity assumption. -/
def powerImage (n : ℕ) : Subfunctor (unitsTestPoints K) :=
  Subfunctor.range (Functor.whiskerLeft (unopUnop (FGAlgCat.{u} K)) (unitsPowerMap K n))

/-- Membership in the power image is existence of a root in the same test algebra. -/
theorem mem_powerImage_iff (n : ℕ) (A : FGAlgCat.{u} K) (a : (A.obj : Type u)ˣ) :
    a ∈ (powerImage K n).obj (op (op A)) ↔
      ∃ b : (A.obj : Type u)ˣ, b ^ n = a := by
  rfl

/-- The monic polynomial defining the one-root extension of a unit. -/
noncomputable def powerRootPolynomial (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) :
    Polynomial (A.obj : Type u) :=
  Polynomial.X ^ n - Polynomial.C (a : A.obj)

/-- The single finitely generated algebra `A[T]/(T^n-a)` adjoining a root. -/
noncomputable def powerRootAlgebra (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) :
    FGAlgCat.{u} K :=
  ⟨CommAlgCat.of K (AdjoinRoot (powerRootPolynomial K n A a)), inferInstance⟩

/-- The canonical algebra map into the one-root extension. -/
noncomputable def powerRootMap (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) :
    A ⟶ powerRootAlgebra K n A a :=
  ObjectProperty.homMk (CommAlgCat.ofHom
    (AdjoinRoot.ofAlgHom K (powerRootPolynomial K n A a)))

private theorem powerRoot_pow_eq (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) :
    AdjoinRoot.root (powerRootPolynomial K n A a) ^ n =
      AdjoinRoot.of (powerRootPolynomial K n A a) a := by
  have h := AdjoinRoot.eval₂_root (powerRootPolynomial K n A a)
  change Polynomial.eval₂ (AdjoinRoot.of (powerRootPolynomial K n A a))
    (AdjoinRoot.root (powerRootPolynomial K n A a))
    (Polynomial.X ^ n - Polynomial.C (a : A.obj)) = 0 at h
  simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, sub_eq_zero] using h

/-- The one-root extension is free over the original algebra. -/
theorem powerRootAlgebra_free (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) (hn : 0 < n) :
    Module.Free (A.obj : Type u) (AdjoinRoot (powerRootPolynomial K n A a)) := by
  exact (Polynomial.monic_X_pow_sub_C (a : A.obj) (Nat.ne_of_gt hn)).free_adjoinRoot

/-- The one-root extension is finite over the original algebra. -/
theorem powerRootAlgebra_finite (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) (hn : 0 < n) :
    Module.Finite (A.obj : Type u) (AdjoinRoot (powerRootPolynomial K n A a)) := by
  exact (Polynomial.monic_X_pow_sub_C (a : A.obj) (Nat.ne_of_gt hn)).finite_adjoinRoot

/-- The polynomial's canonical root is invertible when the constant term
is a unit and its positive-degree power is that unit. -/
theorem powerRoot_isUnit (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) (hn : 0 < n) :
    IsUnit (AdjoinRoot.root (powerRootPolynomial K n A a)) := by
  rw [← isUnit_pow_iff (Nat.ne_of_gt hn), powerRoot_pow_eq]
  exact (Units.isUnit a).map (AdjoinRoot.of (powerRootPolynomial K n A a))

/-- The canonical invertible root in the finite free root extension. -/
noncomputable def powerRootUnit (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) (hn : 0 < n) :
    ((powerRootAlgebra K n A a).obj : Type u)ˣ :=
  (powerRoot_isUnit K n A a hn).unit

/-- The invertible root raises to the image of the original unit. -/
theorem powerRootUnit_pow (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) (hn : 0 < n) :
    powerRootUnit K n A a hn ^ n =
      Units.map (powerRootMap K n A a).hom.hom.toMonoidHom a := by
  apply Units.ext
  change ((powerRoot_isUnit K n A a hn).unit : AdjoinRoot (powerRootPolynomial K n A a)) ^ n =
    AdjoinRoot.of (powerRootPolynomial K n A a) a
  simpa only [IsUnit.unit_spec] using powerRoot_pow_eq K n A a

/-- The canonical map adjoining one root of a unit is faithfully flat. -/
theorem powerRootMap_faithfullyFlat (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) (hn : 0 < n) :
    faithfullyFlatTestMorphisms K (powerRootMap K n A a).op := by
  change (AdjoinRoot.of (powerRootPolynomial K n A a)).FaithfullyFlat
  rw [← AdjoinRoot.algebraMap_eq (f := powerRootPolynomial K n A a),
    RingHom.faithfullyFlat_algebraMap_iff]
  haveI := powerRootAlgebra_free K n A a hn
  by_cases h : Subsingleton (A.obj : Type u)
  · letI : Subsingleton (A.obj : Type u) := h
    apply (Module.FaithfullyFlat.iff_flat_and_proper_ideal
      (A.obj : Type u) (AdjoinRoot (powerRootPolynomial K n A a))).2
    exact ⟨inferInstance, fun I hI => (hI (Subsingleton.elim I ⊤)).elim⟩
  · haveI : Nontrivial (A.obj : Type u) := not_subsingleton_iff_nontrivial.mp h
    have hp : (powerRootPolynomial K n A a).Monic :=
      Polynomial.monic_X_pow_sub_C (a : A.obj) (Nat.ne_of_gt hn)
    have hd : 0 < (powerRootPolynomial K n A a).degree := by
      rw [powerRootPolynomial, Polynomial.degree_X_pow_sub_C hn]
      exact_mod_cast hn
    haveI : Nontrivial (AdjoinRoot (powerRootPolynomial K n A a)) :=
      (AdjoinRoot.of.injective_of_monic_of_degree_pos hp hd).nontrivial
    infer_instance

/-- The image of `a` in the one-root algebra is an `n`th power of a unit,
so the faithfully flat witness is genuinely a *single* morphism. -/
theorem powerRootMap_mem_powerImage (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) (hn : 0 < n) :
    (unitsTestPoints K).map (powerRootMap K n A a).op.op a ∈
      (powerImage K n).obj (op (op (powerRootAlgebra K n A a))) := by
  apply (mem_powerImage_iff K n (powerRootAlgebra K n A a) _).2
  exact ⟨powerRootUnit K n A a hn, powerRootUnit_pow K n A a hn⟩

/-- For every positive exponent, the power image has a single faithfully flat
witness over each test algebra, even when it is not pointwise full. This
finite-type test statement recovers the power-image example following
Milne, *Algebraic Groups*, Definition 5.6. -/
theorem powerImage_isOneCoverDense (n : ℕ) (hn : 0 < n) :
    (powerImage K n).IsOneCoverDense (faithfullyFlatTestMorphisms K) := by
  intro A a
  exact ⟨op (powerRootAlgebra K n A.unop a), (powerRootMap K n A.unop a).op,
    powerRootMap_faithfullyFlat K n A.unop a hn,
    powerRootMap_mem_powerImage K n A.unop a hn⟩

/-- The Laurent polynomial algebra is finitely generated over the base ring;
its standard presentation has one generator and an inverse. -/
theorem laurentPolynomial_finiteType :
    Algebra.FiniteType K (LaurentPolynomial K) := by
  letI : AddMonoid.FG ℤ := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  infer_instance

/-- The finitely generated Laurent-polynomial test algebra. -/
noncomputable def laurentTest : FGAlgCat.{u} K :=
  ⟨CommAlgCat.of K (LaurentPolynomial K), laurentPolynomial_finiteType K⟩

/-- The canonical Laurent monomial `T`, as a unit. -/
noncomputable def laurentUnit : (laurentTest K).objˣ :=
  (LaurentPolynomial.isUnit_T (1 : ℤ)).unit

/-- The additive affine-line functor on finitely generated algebra tests. -/
def additiveTestPoints : ((FGAlgCat.{u} K)ᵒᵖ)ᵒᵖ ⥤ Type u :=
  unopUnop (FGAlgCat.{u} K) ⋙
    ObjectProperty.ι (fun A : CommAlgCat.{u} K ↦ Algebra.FiniteType K A) ⋙
    forget (CommAlgCat.{u} K)

/-- The zero subfunctor of the additive affine-line functor. -/
def zeroAdditiveSubfunctor : Subfunctor (additiveTestPoints K) where
  obj A := {(0 : (A.unop.unop.obj : Type u))}
  map f := by
    rintro _ ⟨rfl⟩
    apply Set.mem_singleton_iff.mpr
    change f.unop.unop.hom.hom.toRingHom (0 : _) = 0
    exact map_zero _

/-- The zero additive subfunctor contains exactly the zero section. -/
@[simp]
theorem mem_zeroAdditiveSubfunctor_iff (A : ((FGAlgCat.{u} K)ᵒᵖ)ᵒᵖ)
    (x : (additiveTestPoints K).obj A) :
    x ∈ (zeroAdditiveSubfunctor K).obj A ↔ x = (0 : (A.unop.unop.obj : Type u)) := Iff.rfl

end General

variable (K : Type u) [Field K]

/-- The degree-one Laurent unit is not an `n`th power for `n ≥ 2`. -/
theorem laurentUnit_not_mem_powerImage (n : ℕ) (hn : 2 ≤ n) :
    laurentUnit K ∉ (powerImage K n).obj (op (op (laurentTest K))) := by
  intro h
  obtain ⟨b, hb⟩ := (mem_powerImage_iff K n (laurentTest K) (laurentUnit K)).1 h
  change (LaurentPolynomial K)ˣ at b
  have hpow : (b : LaurentPolynomial K) ^ n = LaurentPolynomial.T 1 := by
    have hval := congrArg Units.val hb
    change (b : LaurentPolynomial K) ^ n = (laurentUnit K).val at hval
    simpa only [laurentUnit, IsUnit.unit_spec] using hval
  obtain ⟨shift, polynomial, hshift⟩ := LaurentPolynomial.exists_T_pow (b : LaurentPolynomial K)
  have hpolynomial : Polynomial.toLaurent (polynomial ^ n) =
      LaurentPolynomial.T (n * shift + 1 : ℕ) := by
    rw [map_pow, hshift, mul_pow, hpow, LaurentPolynomial.T_pow,
      ← LaurentPolynomial.T_add]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_comm]
  have hp : polynomial ^ n = (Polynomial.X : Polynomial K) ^ (n * shift + 1) :=
    Polynomial.toLaurent_injective (by simpa [Polynomial.toLaurent_X_pow] using hpolynomial)
  have hdegree := congrArg Polynomial.natDegree hp
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_pow] at hdegree
  have hdiv : n ∣ 1 := by
    have hnshift : n ∣ n * shift := ⟨shift, rfl⟩
    have hndegree : n ∣ n * shift + 1 := ⟨polynomial.natDegree, hdegree.symm⟩
    simpa only [Nat.add_sub_cancel_left] using Nat.dvd_sub hndegree hnshift
  have hn1 : n = 1 := Nat.dvd_one.mp hdiv
  omega

private theorem subfunctor_not_isSheafFor_singleton_of_injective
    {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type*} (D : Subfunctor F)
    {X U : C} (f : U ⟶ X) (x : F.obj (op X))
    (hx : F.map f.op x ∈ D.obj (op U))
    (hf : Function.Injective (F.map f.op)) (hnot : x ∉ D.obj (op X)) :
    ¬ Presieve.IsSheafFor D.toFunctor (Presieve.singleton f) := by
  intro hsheaf
  let rootSection : D.toFunctor.obj (op U) := ⟨F.map f.op x, hx⟩
  have compatible : ∀ {Z : C} (left right : Z ⟶ U), left ≫ f = right ≫ f →
      D.toFunctor.map left.op rootSection = D.toFunctor.map right.op rootSection := by
    intro Z left right heq
    apply Subtype.ext
    dsimp only [Subfunctor.toFunctor_map, rootSection]
    change F.map left.op (F.map f.op x) = F.map right.op (F.map f.op x)
    simp only [← Functor.map_comp_apply, ← op_comp, heq]
  obtain ⟨glue, hglue, _⟩ := (Presieve.isSheafFor_singleton.mp hsheaf) rootSection compatible
  have hval : F.map f.op (glue : F.obj (op X)) = F.map f.op x := by
    have heq := congrArg Subtype.val hglue
    change F.map f.op (glue : F.obj (op X)) = F.map f.op x at heq
    exact heq
  apply hnot
  rw [← hf hval]
  exact glue.property

/-- The power-image subfunctor fails descent for its faithfully flat root
cover: the image of `T` has compatible restrictions but does not descend in
the power image itself. -/
theorem powerImage_not_isSheafFor_root (n : ℕ) (hn : 2 ≤ n) :
    ¬ Presieve.IsSheafFor ((powerImage K n).toFunctor)
      (Presieve.singleton (powerRootMap K n (laurentTest K) (laurentUnit K)).op) := by
  apply subfunctor_not_isSheafFor_singleton_of_injective
    (powerImage K n) (powerRootMap K n (laurentTest K) (laurentUnit K)).op
    (laurentUnit K)
  · exact powerRootMap_mem_powerImage K n (laurentTest K) (laurentUnit K)
      (by omega)
  · change Function.Injective
      (Units.map (powerRootMap K n (laurentTest K) (laurentUnit K)).hom.hom.toMonoidHom)
    exact Units.map_injective
      ((powerRootMap_faithfullyFlat K n (laurentTest K) (laurentUnit K)
        (by omega)).injective)
  · exact laurentUnit_not_mem_powerImage K n hn

/-- The zero additive subfunctor is not one-cover dense over a field:
the point `1` cannot become zero under a faithfully flat algebra map. -/
theorem zeroAdditiveSubfunctor_not_oneCoverDense :
    ¬ (zeroAdditiveSubfunctor K).IsOneCoverDense (faithfullyFlatTestMorphisms K) := by
  intro h
  let A : FGAlgCat.{u} K := ⟨CommAlgCat.of K K, inferInstance⟩
  let hone : (additiveTestPoints K).obj (op (op A)) := (1 : (A.obj : Type u))
  obtain ⟨U, f, hf, hmem⟩ := h (op A) hone
  have hzero : (additiveTestPoints K).map f.op hone = (0 : (U.unop.obj : Type u)) :=
    (mem_zeroAdditiveSubfunctor_iff K _ _).1 hmem
  have hmap : f.unop.hom.hom.toRingHom (1 : (A.obj : Type u)) =
      f.unop.hom.hom.toRingHom (0 : (A.obj : Type u)) := by
    change f.unop.hom.hom.toRingHom (1 : (A.obj : Type u)) = 0 at hzero
    simpa only [map_zero] using hzero
  have hneq : (1 : (A.obj : Type u)) ≠ 0 := by
    change (1 : K) ≠ 0
    exact one_ne_zero
  exact hneq ((hf : f.unop.hom.hom.toRingHom.FaithfullyFlat).injective hmap)

end AlgebraicGeometry
