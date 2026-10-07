/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.SingleCoverGroup
public import SchemeProperties.SingleCoverTransport
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Products.Unitor
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.Fintype.Order
public import Mathlib.Data.ZMod.Basic

/-!
# A proper dense group-valued subfunctor

The two-object ordered category `Bool` has a morphism `false ⟶ true`. In the
constant presheaf with two-element group carrier, take the full group at
`false` and the unit subgroup at `true`. Restriction along the nonidentity
arrow makes this proper subfunctor one-cover dense for all morphisms. The
target satisfies singleton descent and the subfunctor has a group law before
applying the extension theorem.

This elementary example checks the categorical group-extension hypotheses.
It does not identify a group law on a represented multiplicative-group scheme.
-/

@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory
open scoped CategoryTheory.Prod

namespace CategoryTheory.Subfunctor

/-- The two-element group used by the constant target presheaf. -/
abbrev twoGroup := Multiplicative (ZMod 2)

/-- The constant two-element-group presheaf on the ordered category `Bool`. -/
abbrev twoPoints : Boolᵒᵖ ⥤ Type := (Functor.const Boolᵒᵖ).obj twoGroup

private instance (X : Boolᵒᵖ) : Group (twoPoints.obj X) := by
  simpa only [twoPoints, Functor.const_obj_obj] using (inferInstance : Group twoGroup)

private def unitAtTop : Subfunctor twoPoints where
  obj X := if X.unop then {1} else Set.univ
  map := by
    intro X Y f x hx
    cases X with | op X =>
      cases Y with | op Y =>
        have hf : Y ≤ X := leOfHom f.unop
        cases X <;> cases Y
        · simp
        · exact ((by decide : ¬ (true ≤ false)) hf).elim
        · simp
        · exact hx

private theorem unitAtTop_one (X : Boolᵒᵖ) :
    (1 : twoGroup) ∈ unitAtTop.obj X := by
  cases X with | op X =>
    cases X <;> simp [unitAtTop]

private theorem unitAtTop_mul (X : Boolᵒᵖ)
    (a b : unitAtTop.toFunctor.obj X) :
    a.1 * b.1 ∈ unitAtTop.obj X := by
  cases X with | op X =>
    cases X
    · simp [unitAtTop]
    · have ha : a.1 = 1 := by simpa [unitAtTop] using a.2
      have hb : b.1 = 1 := by simpa [unitAtTop] using b.2
      simp [unitAtTop, ha, hb]

private theorem unitAtTop_inv (X : Boolᵒᵖ)
    (a : unitAtTop.toFunctor.obj X) :
    a.1⁻¹ ∈ unitAtTop.obj X := by
  cases X with | op X =>
    cases X
    · simp [unitAtTop]
    · have ha : a.1 = 1 := by simpa [unitAtTop] using a.2
      simp [unitAtTop, ha]

private noncomputable instance : GrpObj unitAtTop.toFunctor where
  one := {
    app X := ↾fun _ => ⟨1, unitAtTop_one X⟩
    naturality X Y f := by
      ext x
      apply Subtype.ext
      rfl }
  mul := {
    app X := ↾fun pair => ⟨pair.1.1 * pair.2.1, unitAtTop_mul X pair.1 pair.2⟩
    naturality X Y f := by
      ext x
      apply Subtype.ext
      rfl }
  inv := {
    app X := ↾fun a => ⟨a.1⁻¹, unitAtTop_inv X a⟩
    naturality X Y f := by
      ext x
      apply Subtype.ext
      rfl }
  one_mul := by
    ext X x
    apply Subtype.ext
    simp only [NatTrans.comp_app, Monoidal.whiskerRight_app, Monoidal.leftUnitor_hom_app]
    exact one_mul _
  mul_one := by
    ext X x
    apply Subtype.ext
    simp only [NatTrans.comp_app, Monoidal.whiskerLeft_app, Monoidal.rightUnitor_hom_app]
    exact mul_one _
  mul_assoc := by
    ext X x
    apply Subtype.ext
    change (x.1.1.1 * x.1.2.1) * x.2.1 = x.1.1.1 * (x.1.2.1 * x.2.1)
    exact mul_assoc _ _ _
  left_inv := by
    ext X x
    apply Subtype.ext
    change x.1⁻¹ * x.1 = 1
    exact inv_mul_cancel _
  right_inv := by
    ext X x
    apply Subtype.ext
    change x.1 * x.1⁻¹ = 1
    exact mul_inv_cancel _

private instance : HasPullbacks Bool := by
  constructor
  intro diagram
  exact (Preorder.hasLimit_iff_hasGLB diagram).2
    ⟨sInf (Set.range diagram.obj), isGLB_sInf _⟩

private theorem unitAtTop_dense :
    unitAtTop.IsOneCoverDense (⊤ : MorphismProperty Bool) := by
  intro X x
  refine ⟨false, homOfLE (by cases X <;> decide), by simp, ?_⟩
  simp [unitAtTop]

private theorem twoPoints_descent {X U : Bool} (f : U ⟶ X) :
    Presieve.IsSheafFor twoPoints (Presieve.singleton f) := by
  rw [Presieve.isSheafFor_singleton]
  intro x _
  refine ⟨x, by simp, ?_⟩
  intro y hy
  simpa using hy

private theorem twoPoints_descentTop :
    ∀ {X U : Bool} (f : U ⟶ X),
      (⊤ : MorphismProperty Bool) f →
        Presieve.IsSheafFor twoPoints (Presieve.singleton f) := by
  intro X U f _
  exact twoPoints_descent f

private theorem unitAtTop_proper : unitAtTop ≠ ⊤ := by
  intro h
  have hx : (Multiplicative.ofAdd (1 : ZMod 2)) ∈ unitAtTop.obj (op true) := by
    rw [h]
    trivial
  have hx' : (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
    simp [unitAtTop] at hx
  have heq : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd hx'
  exact (by decide : (1 : ZMod 2) ≠ 0) heq

@[instance_reducible]
private noncomputable def pointwiseGroup : GrpObj twoPoints where
  one := { app _ := ↾fun _ => 1, naturality _ _ _ := rfl }
  mul := { app _ := ↾fun pair => pair.1 * pair.2, naturality _ _ _ := rfl }
  inv := { app _ := ↾fun point => point⁻¹, naturality _ _ _ := rfl }
  one_mul := by
    ext X x
    simp only [NatTrans.comp_app, Monoidal.whiskerRight_app, Monoidal.leftUnitor_hom_app]
    exact one_mul _
  mul_one := by
    ext X x
    simp only [NatTrans.comp_app, Monoidal.whiskerLeft_app, Monoidal.rightUnitor_hom_app]
    exact mul_one _
  mul_assoc := by
    ext X x
    change (x.1.1 * x.1.2) * x.2 = x.1.1 * (x.1.2 * x.2)
    exact mul_assoc _ _ _
  left_inv := by
    ext X x
    change x⁻¹ * x = 1
    exact inv_mul_cancel _
  right_inv := by
    ext X x
    change x * x⁻¹ = 1
    exact mul_inv_cancel _

private noncomputable instance : GrpObj twoPoints := pointwiseGroup

private theorem unitAtTop_inclusion_isMonHom :
    @IsMonHom (Boolᵒᵖ ⥤ Type) _ _ unitAtTop.toFunctor twoPoints
      (inferInstance : MonObj unitAtTop.toFunctor) pointwiseGroup.toMonObj unitAtTop.ι := by
  constructor
  · ext X point
    rfl
  · ext X pair
    rfl

/-- The proper dense subfunctor recovers the independently specified pointwise law. -/
example : unitAtTop ≠ ⊤ ∧
    unitAtTop.IsOneCoverDense (⊤ : MorphismProperty Bool) ∧
    (∀ {X U : Bool} (f : U ⟶ X),
      (⊤ : MorphismProperty Bool) f →
        Presieve.IsSheafFor twoPoints (Presieve.singleton f)) ∧
    pointwiseGroup = unitAtTop_dense.grpObj twoPoints_descentTop := by
  exact ⟨unitAtTop_proper, unitAtTop_dense, twoPoints_descentTop,
    unitAtTop_dense.grpObj_unique twoPoints_descentTop pointwiseGroup
      unitAtTop_inclusion_isMonHom⟩

private noncomputable instance : GrpObj (⊤ : Subfunctor twoPoints).toFunctor :=
  GrpObj.ofIso (asIso (⊤ : Subfunctor twoPoints).ι).symm

private theorem full_inclusion_isMonHom :
    @IsMonHom (Boolᵒᵖ ⥤ Type) _ _
      (⊤ : Subfunctor twoPoints).toFunctor twoPoints
      (inferInstance : MonObj (⊤ : Subfunctor twoPoints).toFunctor)
      pointwiseGroup.toMonObj (⊤ : Subfunctor twoPoints).ι := by
  let e := (asIso (⊤ : Subfunctor twoPoints).ι).symm
  have : IsMonHom e.hom := by
    let : MonObj (⊤ : Subfunctor twoPoints).toFunctor := MonObj.ofIso e
    exact isMonHom_ofIso e
  exact (inferInstance : IsMonHom e.inv)

/-- The full subfunctor also recovers the independently specified pointwise law. -/
example : (⊤ : Subfunctor twoPoints).IsOneCoverDense
      (⊤ : MorphismProperty Bool) ∧
    pointwiseGroup =
      (isOneCoverDense_top (F := twoPoints) (⊤ : MorphismProperty Bool)).grpObj
        twoPoints_descentTop := by
  have hfull := isOneCoverDense_top (F := twoPoints) (⊤ : MorphismProperty Bool)
  exact ⟨hfull, hfull.grpObj_unique twoPoints_descentTop pointwiseGroup
    full_inclusion_isMonHom⟩

private def nonunitSection : unitAtTop.toFunctor.obj (op false) :=
  ⟨Multiplicative.ofAdd (1 : ZMod 2), by
    change _ ∈ Set.univ
    exact Set.mem_univ _⟩

private theorem nonunitSection_ne_one : nonunitSection.1 ≠ (1 : twoGroup) := by
  intro h
  exact (by decide : (1 : ZMod 2) ≠ 0) (congrArg Multiplicative.toAdd h)

/-- At the lower object the proper subfunctor has a nonunit section, whose
square, inverse and unit agree with the extended operations. -/
example : nonunitSection.1 ≠ (1 : twoGroup) ∧
    ((unitAtTop_dense.grpObj twoPoints_descentTop).toMonObj.mul).app (op false)
      ((unitAtTop.ι ⊗ₘ unitAtTop.ι).app (op false)
        (nonunitSection, nonunitSection)) = (1 : twoGroup) ∧
    (unitAtTop_dense.grpObj twoPoints_descentTop).inv.app (op false)
      (unitAtTop.ι.app (op false) nonunitSection) = nonunitSection.1 ∧
    ((unitAtTop_dense.grpObj twoPoints_descentTop).toMonObj.one).app (op false)
      (PUnit.unit : (𝟙_ (Boolᵒᵖ ⥤ Type)).obj (op false)) = (1 : twoGroup) := by
  refine ⟨nonunitSection_ne_one, ?_, ?_, ?_⟩
  · rw [unitAtTop_dense.grpObj_mul_ι_app]
    change (Multiplicative.ofAdd (1 : ZMod 2) : twoGroup) *
      Multiplicative.ofAdd (1 : ZMod 2) = 1
    decide
  · rw [unitAtTop_dense.grpObj_inv_ι_app]
    change (Multiplicative.ofAdd (1 : ZMod 2) : twoGroup)⁻¹ =
      Multiplicative.ofAdd (1 : ZMod 2)
    decide
  · rw [unitAtTop_dense.grpObj_one_ι_app]
    rfl

private noncomputable def nonunitDiagonal :
    (unitAtTop.toFunctor ⨯ unitAtTop.toFunctor).obj (op false) :=
  (prod.lift (𝟙 unitAtTop.toFunctor) (𝟙 unitAtTop.toFunctor)).app
    (op false) nonunitSection

/-- Both projections of the carrier comparison recover a nonunit section. -/
example : ((productIso unitAtTop unitAtTop).hom ≫ prod.fst).app (op false)
      ((productPair unitAtTop unitAtTop).app (op false)
        nonunitDiagonal) = nonunitSection ∧
    ((productIso unitAtTop unitAtTop).hom ≫ prod.snd).app (op false)
      ((productPair unitAtTop unitAtTop).app (op false)
        nonunitDiagonal) = nonunitSection := by
  constructor
  · rw [productIso_hom_fst]
    change (productPair unitAtTop unitAtTop ≫
      productFst unitAtTop unitAtTop).app (op false)
        nonunitDiagonal = _
    rw [← productIso_hom_fst]
    have hpair : productPair unitAtTop unitAtTop ≫
        (productIso unitAtTop unitAtTop).hom =
          𝟙 (unitAtTop.toFunctor ⨯ unitAtTop.toFunctor) :=
      (productIso unitAtTop unitAtTop).inv_hom_id
    rw [← Category.assoc, hpair, Category.id_comp]
    change (prod.lift (𝟙 unitAtTop.toFunctor) (𝟙 unitAtTop.toFunctor) ≫
      prod.fst).app (op false) nonunitSection = nonunitSection
    rw [prod.lift_fst]
    rfl
  · rw [productIso_hom_snd]
    change (productPair unitAtTop unitAtTop ≫
      productSnd unitAtTop unitAtTop).app (op false)
        nonunitDiagonal = _
    rw [← productIso_hom_snd]
    have hpair : productPair unitAtTop unitAtTop ≫
        (productIso unitAtTop unitAtTop).hom =
          𝟙 (unitAtTop.toFunctor ⨯ unitAtTop.toFunctor) :=
      (productIso unitAtTop unitAtTop).inv_hom_id
    rw [← Category.assoc, hpair, Category.id_comp]
    change (prod.lift (𝟙 unitAtTop.toFunctor) (𝟙 unitAtTop.toFunctor) ≫
      prod.snd).app (op false) nonunitSection = nonunitSection
    rw [prod.lift_snd]
    rfl

/-- Comparing the paired subfunctor sections and including them gives
the prescribed pointwise coordinates in the ambient product. -/
example : ((prod.fst : twoPoints ⨯ twoPoints ⟶ twoPoints).app (op false)
      (((productIso unitAtTop unitAtTop).hom ≫
        prod.map unitAtTop.ι unitAtTop.ι).app (op false)
          ((productPair unitAtTop unitAtTop).app (op false) nonunitDiagonal))) =
      nonunitSection.1 ∧
    ((prod.snd : twoPoints ⨯ twoPoints ⟶ twoPoints).app (op false)
      (((productIso unitAtTop unitAtTop).hom ≫
        prod.map unitAtTop.ι unitAtTop.ι).app (op false)
          ((productPair unitAtTop unitAtTop).app (op false) nonunitDiagonal))) =
      nonunitSection.1 := by
  constructor
  · rw [productIso_hom_comp_map_ι]
    change ((productPair unitAtTop unitAtTop ≫
      (unitAtTop.product unitAtTop).ι ≫ prod.fst).app (op false)
        nonunitDiagonal) = _
    rw [← Category.assoc, productPair_comp_ι, prod.map_fst]
    change ((prod.lift (𝟙 unitAtTop.toFunctor) (𝟙 unitAtTop.toFunctor) ≫
      prod.fst).app (op false) nonunitSection).1 = nonunitSection.1
    rw [prod.lift_fst]
    rfl
  · rw [productIso_hom_comp_map_ι]
    change ((productPair unitAtTop unitAtTop ≫
      (unitAtTop.product unitAtTop).ι ≫ prod.snd).app (op false)
        nonunitDiagonal) = _
    rw [← Category.assoc, productPair_comp_ι, prod.map_snd]
    change ((prod.lift (𝟙 unitAtTop.toFunctor) (𝟙 unitAtTop.toFunctor) ≫
      prod.snd).app (op false) nonunitSection).1 = nonunitSection.1
    rw [prod.lift_snd]
    rfl

/-- The empty subfunctor is not one-cover dense, even though the target descends. -/
example : ¬ (⊥ : Subfunctor twoPoints).IsOneCoverDense
    (⊤ : MorphismProperty Bool) := by
  intro h
  obtain ⟨U, f, _, hx⟩ := h false (1 : twoGroup)
  simp at hx

private theorem unitAtTop_productUnit_proper :
    unitAtTop.precomp (prod.rightUnitorEquivalence Bool).functor.op ≠ ⊤ := by
  intro h
  have hx : (Multiplicative.ofAdd (1 : ZMod 2)) ∈
      (unitAtTop.precomp (prod.rightUnitorEquivalence Bool).functor.op).obj
        (op ⟨true, ⟨PUnit.unit⟩⟩) := by
    rw [h]
    trivial
  change (Multiplicative.ofAdd (1 : ZMod 2)) = (1 : twoGroup) at hx
  have heq : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd hx
  exact (by decide : (1 : ZMod 2) ≠ 0) heq

/-- A change from product-with-terminal tests to ordered `Bool` tests retains a
proper dense subfunctor. The original density and properness are established
independently of the transport statement. -/
example :
    (unitAtTop.precomp (prod.rightUnitorEquivalence Bool).functor.op).IsOneCoverDense
      ((⊤ : MorphismProperty Bool).inverseImage
        (prod.rightUnitorEquivalence Bool).functor) ∧
    unitAtTop.precomp (prod.rightUnitorEquivalence Bool).functor.op ≠ ⊤ := by
  exact ⟨(isOneCoverDense_equivalence_iff unitAtTop (⊤ : MorphismProperty Bool)
    (prod.rightUnitorEquivalence Bool)).2 unitAtTop_dense, unitAtTop_productUnit_proper⟩

/-- Even after changing the test category, the empty subfunctor misses the
nonempty section at `false` and cannot be one-cover dense. -/
example :
    ¬ ((⊥ : Subfunctor twoPoints).precomp
      (prod.rightUnitorEquivalence Bool).functor.op).IsOneCoverDense
      ((⊤ : MorphismProperty Bool).inverseImage
        (prod.rightUnitorEquivalence Bool).functor) := by
  intro h
  obtain ⟨U, f, _, hx⟩ := h ⟨false, ⟨PUnit.unit⟩⟩ (1 : twoGroup)
  simp [precomp_obj] at hx

private def discreteBoolTests : Discrete Bool ⥤ Bool := Discrete.functor id

/-- Essential surjectivity alone cannot replace fullness: the discrete tests
have the same objects as `Bool` but cannot lift the nonidentity covering arrow
from `false` to `true`. -/
example :
    discreteBoolTests.EssSurj ∧ ¬ discreteBoolTests.Full ∧
    unitAtTop.IsOneCoverDense (⊤ : MorphismProperty Bool) ∧
    ¬ (unitAtTop.precomp discreteBoolTests.op).IsOneCoverDense
      ((⊤ : MorphismProperty Bool).inverseImage discreteBoolTests) := by
  refine ⟨Functor.essSurj_of_surj (fun X => ⟨⟨X⟩, rfl⟩), ?_,
    unitAtTop_dense, ?_⟩
  · intro hFull
    have f : (⟨false⟩ : Discrete Bool) ⟶ ⟨true⟩ :=
      (hFull.map_surjective (homOfLE (by decide : false ≤ true))).choose
    cases f.eq
  · intro h
    obtain ⟨U, f, _, hx⟩ := h ⟨true⟩ (Multiplicative.ofAdd (1 : ZMod 2))
    have hu : U.as = true := f.eq
    cases U with
    | mk value =>
      cases hu
      change (Multiplicative.ofAdd (1 : ZMod 2)) = (1 : twoGroup) at hx
      have heq : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd hx
      exact (by decide : (1 : ZMod 2) ≠ 0) heq

private def loopTests : Bool × SingleObj twoGroup ⥤ Bool :=
  CategoryTheory.Prod.fst Bool (SingleObj twoGroup)

private instance : loopTests.Full where
  map_surjective := by
    intro X Y morphism
    exact ⟨morphism ×ₘ (1 : twoGroup), rfl⟩

private instance : loopTests.EssSurj :=
  Functor.essSurj_of_surj fun X => ⟨(X, SingleObj.star twoGroup), rfl⟩

private theorem loopTests_not_faithful : ¬ loopTests.Faithful := by
  intro hFaithful
  let X : Bool × SingleObj twoGroup := (false, SingleObj.star twoGroup)
  have h : ((𝟙 false) ×ₘ (1 : twoGroup) : X ⟶ X) =
      ((𝟙 false) ×ₘ Multiplicative.ofAdd (1 : ZMod 2) : X ⟶ X) :=
    hFaithful.map_injective (by rfl)
  have hgroup : (1 : twoGroup) = Multiplicative.ofAdd (1 : ZMod 2) :=
    congrArg (fun (morphism : X ⟶ X) => morphism.2) h
  have heq : (0 : ZMod 2) = 1 := congrArg Multiplicative.toAdd hgroup
  exact (by decide : (0 : ZMod 2) ≠ 1) heq

/-- The projection forgetting nontrivial automorphisms is full and essentially
surjective but not faithful. It transports the existing proper dense subfunctor
because single-arrow density does not require lifting arrows uniquely. -/
example :
    loopTests.Full ∧ loopTests.EssSurj ∧ ¬ loopTests.Faithful ∧
    (unitAtTop.precomp loopTests.op).IsOneCoverDense
      ((⊤ : MorphismProperty Bool).inverseImage loopTests) ∧
    unitAtTop.precomp loopTests.op ≠ ⊤ := by
  refine ⟨inferInstance, inferInstance, loopTests_not_faithful,
    (isOneCoverDense_precomp_iff unitAtTop (⊤ : MorphismProperty Bool) loopTests).2
      unitAtTop_dense, ?_⟩
  intro h
  have hx : (Multiplicative.ofAdd (1 : ZMod 2)) ∈
      (unitAtTop.precomp loopTests.op).obj
        (op (true, SingleObj.star twoGroup)) := by
    rw [h]
    trivial
  change (Multiplicative.ofAdd (1 : ZMod 2)) = (1 : twoGroup) at hx
  have heq : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd hx
  exact (by decide : (1 : ZMod 2) ≠ 0) heq

end CategoryTheory.Subfunctor
