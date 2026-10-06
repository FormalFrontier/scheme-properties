/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.PowerImage

/-!
# Isomorphisms extending from single-cover dense subfunctors

The constant Boolean presheaf carries a nonidentity involution of its full
subfunctor. Its extension is still nonidentity. The square-power image gives
a separate proper one-cover dense subfunctor which need not satisfy descent.
The finite-type specialization is evaluated on an explicit affine spectrum
over the rational numbers.
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry

private def rationalTest : FGAlgCat.{0} ℚ :=
  ⟨CommAlgCat.of ℚ ℚ, inferInstance⟩

private noncomputable def rationalSpec : algebraicOver ℚ :=
  ⟨(finiteAlgSpecOver ℚ).obj (op rationalTest), by
    change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ)))
    simpa only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id] using
      (inferInstance : QuasiCompact (𝟙 (Spec (CommRingCat.of ℚ))))⟩

private noncomputable def fullRationalSpecPoints :
    Subfunctor ((algebraicOverPoints ℚ).obj rationalSpec) := ⊤

private theorem fullRationalSpecPoints_dense :
    fullRationalSpecPoints.IsOneCoverDense (faithfullyFlatTestMorphisms ℚ) := by
  letI := faithfullyFlatTestMorphisms_containsIdentities ℚ
  exact Subfunctor.isOneCoverDense_top (faithfullyFlatTestMorphisms ℚ)

example : (powerImage ℚ 2).IsOneCoverDense (faithfullyFlatTestMorphisms ℚ) ∧
    laurentUnit ℚ ∉ (powerImage ℚ 2).obj (op (op (laurentTest ℚ))) :=
  ⟨powerImage_isOneCoverDense ℚ 2 (by decide),
    laurentUnit_not_mem_powerImage ℚ 2 (by decide)⟩

end AlgebraicGeometry

namespace CategoryTheory.Subfunctor

private abbrev boolPoints : (((FGAlgCat.{0} ℚ)ᵒᵖ)ᵒᵖ) ⥤ Type :=
  (Functor.const ((FGAlgCat.{0} ℚ)ᵒᵖ)ᵒᵖ).obj Bool

private abbrev fullBool : Subfunctor boolPoints := ⊤

private noncomputable def boolSwap : fullBool.toFunctor ⟶ fullBool.toFunctor where
  app _ := ↾fun b ↦ ⟨!b.1, Set.mem_univ _⟩
  naturality _ _ _ := by
    ext b
    rfl

private noncomputable def boolSwapIso : fullBool.toFunctor ≅ fullBool.toFunctor where
  hom := boolSwap
  inv := boolSwap
  hom_inv_id := by
    ext X b
    apply Subtype.ext
    change (!(!b.1)) = b.1
    cases b.1 <;> rfl
  inv_hom_id := by
    ext X b
    apply Subtype.ext
    change (!(!b.1)) = b.1
    cases b.1 <;> rfl

private theorem boolPoints_isSheafFor {X U : (FGAlgCat.{0} ℚ)ᵒᵖ} (f : U ⟶ X) :
    Presieve.IsSheafFor boolPoints (Presieve.singleton f) := by
  rw [Presieve.isSheafFor_singleton]
  intro x _
  refine ⟨x, by simp, ?_⟩
  intro y hy
  simpa using hy

private theorem fullBool_isOneCoverDense :
    fullBool.IsOneCoverDense (AlgebraicGeometry.faithfullyFlatTestMorphisms ℚ) := by
  letI := AlgebraicGeometry.faithfullyFlatTestMorphisms_containsIdentities ℚ
  exact isOneCoverDense_top (AlgebraicGeometry.faithfullyFlatTestMorphisms ℚ)

private abbrev emptyPoints : (((FGAlgCat.{0} ℚ)ᵒᵖ)ᵒᵖ) ⥤ Type :=
  (Functor.const ((FGAlgCat.{0} ℚ)ᵒᵖ)ᵒᵖ).obj Empty

private abbrev emptyBoolSubfunctor : Subfunctor boolPoints := ⊥

private abbrev emptyEmptySubfunctor : Subfunctor emptyPoints := ⊥

private noncomputable def emptySubfunctorsIso :
    emptyBoolSubfunctor.toFunctor ≅ emptyEmptySubfunctor.toFunctor where
  hom := {
    app := fun _ ↦ ↾fun b ↦ (show False from b.property).elim
    naturality := by
      intro X Y f
      ext b
      exact (show False from b.property).elim }
  inv := {
    app := fun _ ↦ ↾fun b ↦ b.1.elim
    naturality := by
      intro X Y f
      ext b
      exact b.1.elim }
  hom_inv_id := by
    ext X b
    exact (show False from b.property).elim
  inv_hom_id := by
    ext X b
    exact b.1.elim

private theorem emptyPoints_isSheafFor {X U : (FGAlgCat.{0} ℚ)ᵒᵖ} (f : U ⟶ X) :
    Presieve.IsSheafFor emptyPoints (Presieve.singleton f) := by
  rw [Presieve.isSheafFor_singleton]
  intro x _
  exact x.elim

example :
    emptyEmptySubfunctor.IsOneCoverDense
      (AlgebraicGeometry.faithfullyFlatTestMorphisms ℚ) ∧
    (∀ {X U : (FGAlgCat.{0} ℚ)ᵒᵖ} (f : U ⟶ X),
      AlgebraicGeometry.faithfullyFlatTestMorphisms ℚ f →
        Presieve.IsSheafFor emptyPoints (Presieve.singleton f)) ∧
    ¬ emptyBoolSubfunctor.IsOneCoverDense
      (AlgebraicGeometry.faithfullyFlatTestMorphisms ℚ) ∧
    Nonempty (emptyBoolSubfunctor.toFunctor ≅ emptyEmptySubfunctor.toFunctor) ∧
    ¬ Nonempty (boolPoints ≅ emptyPoints) := by
  refine ⟨?_, (fun f _ ↦ emptyPoints_isSheafFor f), ?_, ⟨emptySubfunctorsIso⟩, ?_⟩
  · intro X x
    exact x.elim
  · intro h
    obtain ⟨U, f, hf, hx⟩ := h (op AlgebraicGeometry.rationalTest) true
    exact (show False from hx).elim
  · rintro ⟨i⟩
    exact (i.hom.app (op (op AlgebraicGeometry.rationalTest)) true).elim

example : boolSwapIso ≠ Iso.refl _ := by
  intro h
  have ht := congrArg (fun i : fullBool.toFunctor ≅ fullBool.toFunctor ↦
    (i.hom.app (op (op AlgebraicGeometry.rationalTest)) ⟨true, Set.mem_univ _⟩).1) h
  cases ht

private noncomputable def boolAmbientIso : boolPoints ≅ boolPoints := by
  letI := AlgebraicGeometry.hasPullbacks_finiteTypeAffineTests ℚ
  letI := AlgebraicGeometry.faithfullyFlatTestMorphisms_isStableUnderBaseChange ℚ
  exact extendOneCoverIso fullBool_isOneCoverDense fullBool_isOneCoverDense
    (fun f _ ↦ boolPoints_isSheafFor f)
    (fun f _ ↦ boolPoints_isSheafFor f) boolSwapIso

example :
    (boolAmbientIso.hom.app (op (op AlgebraicGeometry.rationalTest))) true = false := by
  letI := AlgebraicGeometry.hasPullbacks_finiteTypeAffineTests ℚ
  letI := AlgebraicGeometry.faithfullyFlatTestMorphisms_isStableUnderBaseChange ℚ
  have h := congrArg (fun φ ↦ φ.app (op (op AlgebraicGeometry.rationalTest))
    ⟨true, Set.mem_univ _⟩)
    (ι_comp_extendOneCoverIso_hom fullBool_isOneCoverDense fullBool_isOneCoverDense
      (fun f _ ↦ boolPoints_isSheafFor f)
      (fun f _ ↦ boolPoints_isSheafFor f) boolSwapIso)
  change (boolAmbientIso.hom.app (op (op AlgebraicGeometry.rationalTest))) true = false at h
  exact h

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry

example :
    extendAlgebraicOverIso ℚ rationalSpec rationalSpec
      fullRationalSpecPoints fullRationalSpecPoints
      fullRationalSpecPoints_dense fullRationalSpecPoints_dense (Iso.refl _) =
        Iso.refl rationalSpec := by
  symm
  apply extendAlgebraicOverIso_unique ℚ rationalSpec rationalSpec
    fullRationalSpecPoints fullRationalSpecPoints
    fullRationalSpecPoints_dense fullRationalSpecPoints_dense (Iso.refl _)
  simp

end AlgebraicGeometry
