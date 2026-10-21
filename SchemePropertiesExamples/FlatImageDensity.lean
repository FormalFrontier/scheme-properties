/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.FlatImageDensity
public import SchemeProperties.PowerImage
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# A nontrivial faithfully flat image

Adjoining a square root of the Laurent unit gives a finite free, faithfully flat
map of affine schemes. The identity point of the Laurent test has no lift
before base change, since it would give a square root of the Laurent unit.
After the root extension, the identity point does lift along this same map.
The map is therefore not surjective on Laurent-test points and is not an
isomorphism, although it is topologically surjective. The two density examples
apply the stated one-cover theorems; the non-lifting and explicit root-cover
triangle are verified separately.

## References

- J. S. Milne, *Algebraic Groups* (2017), Proposition 5.7 and the power-image
  example following Definition 5.6.
- `SchemeProperties.PowerImage` for the explicit root algebra and Laurent boundary.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

private noncomputable def affineFiniteTypeScheme (K : Type u) [Field K]
    (A : FGAlgCat K) : algebraicOver K :=
  ⟨(finiteAlgSpecOver K).obj (op A), by
    rw [finiteAlgSpecOver_obj_hom]
    have hcompact : QuasiCompact (Spec.map
        (CommRingCat.ofHom (algebraMap K A.obj))) := by
      exact (quasiCompact_iff_compactSpace _).mpr (by infer_instance)
    exact hcompact⟩

private noncomputable def affineRootSchemeMap :
    affineFiniteTypeScheme ℚ (powerRootAlgebra ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)) ⟶
      affineFiniteTypeScheme ℚ (laurentTest ℚ) :=
  ObjectProperty.homMk ((finiteAlgSpecOver ℚ).map
    (powerRootMap ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)).op)

private noncomputable def laurentSquareRootRingMap :
    CommRingCat.of ((laurentTest ℚ).obj : Type) ⟶
      CommRingCat.of ((powerRootAlgebra ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)).obj : Type) :=
  CommRingCat.ofHom
    (powerRootMap ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)).hom.hom.toRingHom

private theorem laurentSquareRootRingMap_eq_ofHom :
    laurentSquareRootRingMap = CommRingCat.ofHom
      (powerRootMap ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)).hom.hom.toRingHom := rfl

private theorem laurentSquareRootRingMap_finitePresentation :
    laurentSquareRootRingMap.hom.FinitePresentation := by
  change (AdjoinRoot.of (powerRootPolynomial ℚ 2 (laurentTest ℚ)
    (laurentUnit ℚ))).FinitePresentation
  rw [← AdjoinRoot.algebraMap_eq]
  exact (RingHom.finitePresentation_algebraMap).2 (by infer_instance)

/-- The map adjoining a square root of the Laurent unit has no section.
A section would give a square root in the Laurent test, contradicting the power-image
example after Definition 5.6 in Milne's *Algebraic Groups*. -/
theorem laurentSquareRoot_no_section :
    ¬ ∃ candidateLift : Spec (CommRingCat.of ((laurentTest ℚ).obj : Type)) ⟶
        Spec (CommRingCat.of ((powerRootAlgebra ℚ 2 (laurentTest ℚ)
          (laurentUnit ℚ)).obj : Type)),
      candidateLift ≫ Spec.map (CommRingCat.ofHom
        (powerRootMap ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)).hom.hom.toRingHom) = 𝟙 _ := by
  rintro ⟨candidateLift, htriangle⟩
  have hsection : laurentSquareRootRingMap ≫ Spec.preimage candidateLift = 𝟙 _ := by
    apply Spec.map_injective
    simpa only [← laurentSquareRootRingMap_eq_ofHom,
      Spec.map_comp, Spec.map_preimage, Spec.map_id] using htriangle
  let root := powerRootUnit ℚ 2 (laurentTest ℚ) (laurentUnit ℚ) (by decide)
  let originalRoot := Units.map (Spec.preimage candidateLift).hom.toMonoidHom root
  have hroot : (root : (powerRootAlgebra ℚ 2 (laurentTest ℚ)
      (laurentUnit ℚ)).obj) ^ 2 =
      laurentSquareRootRingMap.hom (laurentUnit ℚ) := by
    exact congrArg Units.val
      (powerRootUnit_pow ℚ 2 (laurentTest ℚ) (laurentUnit ℚ) (by decide))
  have hsquare : originalRoot ^ 2 = laurentUnit ℚ := by
    apply Units.ext
    change ((Spec.preimage candidateLift).hom (root : _)) ^ 2 = (laurentUnit ℚ).val
    rw [← map_pow, hroot]
    have := congrArg (fun endomorphism : CommRingCat.of ((laurentTest ℚ).obj : Type) ⟶
        CommRingCat.of ((laurentTest ℚ).obj : Type) ↦
          endomorphism.hom (laurentUnit ℚ).val)
      hsection
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_id, RingHom.id_apply] using this
  exact (laurentUnit_not_mem_powerImage ℚ 2 (by decide))
    ((mem_powerImage_iff ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)).2
      ⟨originalRoot, hsquare⟩)

example :
    ∃ (coverAlgebra : CommRingCat)
        (coverMap : CommRingCat.of ((laurentTest ℚ).obj : Type) ⟶ coverAlgebra)
        (lift : Spec coverAlgebra ⟶ Spec (CommRingCat.of
          ((powerRootAlgebra ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)).obj : Type))),
      coverMap.hom.FaithfullyFlat ∧ coverMap.hom.FinitePresentation ∧
        Spec.map coverMap ≫ (𝟙 (Spec (CommRingCat.of ((laurentTest ℚ).obj : Type)))) =
          lift ≫ Spec.map laurentSquareRootRingMap := by
  have hff : laurentSquareRootRingMap.hom.FaithfullyFlat :=
    powerRootMap_faithfullyFlat ℚ 2 (laurentTest ℚ) (laurentUnit ℚ) (by decide)
  have hgeom : Flat (Spec.map laurentSquareRootRingMap) ∧
      Surjective (Spec.map laurentSquareRootRingMap) :=
    (flat_and_surjective_SpecMap_iff _).mpr hff
  let : Flat (Spec.map laurentSquareRootRingMap) := hgeom.1
  let : Surjective (Spec.map laurentSquareRootRingMap) := hgeom.2
  let : LocallyOfFinitePresentation (Spec.map laurentSquareRootRingMap) :=
    (LocallyOfFinitePresentation.SpecMap_iff _).2
      laurentSquareRootRingMap_finitePresentation
  exact exists_affine_lift_of_flat_surjective_lfp
    (Spec.map laurentSquareRootRingMap) _ (𝟙 _)

example :
    (¬ ∃ candidateLift : Spec (CommRingCat.of ((laurentTest ℚ).obj : Type)) ⟶
        Spec (CommRingCat.of ((powerRootAlgebra ℚ 2 (laurentTest ℚ)
          (laurentUnit ℚ)).obj : Type)),
      candidateLift ≫ Spec.map laurentSquareRootRingMap = 𝟙 _) ∧
    laurentSquareRootRingMap.hom.FaithfullyFlat ∧
    laurentSquareRootRingMap.hom.FinitePresentation ∧
    Spec.map laurentSquareRootRingMap ≫
        (𝟙 (Spec (CommRingCat.of ((laurentTest ℚ).obj : Type)))) =
      (𝟙 (Spec (CommRingCat.of ((powerRootAlgebra ℚ 2 (laurentTest ℚ)
        (laurentUnit ℚ)).obj : Type)))) ≫ Spec.map laurentSquareRootRingMap := by
  refine ⟨laurentSquareRoot_no_section, ?_, laurentSquareRootRingMap_finitePresentation, ?_⟩
  · exact powerRootMap_faithfullyFlat ℚ 2 (laurentTest ℚ) (laurentUnit ℚ) (by decide)
  · simp

example :
    (CategoryTheory.Subfunctor.range
      ((Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver ℚ)).map
        ((finiteAlgSpecOver ℚ).map
          (powerRootMap ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)).op))).IsOneCoverDense
      (faithfullyFlatTestMorphisms ℚ) ∧
    ¬ IsIso ((finiteAlgSpecOver ℚ).map
      (powerRootMap ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)).op).left ∧
    ¬ ∃ candidateLift : Spec (CommRingCat.of ((laurentTest ℚ).obj : Type)) ⟶
        Spec (CommRingCat.of ((powerRootAlgebra ℚ 2 (laurentTest ℚ)
          (laurentUnit ℚ)).obj : Type)),
      candidateLift ≫ Spec.map laurentSquareRootRingMap = 𝟙 _ := by
  let algebraMap := powerRootMap ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)
  have hff : algebraMap.hom.hom.toRingHom.FaithfullyFlat :=
    powerRootMap_faithfullyFlat ℚ 2 (laurentTest ℚ) (laurentUnit ℚ) (by decide)
  have hgeom : Flat ((finiteAlgSpecOver ℚ).map algebraMap.op).left ∧
      Surjective ((finiteAlgSpecOver ℚ).map algebraMap.op).left := by
    simp only [finiteAlgSpecOver_map_left]
    exact (flat_and_surjective_SpecMap_iff _).mpr hff
  have hnot : ¬ IsIso ((finiteAlgSpecOver ℚ).map algebraMap.op).left := by
    intro hiso
    have hiso' : IsIso (Spec.map laurentSquareRootRingMap) := by
      simpa [finiteAlgSpecOver_map_left, laurentSquareRootRingMap, algebraMap]
        using hiso
    exact laurentSquareRoot_no_section ⟨inv (Spec.map laurentSquareRootRingMap), by
      simp only [← laurentSquareRootRingMap_eq_ofHom, IsIso.inv_hom_id]⟩
  let : Flat ((finiteAlgSpecOver ℚ).map algebraMap.op).left := hgeom.1
  let : Surjective ((finiteAlgSpecOver ℚ).map algebraMap.op).left := hgeom.2
  exact ⟨isOneCoverDense_range_lftPoints ℚ ((finiteAlgSpecOver ℚ).map algebraMap.op), hnot,
    laurentSquareRoot_no_section⟩

example :
    (CategoryTheory.Subfunctor.range
      ((algebraicOverPoints ℚ).map affineRootSchemeMap)).IsOneCoverDense
        (faithfullyFlatTestMorphisms ℚ) := by
  let algebraMap := powerRootMap ℚ 2 (laurentTest ℚ) (laurentUnit ℚ)
  have hff : algebraMap.hom.hom.toRingHom.FaithfullyFlat :=
    powerRootMap_faithfullyFlat ℚ 2 (laurentTest ℚ) (laurentUnit ℚ) (by decide)
  have hgeom : Flat affineRootSchemeMap.hom.left ∧
      Surjective affineRootSchemeMap.hom.left := by
    change Flat ((finiteAlgSpecOver ℚ).map algebraMap.op).left ∧
      Surjective ((finiteAlgSpecOver ℚ).map algebraMap.op).left
    simp only [finiteAlgSpecOver_map_left]
    exact (flat_and_surjective_SpecMap_iff _).mpr hff
  let : Flat affineRootSchemeMap.hom.left := hgeom.1
  let : Surjective affineRootSchemeMap.hom.left := hgeom.2
  exact isOneCoverDense_range_algebraicOverPoints ℚ affineRootSchemeMap

end AlgebraicGeometry

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
  let := faithfullyFlatTestMorphisms_containsIdentities ℚ
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
  let := AlgebraicGeometry.faithfullyFlatTestMorphisms_containsIdentities ℚ
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
  let := AlgebraicGeometry.hasPullbacks_finiteTypeAffineTests ℚ
  let := AlgebraicGeometry.faithfullyFlatTestMorphisms_isStableUnderBaseChange ℚ
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
