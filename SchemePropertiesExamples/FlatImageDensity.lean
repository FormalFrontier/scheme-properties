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
The map is therefore neither pointwise surjective nor an isomorphism. The two
density examples apply the stated one-cover theorems; the non-lifting and
explicit root-cover triangle are verified separately.

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

private theorem laurentSquareRootRingMap_finitePresentation :
    laurentSquareRootRingMap.hom.FinitePresentation := by
  change (AdjoinRoot.of (powerRootPolynomial ℚ 2 (laurentTest ℚ)
    (laurentUnit ℚ))).FinitePresentation
  rw [← AdjoinRoot.algebraMap_eq]
  exact (RingHom.finitePresentation_algebraMap).2 (by infer_instance)

private theorem laurentSquareRoot_no_lift :
    ¬ ∃ candidateLift : Spec (CommRingCat.of ((laurentTest ℚ).obj : Type)) ⟶
        Spec (CommRingCat.of ((powerRootAlgebra ℚ 2 (laurentTest ℚ)
          (laurentUnit ℚ)).obj : Type)),
      candidateLift ≫ Spec.map laurentSquareRootRingMap = 𝟙 _ := by
  rintro ⟨candidateLift, htriangle⟩
  have hsection : laurentSquareRootRingMap ≫ Spec.preimage candidateLift = 𝟙 _ := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_preimage, Spec.map_id] using htriangle
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
  letI : Flat (Spec.map laurentSquareRootRingMap) := hgeom.1
  letI : Surjective (Spec.map laurentSquareRootRingMap) := hgeom.2
  letI : LocallyOfFinitePresentation (Spec.map laurentSquareRootRingMap) :=
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
  refine ⟨laurentSquareRoot_no_lift, ?_, laurentSquareRootRingMap_finitePresentation, ?_⟩
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
    exact laurentSquareRoot_no_lift ⟨inv (Spec.map laurentSquareRootRingMap), by simp⟩
  letI : Flat ((finiteAlgSpecOver ℚ).map algebraMap.op).left := hgeom.1
  letI : Surjective ((finiteAlgSpecOver ℚ).map algebraMap.op).left := hgeom.2
  exact ⟨isOneCoverDense_range_lftPoints ℚ ((finiteAlgSpecOver ℚ).map algebraMap.op), hnot,
    laurentSquareRoot_no_lift⟩

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
  letI : Flat affineRootSchemeMap.hom.left := hgeom.1
  letI : Surjective affineRootSchemeMap.hom.left := hgeom.2
  exact isOneCoverDense_range_algebraicOverPoints ℚ affineRootSchemeMap

end AlgebraicGeometry
