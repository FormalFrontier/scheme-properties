/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.FiniteTypeSingleCover
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact

/-!
# Faithfully flat images on finite-type affine tests

The image of a flat, surjective morphism of locally finite-type schemes over a field is
one-cover dense on finitely generated algebra tests. In particular, the covering algebra
remains finitely generated over the field even when the source scheme is not quasi-compact.
The affine-lifting statement also records the finite-presentation property of its cover:
it is this property that permits restriction to finite-type tests.

## References

- J. S. Milne, *Algebraic Groups* (2017), Proposition 5.7: faithfully flat images of
  finite-type schemes are fat. Here the statement also covers locally finite-type schemes.
- Mathlib, `AlgebraicGeometry.QuasiCompactCover.exists_hom` and
  `AlgebraicGeometry.isSheaf_type_propQCTopology_iff`: finite affine refinements and their
  assembly into a single affine cover.
- Mathlib, `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`: local
  Noetherianness and finite presentation over a field.
- `SchemeProperties.FiniteTypePoints` and `SchemeProperties.FiniteTypeSingleCover`:
  restricted points and the one-cover test morphism property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- An affine test of a flat, surjective, locally finitely presented morphism lifts after
one faithfully flat *finitely presented* affine base change. The equation is the
commuting triangle over the original target; no quasi-compactness of the source or
of the morphism is assumed. -/
theorem exists_affine_lift_of_flat_surjective_lfp
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [LocallyOfFinitePresentation f]
    (A : CommRingCat.{u}) (y : Spec A ⟶ Y) :
    ∃ (B : CommRingCat.{u}) (g : A ⟶ B) (x : Spec B ⟶ X),
      g.hom.FaithfullyFlat ∧ g.hom.FinitePresentation ∧
        Spec.map g ≫ y = x ≫ f := by
  let p : pullback y f ⟶ Spec A := pullback.fst y f
  haveI : Flat p := inferInstance
  haveI : LocallyOfFinitePresentation p := inferInstance
  haveI : Surjective p := inferInstance
  let 𝒰 : (Spec A).Cover (Scheme.precoverage @Flat) := p.cover (by infer_instance)
  letI : IsZariskiLocalAtSource
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  letI : Scheme.JointlySurjective (Scheme.precoverage (@Flat : MorphismProperty Scheme.{u})) :=
    Scheme.instJointlySurjectivePrecoverage
  letI : MorphismProperty.RespectsLeft
      (@Flat : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
    ⟨fun _ hi _ hf ↦ by
      letI : IsOpenImmersion _ := hi
      letI : Flat _ := hf
      infer_instance⟩
  haveI : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (𝒰 := 𝒰) (fun _ ↦ by
      change IsOpenMap p
      exact p.isOpenMap)
  obtain ⟨𝒱, refinement, hfinite, hopen⟩ :=
    QuasiCompactCover.exists_hom (P := @Flat) 𝒰
  letI : Finite 𝒱.I₀ := hfinite
  let U : Scheme.{u} := ∐ 𝒱.cover.X
  haveI : IsAffine U := by
    change IsAffine (∐ (fun j : 𝒱.I₀ ↦ Spec (𝒱.X j)))
    infer_instance
  let q : Spec _ ⟶ Spec A := U.isoSpec.inv ≫ Sigma.desc 𝒱.cover.f
  obtain ⟨g, hg⟩ := Spec.map_surjective q
  have hflat : Flat q := by
    letI : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
    have hsource : Flat U.isoSpec.inv := inferInstance
    have htarget : Flat (Sigma.desc 𝒱.cover.f) :=
      IsZariskiLocalAtSource.sigmaDesc 𝒱.cover.map_prop
    exact MorphismProperty.comp_mem _ _ _ hsource htarget
  have hfinitePresentation : LocallyOfFinitePresentation q := by
    have hcomponent (j : 𝒱.I₀) : LocallyOfFinitePresentation (𝒱.cover.f j) := by
      rw [← refinement.w₀ j]
      change LocallyOfFinitePresentation (refinement.h₀ j ≫ p)
      haveI : IsOpenImmersion (refinement.h₀ j) := hopen j
      have hleft : LocallyOfFinitePresentation (refinement.h₀ j) := inferInstance
      have hright : LocallyOfFinitePresentation p := by assumption
      exact MorphismProperty.comp_mem _ _ _ hleft hright
    have hsigma : LocallyOfFinitePresentation (Sigma.desc 𝒱.cover.f) :=
      IsZariskiLocalAtSource.sigmaDesc hcomponent
    dsimp [q]
    infer_instance
  have hsurjective : Surjective q := by
    haveI : Surjective (Sigma.desc 𝒱.cover.f) :=
      Surjective.sigmaDesc_of_union_range_eq_univ 𝒱.cover.iUnion_range
    dsimp [q]
    infer_instance
  let r : U ⟶ pullback y f := Sigma.desc refinement.h₀
  have hcomp (j : 𝒱.I₀) : refinement.h₀ j ≫ p = 𝒱.cover.f j := refinement.w₀ j
  have hcomm : r ≫ p = Sigma.desc 𝒱.cover.f := by
    refine Sigma.hom_ext _ _ (fun j ↦ ?_)
    change (Sigma.ι 𝒱.cover.X j ≫ Sigma.desc refinement.h₀) ≫ p =
      Sigma.ι 𝒱.cover.X j ≫ Sigma.desc 𝒱.cover.f
    calc
      (Sigma.ι 𝒱.cover.X j ≫ Sigma.desc refinement.h₀) ≫ p =
          refinement.h₀ j ≫ p :=
        congrArg (fun h ↦ h ≫ p) (Sigma.ι_desc refinement.h₀ j)
      _ = 𝒱.cover.f j := hcomp j
      _ = Sigma.ι 𝒱.cover.X j ≫ Sigma.desc 𝒱.cover.f :=
        (Sigma.ι_desc 𝒱.cover.f j).symm
  let x : Spec _ ⟶ X := U.isoSpec.inv ≫ r ≫ pullback.snd y f
  refine ⟨_, g, x, (flat_and_surjective_SpecMap_iff g).mp ?_,
    (LocallyOfFinitePresentation.SpecMap_iff g).mp ?_, ?_⟩
  · rw [hg]
    exact ⟨hflat, hsurjective⟩
  · rw [hg]
    exact hfinitePresentation
  · rw [hg]
    dsimp [q, x]
    calc
      (U.isoSpec.inv ≫ Sigma.desc 𝒱.cover.f) ≫ y =
          (U.isoSpec.inv ≫ r ≫ p) ≫ y := by simp only [Category.assoc, hcomm]
      _ = (U.isoSpec.inv ≫ r ≫ pullback.snd y f) ≫ f := by
        simp only [p, Category.assoc, pullback.condition]

/-- The range of a flat, surjective morphism on restricted points is one-cover dense
for finitely generated field algebras. This extends the finite-type claim of
J. S. Milne, *Algebraic Groups*, Proposition 5.7, to locally finite-type schemes;
in particular neither scheme nor the morphism is assumed quasi-compact. -/
theorem isOneCoverDense_range_lftPoints (K : Type u) [Field K]
    {X Y : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))} (f : X ⟶ Y)
    [Flat f.left] [Surjective f.left] :
    (CategoryTheory.Subfunctor.range
      ((Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).map f)).IsOneCoverDense
        (faithfullyFlatTestMorphisms K) := by
  classical
  haveI : LocallyOfFiniteType Y.hom := Y.prop
  haveI : IsLocallyNoetherian (Spec (.of K)) := inferInstance
  haveI : IsLocallyNoetherian ((Functor.fromPUnit (Spec (.of K))).obj Y.right) := by
    change IsLocallyNoetherian (Spec (.of K))
    infer_instance
  haveI : IsLocallyNoetherian Y.left :=
    LocallyOfFiniteType.isLocallyNoetherian Y.hom
  haveI : LocallyOfFiniteType f.left := by
    haveI : LocallyOfFiniteType (f.left ≫ Y.hom) := by
      rw [MorphismProperty.Over.w f]
      exact X.prop
    exact locallyOfFiniteType_of_comp f.left Y.hom
  haveI : LocallyOfFinitePresentation f.left := inferInstance
  intro A point
  obtain ⟨B, g, x, hfaithful, hpresentation, htriangle⟩ :=
    exists_affine_lift_of_flat_surjective_lfp f.left (.of A.unop.obj) point.down.left
  letI : Algebra K B :=
    (g.hom.comp (algebraMap K A.unop.obj)).toAlgebra
  have hfiniteType : Algebra.FiniteType K B := by
    rw [← RingHom.finiteType_algebraMap]
    exact RingHom.FiniteType.comp
      (RingHom.FiniteType.of_finitePresentation hpresentation)
      ((RingHom.finiteType_algebraMap).mpr A.unop.property)
  let B' : FGAlgCat K := ⟨CommAlgCat.of K B, hfiniteType⟩
  have hbase : Spec.map g ≫ ((finiteAlgSpecOver K).obj A).hom =
      ((finiteAlgSpecOver K).obj (op B')).hom := by
    rw [finiteAlgSpecOver_obj_hom, finiteAlgSpecOver_obj_hom, ← Spec.map_comp]
    rfl
  let testCover : (finiteAlgSpecOver K).obj (op B') ⟶
      (finiteAlgSpecOver K).obj A :=
    MorphismProperty.Over.homMk (Spec.map g) hbase
  have hlift : x ≫ X.hom = ((finiteAlgSpecOver K).obj (op B')).hom := by
    have hleft : x ≫ X.hom = (Spec.map g ≫ point.down.left) ≫ Y.hom := by
      calc
        x ≫ X.hom = x ≫ (f.left ≫ Y.hom) :=
          congrArg (fun h ↦ x ≫ h) (MorphismProperty.Over.w f).symm
        _ = (x ≫ f.left) ≫ Y.hom := (Category.assoc _ _ _).symm
        _ = (Spec.map g ≫ point.down.left) ≫ Y.hom :=
          congrArg (fun h ↦ h ≫ Y.hom) htriangle.symm
    have hright : (Spec.map g ≫ point.down.left) ≫ Y.hom =
        Spec.map g ≫ ((finiteAlgSpecOver K).obj A).hom :=
      (Category.assoc _ _ _).trans
        (congrArg (fun h ↦ Spec.map g ≫ h) (MorphismProperty.Over.w point.down))
    exact (hleft.trans hright).trans hbase
  let testLift : (finiteAlgSpecOver K).obj (op B') ⟶ X :=
    MorphismProperty.Over.homMk x hlift
  let coverArrow : (op B') ⟶ A := (finiteAlgSpecOverFullyFaithful K).preimage testCover
  have hmap : ((finiteAlgSpecOver K).map coverArrow).left = Spec.map g := by
    exact congrArg (fun h : (finiteAlgSpecOver K).obj (op B') ⟶
      (finiteAlgSpecOver K).obj A ↦ h.left)
        ((finiteAlgSpecOverFullyFaithful K).map_preimage testCover)
  have hring : coverArrow.unop.hom.hom.toRingHom = g.hom := by
    have hmap' : CommRingCat.ofHom coverArrow.unop.hom.hom.toRingHom = g :=
      Spec.map_injective (by
        simpa only [finiteAlgSpecOver_map_left, finiteAlgSpecOver_obj_left] using hmap)
    exact congrArg (fun φ : CommRingCat.of A.unop.obj ⟶ B ↦ φ.hom) hmap'
  refine ⟨op B', coverArrow, ?_, ?_⟩
  · change coverArrow.unop.hom.hom.toRingHom.FaithfullyFlat
    rw [hring]
    exact hfaithful
  · change ∃ sourcePoint : ULift.{0} ((finiteAlgSpecOver K).obj (op B') ⟶ X),
      ((Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).map f).app
        (op (op B')) sourcePoint =
        ((Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj Y).map
          coverArrow.op point
    refine ⟨ULift.up testLift, ?_⟩
    have hpoint : testLift ≫ f = (finiteAlgSpecOver K).map coverArrow ≫ point.down := by
      apply MorphismProperty.Over.Hom.ext
      change x ≫ f.left = ((finiteAlgSpecOver K).map coverArrow).left ≫ point.down.left
      rw [hmap]
      exact htriangle.symm
    change ULift.up (testLift ≫ f) =
      ULift.up ((finiteAlgSpecOver K).map coverArrow ≫ point.down)
    exact congrArg ULift.up hpoint

/-- For finite-type schemes over a field, the image of a flat, surjective morphism
is one-cover dense on finitely generated algebra tests. This is the functor-of-points
form of J. S. Milne, *Algebraic Groups*, Proposition 5.7. -/
theorem isOneCoverDense_range_algebraicOverPoints (K : Type u) [Field K]
    {X Y : algebraicOver K} (f : X ⟶ Y)
    [Flat f.hom.left] [Surjective f.hom.left] :
    (CategoryTheory.Subfunctor.range ((algebraicOverPoints K).map f)).IsOneCoverDense
      (faithfullyFlatTestMorphisms K) := by
  exact isOneCoverDense_range_lftPoints K f.hom

end AlgebraicGeometry
