/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.FiniteTypePoints
public import SchemeProperties.SingleCoverExtension
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Single faithfully flat extensions on finite-type affine tests

The test objects are finitely generated algebras over a field, regarded contravariantly
as affine schemes. A cover consists of **one** faithfully flat homomorphism between
objects of this category. The functor of points is the existing restricted Yoneda
functor, already defined as a presheaf on the opposite category of affine tests.

The represented-target bridge transports the `Spec` of a faithfully flat algebra
map to an fpqc singleton cover. Mathlib's representable fpqc descent supplies
descent of underlying scheme maps, while the comparison of the finite-type
test pullback with the scheme pullback transports the Čech compatibility.
Surjectivity recovers the structure-map equation over the base. This route
does not compare the entire induced flat topology or translate Milne's
ring-level proof.

## References

- J. S. Milne, *Algebraic Groups*, Lemma 5.9 for the faithfully flat equalizer
  and Proposition 5.10 for the represented extension on finite-type field tests.
- Mathlib's fpqc singleton precoverage and subcanonical topology.
- `SchemeProperties.FiniteTypePoints` for restricted fully faithful points.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry

section General

variable (K : Type u) [CommRing K]

/-- Affine test morphisms whose opposite algebra map is faithfully flat. The target
algebra must itself be finitely generated over the base. -/
def faithfullyFlatTestMorphisms : MorphismProperty ((FGAlgCat.{u} K)ᵒᵖ) :=
  fun _ _ f ↦ f.unop.hom.hom.toRingHom.FaithfullyFlat

/-- Finite-type test algebras admit pushouts, equivalently their opposite category
admits fiber products. The pushout is an algebra tensor product. -/
theorem hasPullbacks_finiteTypeAffineTests :
    HasPullbacks ((FGAlgCat.{u} K)ᵒᵖ) := by
  let P : MorphismProperty CommRingCat.{u} :=
    RingHom.toMorphismProperty @RingHom.FiniteType
  letI : P.IsStableUnderComposition :=
    ⟨fun f g hf hg ↦ RingHom.FiniteType.comp hg hf⟩
  letI : P.IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
      RingHom.finiteType_isStableUnderBaseChange
  letI : P.HasOfPrecompProperty P :=
    ⟨fun f g _ hfg ↦ RingHom.FiniteType.of_comp_finiteType hfg⟩
  haveI : HasPushouts (MorphismProperty.Under P ⊤ (CommRingCat.of K)) := inferInstance
  haveI : HasPushouts (FGAlgCat.{u} K) :=
    Adjunction.hasColimitsOfShape_of_equivalence (FGAlgCat.equivUnder (.of K)).functor
  infer_instance

/-- Faithfully flat test morphisms contain the identities. -/
theorem faithfullyFlatTestMorphisms_containsIdentities :
    (faithfullyFlatTestMorphisms K).ContainsIdentities := by
  constructor
  intro X
  change (RingHom.id X.unop.obj).FaithfullyFlat
  exact RingHom.FaithfullyFlat.of_bijective Function.bijective_id

/-- Faithfully flat test morphisms compose. -/
theorem faithfullyFlatTestMorphisms_isStableUnderComposition :
    (faithfullyFlatTestMorphisms K).IsStableUnderComposition := by
  constructor
  intro X Y Z f g hf hg
  exact RingHom.FaithfullyFlat.stableUnderComposition g.unop.hom.hom.toRingHom
    f.unop.hom.hom.toRingHom hg hf

private theorem isPushout_commRingCat_of_fgAlgCat
    {A B C D : FGAlgCat.{u} K} (f : A ⟶ B) (g : A ⟶ C)
    (f' : B ⟶ D) (g' : C ⟶ D) (hs : IsPushout f g f' g') :
    IsPushout (CommRingCat.ofHom f.hom.hom.toRingHom)
      (CommRingCat.ofHom g.hom.hom.toRingHom)
      (CommRingCat.ofHom f'.hom.hom.toRingHom)
      (CommRingCat.ofHom g'.hom.hom.toRingHom) := by
  let P : MorphismProperty CommRingCat.{u} :=
    RingHom.toMorphismProperty @RingHom.FiniteType
  letI : P.IsStableUnderComposition :=
    ⟨fun a b ha hb ↦ RingHom.FiniteType.comp hb ha⟩
  letI : P.IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
      RingHom.finiteType_isStableUnderBaseChange
  letI : P.HasOfPrecompProperty P :=
    ⟨fun a b _ hab ↦ RingHom.FiniteType.of_comp_finiteType hab⟩
  let F := (FGAlgCat.equivUnder (CommRingCat.of K)).functor
  let G := MorphismProperty.Under.forget P ⊤ (CommRingCat.of K)
  let H := Under.forget (CommRingCat.of K)
  have hs' := ((hs.map F).map G).map H
  exact hs'

/-- A faithfully flat test morphism remains faithfully flat after a pullback
in the finite-type affine test category. -/
theorem faithfullyFlatTestMorphisms_isStableUnderBaseChange :
    (faithfullyFlatTestMorphisms K).IsStableUnderBaseChange := by
  constructor
  intro X Y Y' S f g f' g' hs hg
  have hs' := isPushout_commRingCat_of_fgAlgCat K f.unop g.unop
    g'.unop f'.unop hs.unop
  haveI : (RingHom.toMorphismProperty @RingHom.FaithfullyFlat).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
      RingHom.FaithfullyFlat.isStableUnderBaseChange
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (P := RingHom.toMorphismProperty @RingHom.FaithfullyFlat) hs' hg

end General

variable (K : Type u) [Field K]

private theorem isPullback_finiteAlgSpecOver_self
    {X U : (FGAlgCat.{u} K)ᵒᵖ} (f : U ⟶ X)
    [HasPullbacks ((FGAlgCat.{u} K)ᵒᵖ)] :
    IsPullback ((finiteAlgSpecOver K).map (pullback.fst f f)).left
      ((finiteAlgSpecOver K).map (pullback.snd f f)).left
      ((finiteAlgSpecOver K).map f).left ((finiteAlgSpecOver K).map f).left := by
  have hs : IsPushout f.unop f.unop (pullback.fst f f).unop
      (pullback.snd f f).unop := (IsPullback.of_hasPullback f f).unop.flip
  rw [finiteAlgSpecOver_map_left K (pullback.fst f f),
    finiteAlgSpecOver_map_left K (pullback.snd f f), finiteAlgSpecOver_map_left K f]
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_commRingCat_of_fgAlgCat K _ _ _ _ hs)

/-- Restricted points of a represented finite-type scheme satisfy singleton
Čech descent for every faithfully flat algebra map between finite-type tests.
This is the restriction to these tests of the faithfully flat equalizer of
J. S. Milne, *Algebraic Groups*, Lemma 5.9. The proof instead restricts
Mathlib's fpqc representable descent and compares the two Čech pullbacks;
it does not formalize Milne's ring-level argument. -/
theorem algebraicOverPoints_isSheafFor_faithfullyFlat
    (Y : algebraicOver K) {X U : (FGAlgCat.{u} K)ᵒᵖ} (f : U ⟶ X)
    (hf : faithfullyFlatTestMorphisms K f) :
    Presieve.IsSheafFor ((algebraicOverPoints K).obj Y) (Presieve.singleton f) := by
  letI : HasPullbacks ((FGAlgCat.{u} K)ᵒᵖ) := hasPullbacks_finiteTypeAffineTests K
  let P := finiteAlgSpecOver K
  let fSpec : (P.obj U).left ⟶ (P.obj X).left := (P.map f).left
  have hff : Flat fSpec ∧ Surjective fSpec := by
    change Flat ((finiteAlgSpecOver K).map f).left ∧
      Surjective ((finiteAlgSpecOver K).map f).left
    rw [finiteAlgSpecOver_map_left K f]
    exact (flat_and_surjective_SpecMap_iff _).mpr hf
  letI : Flat fSpec := hff.1
  letI : Surjective fSpec := hff.2
  haveI : QuasiCompact fSpec := by
    change QuasiCompact ((finiteAlgSpecOver K).map f).left
    rw [finiteAlgSpecOver_map_left K f]
    letI : IsAffine (Spec (.of U.unop.obj)) := isAffine_Spec _
    letI : IsAffine (Spec (.of X.unop.obj)) := isAffine_Spec _
    have hAffine : IsAffineHom (Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom)) :=
      isAffineHom_of_isAffine _
    exact quasiCompact_iff_forall_isAffineOpen.mpr
      (fun _ hV ↦ (@IsAffineOpen.preimage _ _ _ hV
        (Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom)) hAffine).isCompact)
  have hcover : Presieve.singleton fSpec ∈ Scheme.fpqcPrecoverage (P.obj X).left :=
    Scheme.Hom.singleton_mem_fpqcPrecoverage fSpec
  have hsheaf : Presieve.IsSheafFor (yoneda.obj Y.obj.left)
      (Presieve.singleton fSpec) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fpqcTopology) _).isSheafFor _
        (Precoverage.generate_mem_toGrothendieck hcover)
  rw [Presieve.isSheafFor_singleton] at hsheaf
  rw [Presieve.isSheafFor_singleton]
  intro x hx
  change ULift.{0} (P.obj U ⟶ Y.obj) at x
  have hpb := isPullback_finiteAlgSpecOver_self K f
  have hcompat : (P.map (pullback.fst f f)).left ≫ x.down.left =
      (P.map (pullback.snd f f)).left ≫ x.down.left := by
    have h := hx (pullback.fst f f) (pullback.snd f f) pullback.condition
    rw [algebraicOverPoints_map_apply K Y (pullback.fst f f) x,
      algebraicOverPoints_map_apply K Y (pullback.snd f f) x] at h
    exact congrArg (fun a : ULift.{0} (P.obj (pullback f f) ⟶ Y.obj) ↦ a.down.left) h
  have hrel {T : Scheme} (a b : T ⟶ (P.obj U).left)
      (hab : a ≫ fSpec = b ≫ fSpec) : a ≫ x.down.left = b ≫ x.down.left := by
    let l := hpb.lift a b hab
    calc
      a ≫ x.down.left = l ≫ ((P.map (pullback.fst f f)).left ≫ x.down.left) := by
        rw [← Category.assoc, hpb.lift_fst]
      _ = l ≫ ((P.map (pullback.snd f f)).left ≫ x.down.left) := by rw [hcompat]
      _ = b ≫ x.down.left := by rw [← Category.assoc, hpb.lift_snd]
  obtain ⟨y, hy, _⟩ := hsheaf x.down.left (fun a b hab ↦ hrel a b hab)
  have hy' : fSpec ≫ y = x.down.left := hy
  have hbase : y ≫ Y.obj.hom = (P.obj X).hom := by
    apply (cancel_epi fSpec).mp
    calc
      fSpec ≫ y ≫ Y.obj.hom = x.down.left ≫ Y.obj.hom :=
        congrArg (fun morphism ↦ morphism ≫ Y.obj.hom) hy'
      _ = (P.obj U).hom := Over.w x.down.hom
      _ = fSpec ≫ (P.obj X).hom := (Over.w (P.map f).hom).symm
  let desc : P.obj X ⟶ Y.obj := MorphismProperty.Over.homMk y hbase
  refine ⟨ULift.up desc, ?_, ?_⟩
  · apply ULift.ext
    apply MorphismProperty.Over.Hom.ext
    change fSpec ≫ y = x.down.left
    exact hy'
  · intro z hz
    apply ULift.ext
    apply MorphismProperty.Over.Hom.ext
    change z.down.left = y
    apply (cancel_epi fSpec).mp
    have hz' : fSpec ≫ z.down.left = x.down.left := by
      have h := congrArg ULift.down hz
      change (P.map f ≫ z.down) = x.down at h
      exact congrArg (fun a : P.obj U ⟶ Y.obj ↦ a.left) h
    exact hz'.trans hy'.symm

/-- Maps from a one-cover dense subfunctor of finite-type scheme points to
represented points correspond exactly to morphisms of the ambient schemes.
In particular, this uses the existing fully faithful restricted Yoneda functor,
and imposes no sheaf condition on the source subfunctor. This represented
finite-type specialization recovers Milne, *Algebraic Groups*, Proposition 5.10
from the generic single-cover extension and represented-target descent. -/
noncomputable def algebraicOverOneCoverEquiv (X Y : algebraicOver K)
    (D : Subfunctor ((algebraicOverPoints K).obj X))
    (hD : D.IsOneCoverDense (faithfullyFlatTestMorphisms K)) :
    (X ⟶ Y) ≃ (D.toFunctor ⟶ (algebraicOverPoints K).obj Y) := by
  letI : HasPullbacks ((FGAlgCat.{u} K)ᵒᵖ) := hasPullbacks_finiteTypeAffineTests K
  letI : (faithfullyFlatTestMorphisms K).IsStableUnderBaseChange :=
    faithfullyFlatTestMorphisms_isStableUnderBaseChange K
  exact (algebraicOverPointsFullyFaithful K).homEquiv.trans
    (Subfunctor.oneCoverExtensionEquiv hD
      (fun f hf ↦ algebraicOverPoints_isSheafFor_faithfullyFlat K Y f hf))

/-- The unique scheme map induced by a transformation from a one-cover dense
subfunctor to represented points. -/
noncomputable def extendAlgebraicOver (X Y : algebraicOver K)
    (D : Subfunctor ((algebraicOverPoints K).obj X))
    (hD : D.IsOneCoverDense (faithfullyFlatTestMorphisms K))
    (φ : D.toFunctor ⟶ (algebraicOverPoints K).obj Y) : X ⟶ Y :=
  (algebraicOverOneCoverEquiv K X Y D hD).symm φ

/-- Restricting the induced scheme map recovers the map on the subfunctor. -/
theorem algebraicOverOneCoverEquiv_apply (X Y : algebraicOver K)
    (D : Subfunctor ((algebraicOverPoints K).obj X))
    (hD : D.IsOneCoverDense (faithfullyFlatTestMorphisms K)) (f : X ⟶ Y) :
    algebraicOverOneCoverEquiv K X Y D hD f =
      D.ι ≫ (algebraicOverPoints K).map f := by
  letI : HasPullbacks ((FGAlgCat.{u} K)ᵒᵖ) := hasPullbacks_finiteTypeAffineTests K
  letI : (faithfullyFlatTestMorphisms K).IsStableUnderBaseChange :=
    faithfullyFlatTestMorphisms_isStableUnderBaseChange K
  exact Subfunctor.oneCoverExtensionEquiv_apply hD
    (fun g hg ↦ algebraicOverPoints_isSheafFor_faithfullyFlat K Y g hg) _

/-- The scheme morphism induced from `φ` restricts to `φ` on the dense subfunctor. -/
@[reassoc (attr := simp)]
theorem ι_comp_extendAlgebraicOver (X Y : algebraicOver K)
    (D : Subfunctor ((algebraicOverPoints K).obj X))
    (hD : D.IsOneCoverDense (faithfullyFlatTestMorphisms K))
    (φ : D.toFunctor ⟶ (algebraicOverPoints K).obj Y) :
    D.ι ≫ (algebraicOverPoints K).map (extendAlgebraicOver K X Y D hD φ) = φ := by
  rw [← algebraicOverOneCoverEquiv_apply K X Y D hD]
  exact (algebraicOverOneCoverEquiv K X Y D hD).apply_symm_apply φ

/-- A morphism of schemes agreeing with a prescribed map on the dense
subfunctor equals its extension. -/
theorem extendAlgebraicOver_unique (X Y : algebraicOver K)
    (D : Subfunctor ((algebraicOverPoints K).obj X))
    (hD : D.IsOneCoverDense (faithfullyFlatTestMorphisms K))
    (φ : D.toFunctor ⟶ (algebraicOverPoints K).obj Y) (f : X ⟶ Y)
    (hf : D.ι ≫ (algebraicOverPoints K).map f = φ) :
    f = extendAlgebraicOver K X Y D hD φ := by
  apply (algebraicOverOneCoverEquiv K X Y D hD).injective
  rw [algebraicOverOneCoverEquiv_apply, hf]
  exact ((algebraicOverOneCoverEquiv K X Y D hD).apply_symm_apply φ).symm

end AlgebraicGeometry
