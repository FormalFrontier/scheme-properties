/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Ideal.MinimalPrimeLocalization
public import SchemeProperties.GenericFiniteness.Avoidance
public import SchemeProperties.GenericFiniteness.Openness
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Sober

/-!
# Finiteness near a generic point

A locally finite type, quasi-compact morphism with a finite point fibre over a
given generic point of the whole target is finite over a dense open neighbourhood
of that point. The restriction has the whole preimage of the open as its source.
Neither separatedness of the morphism nor reducedness of the target is assumed.
Empty generic fibres are allowed.

## References

* Mathlib's scheme restriction, affine-fibre, minimal-prime, and finite-morphism APIs.
* The minimal-primes formalization of finite-type algebras near a minimal prime,
  `Algebra.FiniteType.exists_finite_awayMap_of_mem_minimalPrimes`.
* The multivariate-polynomials generic-freeness formalization,
  `Algebra.FiniteType.exists_free_localizationAway`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

private lemma isGenericPoint_opens
    {S : Scheme.{u}} (η : S) (hη : IsGenericPoint η (Set.univ : Set S))
    (U : S.Opens) (hηU : η ∈ U) :
    IsGenericPoint (⟨η, hηU⟩ : U) (Set.univ : Set U) := by
  apply isGenericPoint_iff_specializes.mpr
  intro y
  constructor
  · intro _; trivial
  · intro _
    exact U.ι.isOpenEmbedding.isInducing.specializes_iff.mp
      (hη.specializes (Set.mem_univ y.1))

private lemma isFinite_fiber_of_finite_preimage
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (η : S) (hf : (f ⁻¹' {η}).Finite) :
    IsFinite (f.fiberToSpecResidueField η) := by
  have : Finite (f ⁻¹' {η}) := hf.to_subtype
  have : Finite (f.fiber η) := Finite.of_injective
    (f.fiberHomeo η) (f.fiberHomeo η).injective
  have : LocallyOfFiniteType (f.fiberToSpecResidueField η) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField η)))
  have : QuasiCompact (f.fiberToSpecResidueField η) :=
    inferInstanceAs (QuasiCompact (pullback.snd f (S.fromSpecResidueField η)))
  have : LocallyQuasiFinite (f.fiberToSpecResidueField η) :=
    .of_finite_preimage_singleton _ fun _ ↦ Set.toFinite _
  exact .of_locallyQuasiFinite _

private lemma exists_isolating_affine_chart
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (η : S) (hf : (f ⁻¹' {η}).Finite) {A : S.Opens} (hηA : η ∈ A)
    (x : f ⁻¹' {η}) :
    ∃ W : X.Opens, IsAffineOpen W ∧ x.1 ∈ W ∧ W ≤ f ⁻¹ᵁ A ∧
      ∀ y ∈ W, f y = η → y = x.1 := by
  have : Finite (f ⁻¹' {η}) := hf.to_subtype
  have : Finite (f.fiber η) := Finite.of_injective
    (f.fiberHomeo η) (f.fiberHomeo η).injective
  have : LocallyOfFiniteType (f.fiberToSpecResidueField η) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField η)))
  have : LocallyQuasiFinite (f.fiberToSpecResidueField η) :=
    .of_finite_preimage_singleton _ fun _ ↦ Set.toFinite _
  have : IsLocallyArtinian (f.fiber η) :=
    .of_locallyQuasiFinite (f.fiberToSpecResidueField η)
  have hdiscrete : _root_.IsDiscrete (f ⁻¹' {η}) := by
    simpa only [Set.image_univ, Scheme.Hom.range_fiberι] using
      (isDiscrete_univ_iff.mpr (inferInstance : DiscreteTopology (f.fiber η))).image
        (f.fiberι η).isEmbedding.toIsInducing
  obtain ⟨O, hO, hOx⟩ :=
    isDiscrete_iff_forall_mem_exists_isOpen.mp hdiscrete x.1 x.2
  have hxO : x.1 ∈ O := by
    have hx : x.1 ∈ O ∩ f ⁻¹' {η} := by rw [hOx]; rfl
    exact hx.1
  let V : X.Opens := ⟨O, hO⟩ ⊓ f ⁻¹ᵁ A
  have hxV : x.1 ∈ V := ⟨hxO, by
    change f x.1 ∈ A
    rw [show f x.1 = η from x.2]
    exact hηA⟩
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  refine ⟨W, hW, hxW, hWV.trans inf_le_right, ?_⟩
  intro y hy hfy
  have hyO : y ∈ O ∩ f ⁻¹' {η} := ⟨(hWV hy).1, hfy⟩
  rwa [hOx] at hyO

private lemma moduleFinite_fiber_of_finite_spec_preimage
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] (p : PrimeSpectrum R)
    (hf : ((Spec.map (CommRingCat.ofHom (algebraMap R B))) ⁻¹' {p}).Finite) :
    Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber B) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have : LocallyOfFiniteType g :=
    (HasRingHomProperty.Spec_iff
      (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))).mpr
      (by simpa only [CommRingCat.hom_ofHom] using
        (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType R B)))
  have hfinite : IsFinite (g.fiberToSpecResidueField p) :=
    isFinite_fiber_of_finite_preimage g p hf
  have hfinite' : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B)))) := by
    let : IsFinite (g.fiberToSpecResidueField p) := hfinite
    rw [Arrow.iso_w' (Spec.fiberToSpecResidueFieldIso R B p)]
    infer_instance
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hfinite')

private lemma isFinite_resLE_basicOpen_of_awayMap_finite
    {X S : Scheme.{u}} (f : X ⟶ S) {A : S.Opens} {W : X.Opens}
    (hA : IsAffineOpen A) (hW : IsAffineOpen W) (e : W ≤ f ⁻¹ᵁ A)
    (r : Γ(S, A)) (hr : (Localization.awayMap (f.appLE A W e).hom r).Finite) :
    IsFinite (f.resLE (S.basicOpen r) (W ⊓ f ⁻¹ᵁ S.basicOpen r) inf_le_right) := by
  let R := Γ(S, A)
  let B := Γ(X, W)
  let φ : R →+* B := (f.appLE A W e).hom
  let D := S.basicOpen r
  let V := X.basicOpen (φ r)
  have eV : V ≤ f ⁻¹ᵁ D := by
    change X.basicOpen (f.appLE A W e r) ≤ f ⁻¹ᵁ S.basicOpen r
    rw [Scheme.basicOpen_appLE]
    exact inf_le_right
  have : IsAffine D.toScheme := hA.basicOpen r
  have : IsAffine V.toScheme := hW.basicOpen (φ r)
  let R' := Γ(S, D)
  let B' := Γ(X, V)
  let ψ : R' →+* B' := (f.appLE D V eV).hom
  have : IsLocalization.Away r R' := hA.isLocalization_basicOpen r
  have : IsLocalization.Away (φ r) B' := hW.isLocalization_basicOpen (φ r)
  have hmap : IsLocalization.Away.map R' B' φ r = ψ := by
    exact (congrArg CommRingCat.Hom.hom
      (IsAffineOpen.appLE_eq_away_map f hA hW e r)).symm
  have hψ : ψ.Finite := by
    rw [← hmap]
    exact (RingHom.finite_respectsIso.isLocalization_away_iff R' B' φ r).mp hr
  have hg : IsFinite (f.resLE D V eV) := by
    have happ : (f.resLE D V eV).appTop.hom.Finite :=
      (RingHom.finite_respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f D V eV)).mpr hψ
    let g : V.toScheme ⟶ D.toScheme := f.resLE D V eV
    let : IsFinite (Spec.map g.appTop) := (IsFinite.SpecMap_iff _).mpr happ
    change IsFinite g
    rw [Arrow.iso_w' (arrowIsoSpecΓOfIsAffine g).symm]
    infer_instance
  have hV : V = W ⊓ f ⁻¹ᵁ D := Scheme.basicOpen_appLE f W A e r
  have hfamily : ∀ e' : V ≤ f ⁻¹ᵁ D, IsFinite (f.resLE D V e') := fun _ ↦ hg
  exact (hV ▸ hfamily) inf_le_right

private lemma exists_isFinite_resLE_basicOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S))
    (hf : (f ⁻¹' {η}).Finite) {A : S.Opens} {W : X.Opens}
    (hA : IsAffineOpen A) (hW : IsAffineOpen W) (e : W ≤ f ⁻¹ᵁ A) (hηA : η ∈ A) :
    ∃ r : Γ(S, A), η ∈ S.basicOpen r ∧
      IsFinite (f.resLE (S.basicOpen r) (W ⊓ f ⁻¹ᵁ S.basicOpen r) inf_le_right) := by
  let R := Γ(S, A)
  let B := Γ(X, W)
  let φ : R →+* B := (f.appLE A W e).hom
  let : Algebra R B := φ.toAlgebra
  have : Algebra.FiniteType R B := f.finiteType_appLE hA hW e
  let p : PrimeSpectrum R := hA.primeIdealOf ⟨η, hηA⟩
  have hp : p.asIdeal ∈ minimalPrimes R := by
    apply PrimeSpectrum.isMin_iff.mp
    intro q _
    apply (PrimeSpectrum.le_iff_specializes p q).mpr
    apply hA.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp
    rw [show hA.fromSpec p = η from hA.fromSpec_primeIdealOf ⟨η, hηA⟩]
    exact hη.specializes (Set.mem_univ _)
  have hfp : ((Spec.map (CommRingCat.ofHom (algebraMap R B))) ⁻¹' {p}).Finite := by
    have hfin := hf.preimage hW.fromSpec.isOpenEmbedding.injective.injOn
    apply hfin.subset
    intro q hq
    change f (hW.fromSpec q) = η
    have hnat := congrArg (fun k : Spec (CommRingCat.of B) ⟶ S ↦ k q)
      (IsAffineOpen.SpecMap_appLE_fromSpec f hA hW e)
    simp only [Scheme.Hom.comp_apply] at hnat
    rw [← hnat, show Spec.map (f.appLE A W e) q = p from hq]
    exact hA.fromSpec_primeIdealOf ⟨η, hηA⟩
  have : Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber B) :=
    moduleFinite_fiber_of_finite_spec_preimage p hfp
  obtain ⟨r, hr, hfinite⟩ :=
    Algebra.FiniteType.exists_finite_awayMap_of_mem_minimalPrimes (B := B) p hp
  refine ⟨r, ?_, isFinite_resLE_basicOpen_of_awayMap_finite f hA hW e r hfinite⟩
  have hr' : p ∈ hA.fromSpec ⁻¹ᵁ S.basicOpen r := by
    rw [hA.fromSpec_preimage_basicOpen]
    exact hr
  have hpη : hA.fromSpec p = η := hA.fromSpec_primeIdealOf ⟨η, hηA⟩
  exact hpη ▸ (hA.fromSpec.mem_preimage.mp hr')

private lemma isPullback_resLE_inf
    {X S : Scheme.{u}} (f : X ⟶ S) (W : X.Opens) {U D : S.Opens} (hUD : U ≤ D) :
    CategoryTheory.IsPullback
      (f.resLE U (W ⊓ f ⁻¹ᵁ U) inf_le_right)
      (X.homOfLE (inf_le_inf_left W (f.preimage_mono hUD)))
      (S.homOfLE hUD) (f.resLE D (W ⊓ f ⁻¹ᵁ D) inf_le_right) := by
  let K := W ⊓ f ⁻¹ᵁ U
  let T := W ⊓ f ⁻¹ᵁ D
  have hKT : K ≤ T := inf_le_inf_left W (f.preimage_mono hUD)
  have hK : K = f ⁻¹ᵁ U ⊓ (𝟙 X) ⁻¹ᵁ T := by
    ext x
    constructor
    · rintro ⟨hxW, hxU⟩
      exact ⟨hxU, hxW, f.preimage_mono hUD hxU⟩
    · rintro ⟨hxU, hxW, _⟩
      exact ⟨hxW, hxU⟩
  have hpb := Scheme.Hom.isPullback_resLE (CategoryTheory.IsPullback.id_vert f)
    (US := D) (UT := T) (UX := U) (UY := K)
    (show T ≤ f ⁻¹ᵁ D from inf_le_right) (by simpa using hUD) hK
  have hXT : Scheme.Hom.resLE (𝟙 X : X ⟶ X) T K (by simpa using hKT) =
      X.homOfLE hKT := Scheme.Hom.resLE_id hKT
  have hSD : Scheme.Hom.resLE (𝟙 S : S ⟶ S) D U (by simpa using hUD) =
      S.homOfLE hUD := Scheme.Hom.resLE_id hUD
  rw [hXT, hSD] at hpb
  exact hpb

private lemma isOpenMap_morphismRestrict_of_le
    {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.Opens} (hUV : U ≤ V)
    (hf : IsOpenMap (f ∣_ V)) : IsOpenMap (f ∣_ U) := by
  have hres (T : S.Opens) :
      topologically @IsOpenMap (f.resLE T (⊤ ⊓ f ⁻¹ᵁ T) inf_le_right) ↔
        IsOpenMap (f ∣_ T) := by
    trans topologically @IsOpenMap (f.resLE T (f ⁻¹ᵁ T) le_rfl)
    · exact f.resLE_congr inf_le_right rfl (top_inf_eq _) (topologically @IsOpenMap)
    · exact (congrArg (fun q : (f ⁻¹ᵁ T).toScheme ⟶ T.toScheme ↦
        topologically @IsOpenMap q) (f.resLE_eq_morphismRestrict (U := T))).to_iff
  have hf' := (hres V).mpr hf
  have h := IsZariskiLocalAtTarget.of_isPullback
    (P := topologically @IsOpenMap) (isPullback_resLE_inf f ⊤ hUV).flip hf'
  exact (hres U).mp h

private lemma exists_finite_chart_cover
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S)) (hf : (f ⁻¹' {η}).Finite) :
    ∃ (U : S.Opens) (W : (f ⁻¹' {η}) → X.Opens),
      η ∈ U ∧ IsAffineOpen U ∧
      (∀ i, IsAffineOpen (W i)) ∧
      (∀ i, IsFinite (f.resLE U (W i ⊓ f ⁻¹ᵁ U) inf_le_right)) ∧
      (∀ i, ∀ y ∈ W i, f y = η → y = i.1) ∧ f ⁻¹ᵁ U ≤ iSup W := by
  classical
  let := hf.fintype
  obtain ⟨A, hA, hηA, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := η) (U := ⊤) trivial
  choose W hW hiW eW hisolate using exists_isolating_affine_chart f η hf hηA
  have hcover : f ⁻¹' {η} ⊆ (iSup W : X.Opens) := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hiW ⟨x, hx⟩⟩
  obtain ⟨V, hηV, hV⟩ :=
    f.exists_open_preimage_subset_of_isGenericPoint η hη (iSup W) hcover
  choose r hr hfinite using fun i ↦
    exists_isFinite_resLE_basicOpen f η hη hf hA (hW i) (eW i) hηA
  have hcommon (t : Finset (f ⁻¹' {η})) :
      ∃ U : S.Opens, η ∈ U ∧ U ≤ A ⊓ V ∧ ∀ i ∈ t, U ≤ S.basicOpen (r i) := by
    induction t using Finset.induction_on with
    | empty => exact ⟨A ⊓ V, ⟨hηA, hηV⟩, le_rfl, by simp⟩
    | @insert i t hi ih =>
        obtain ⟨U, hηU, hU, hUi⟩ := ih
        refine ⟨U ⊓ S.basicOpen (r i), ⟨hηU, hr i⟩, inf_le_left.trans hU, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact inf_le_right
        · exact inf_le_left.trans (hUi j hj)
  obtain ⟨K, hηK, hK, hKi⟩ := hcommon Finset.univ
  obtain ⟨a, haK, hηa⟩ := hA.exists_basicOpen_le (V := K) ⟨η, hηK⟩ hηA
  let U := S.basicOpen a
  have hUD (i : f ⁻¹' {η}) : U ≤ S.basicOpen (r i) :=
    haK.trans (hKi i (Finset.mem_univ i))
  refine ⟨U, W, hηa, hA.basicOpen a, hW, ?_, hisolate, ?_⟩
  · intro i
    exact MorphismProperty.of_isPullback
      (P := (@IsFinite : MorphismProperty Scheme.{u}))
      (isPullback_resLE_inf f (W i) (hUD i)).flip (hfinite i)
  · exact (f.preimage_mono (haK.trans (hK.trans inf_le_right))).trans hV

private lemma isFinite_of_isCompl_openImmersions
    {U V X S : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X) (f : X ⟶ S)
    [IsOpenImmersion i] [IsOpenImmersion j] (hij : IsCompl i.opensRange j.opensRange)
    [IsFinite (i ≫ f)] [IsFinite (j ≫ f)] : IsFinite f := by
  obtain ⟨hC⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl i j hij
  let q : U ⨿ V ⟶ X := coprod.desc i j
  have hq : IsIso q := by
    -- The colimit characterization uses the points of the two cocones.
    change IsIso ((colimit.isColimit (pair U V)).desc (BinaryCofan.mk i j))
    exact (IsColimit.nonempty_isColimit_iff_isIso_desc
      (s := colimit.cocone (pair U V)) (t := BinaryCofan.mk i j)
      (colimit.isColimit (pair U V))).mp ⟨hC⟩
  let : IsIso q := hq
  have hf : IsFinite (q ≫ f) := by
    dsimp only [q]
    rw [coprod.desc_comp f i j]
    infer_instance
  let : IsFinite (q ≫ f) := hf
  simpa only [IsIso.inv_hom_id_assoc] using
    (inferInstance : IsFinite (inv q ≫ (q ≫ f)))

private lemma isFinite_iSup_finset_of_disjoint
    {ι : Type u} {X S : Scheme.{u}} (f : X ⟶ S) (W : ι → X.Opens)
    (hdisj : Pairwise (fun i j ↦ Disjoint (W i) (W j)))
    (hfin : ∀ i, IsFinite ((W i).ι ≫ f)) (t : Finset ι) :
    IsFinite (((⨆ i ∈ t, W i) : X.Opens).ι ≫ f) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      have he : (⨆ i ∈ (∅ : Finset ι), W i) = ⊥ := by simp
      rw [he]
      have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ by simpa using x.property⟩
      infer_instance
  | @insert i t hi ih =>
      rw [Finset.iSup_insert]
      let V : X.Opens := ⨆ j ∈ t, W j
      let U : X.Opens := W i ⊔ V
      let a : (W i).toScheme ⟶ U.toScheme := X.homOfLE le_sup_left
      let b : V.toScheme ⟶ U.toScheme := X.homOfLE le_sup_right
      have hd : Disjoint (W i) V := by
        apply disjoint_iSup_iff.mpr
        intro j
        apply disjoint_iSup_iff.mpr
        intro hj
        apply hdisj
        rintro rfl
        exact hi hj
      have hc : IsCompl a.opensRange b.opensRange := by
        dsimp only [a, b]
        rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE]
        constructor
        · rw [← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_left]
          intro x hxi hxV
          exact Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr hd) hxi hxV
        · rw [codisjoint_iff]
          ext x
          have hx : U.ι x = x.1 := Scheme.Opens.ι_apply U x
          simpa only [Opens.coe_sup, Opens.coe_top, Set.mem_union,
            Scheme.Hom.coe_preimage, Set.mem_preimage, Set.mem_univ,
            SetLike.mem_coe, hx, iff_true] using
            (show x.1 ∈ W i ∨ x.1 ∈ V from x.property)
      have : IsFinite (a ≫ (U.ι ≫ f)) := by
        simpa only [← Category.assoc, a, Scheme.homOfLE_ι] using hfin i
      have : IsFinite (b ≫ (U.ι ≫ f)) := by
        simpa only [← Category.assoc, b, Scheme.homOfLE_ι, V] using ih
      exact isFinite_of_isCompl_openImmersions a b (U.ι ≫ f) hc

private lemma isFinite_of_disjoint_openCover
    {ι : Type u} [Finite ι] {X S : Scheme.{u}} (f : X ⟶ S) (W : ι → X.Opens)
    (hdisj : Pairwise (fun i j ↦ Disjoint (W i) (W j))) (hcov : iSup W = ⊤)
    (hfin : ∀ i, IsFinite ((W i).ι ≫ f)) : IsFinite f := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hf := isFinite_iSup_finset_of_disjoint f W hdisj hfin Finset.univ
  have he : (⨆ i ∈ (Finset.univ : Finset ι), W i) = ⊤ := by simpa using hcov
  rw [he] at hf
  have : IsIso (⊤ : X.Opens).ι := inferInstanceAs (IsIso X.topIso.hom)
  let : IsFinite ((⊤ : X.Opens).ι ≫ f) := hf
  simpa only [IsIso.inv_hom_id_assoc] using
    (inferInstance : IsFinite (inv (⊤ : X.Opens).ι ≫ ((⊤ : X.Opens).ι ≫ f)))

private lemma disjoint_of_isOpenMap_of_generic_fiber_disjoint
    {X T : Scheme.{u}} (g : X ⟶ T)
    (ζ : T) (hζ : IsGenericPoint ζ (Set.univ : Set T)) (W V : X.Opens)
    (hopen : IsOpenMap (W.ι ≫ g))
    (hmiss : ∀ x : X, x ∈ W → x ∈ V → g x ≠ ζ) : Disjoint W V := by
  rw [← Opens.coe_disjoint, Set.disjoint_left]
  intro x hxW hxV
  let O : W.toScheme.Opens := W.ι ⁻¹ᵁ V
  have hO : IsOpen ((W.ι ≫ g) '' (O : Set W.toScheme)) := hopen _ O.isOpen
  have hne : ((W.ι ≫ g) '' (O : Set W.toScheme)).Nonempty :=
    ⟨g x, ⟨⟨x, hxW⟩, hxV, rfl⟩⟩
  have hζmem : ζ ∈ (W.ι ≫ g) '' (O : Set W.toScheme) :=
    (hζ.mem_open_set_iff hO).mpr (by simpa only [Set.univ_inter] using hne)
  obtain ⟨z, hz, hzg⟩ := hζmem
  exact hmiss z.1 z.2 hz hzg

/-- A locally finite type, quasi-compact morphism with finite point fibre over a
given generic point of the whole target is finite on the whole preimage of some
dense open neighbourhood of that point. No separatedness assumption is required. -/
theorem Scheme.Hom.exists_isFinite_morphismRestrict_of_isGenericPoint
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S))
    (hf : (f ⁻¹' {η}).Finite) :
    ∃ U : S.Opens, η ∈ U ∧ Dense (U : Set S) ∧ IsFinite (f ∣_ U) := by
  classical
  let I := f ⁻¹' {η}
  let : Fintype I := hf.fintype
  obtain ⟨U₀, W, hηU₀, _, _, hfin, hisolate, hcover⟩ :=
    exists_finite_chart_cover f η hη hf
  let X₀ := (f ⁻¹ᵁ U₀).toScheme
  let F : X₀ ⟶ U₀.toScheme := f ∣_ U₀
  let A (i : I) : X.Opens := W i ⊓ f ⁻¹ᵁ U₀
  let k (i : I) : (A i).toScheme ⟶ X₀ := X.homOfLE inf_le_right
  let g (i : I) : (A i).toScheme ⟶ U₀.toScheme := k i ≫ F
  let η₀ : U₀ := ⟨η, hηU₀⟩
  have hη₀ : IsGenericPoint η₀ (Set.univ : Set U₀) :=
    isGenericPoint_opens η hη U₀ hηU₀
  have hget (i : I) : ∃ O : U₀.toScheme.Opens, η₀ ∈ O ∧ IsOpenMap (g i ∣_ O) := by
    have : IsFinite (g i) := hfin i
    exact (g i).exists_isOpenMap_morphismRestrict_of_isFinite_of_isGenericPoint η₀ hη₀
  choose O hηO hopenO using hget
  let V : U₀.toScheme.Opens := ⨅ i, O i
  have hηV : η₀ ∈ V := by
    change η₀ ∈ (((⨅ i, O i) : U₀.toScheme.Opens) : Set U₀)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hηO
  let Y := (F ⁻¹ᵁ V).toScheme
  let G : Y ⟶ V := F ∣_ V
  let ζ : V := ⟨η₀, hηV⟩
  have hζ : IsGenericPoint ζ (Set.univ : Set V) :=
    isGenericPoint_opens η₀ hη₀ V hηV
  let l (i : I) : (g i ⁻¹ᵁ V).toScheme ⟶ Y := k i ∣_ F ⁻¹ᵁ V
  have (i : I) : IsOpenImmersion (l i) := by
    have : IsOpenImmersion (k i) :=
      inferInstanceAs (IsOpenImmersion (X.homOfLE
        (show A i ≤ f ⁻¹ᵁ U₀ from inf_le_right)))
    exact inferInstanceAs (IsOpenImmersion (k i ∣_ F ⁻¹ᵁ V))
  let R (i : I) : Y.Opens := (l i).opensRange
  have hfinl (i : I) : IsFinite (l i ≫ G) := by
    have : IsFinite (g i) := hfin i
    change IsFinite ((k i ∣_ F ⁻¹ᵁ V) ≫ F ∣_ V)
    rw [← morphismRestrict_comp]
    change IsFinite (g i ∣_ V)
    infer_instance
  have hopenl (i : I) : IsOpenMap (l i ≫ G) := by
    change IsOpenMap ((k i ∣_ F ⁻¹ᵁ V) ≫ F ∣_ V)
    rw [← morphismRestrict_comp]
    exact isOpenMap_morphismRestrict_of_le (g i) (iInf_le _ i) (hopenO i)
  have hfinR (i : I) : IsFinite ((R i).ι ≫ G) := by
    change IsFinite ((l i).opensRange.ι ≫ G)
    rw [← Scheme.Hom.isoOpensRange_inv_comp (l i), Category.assoc]
    have : IsFinite (l i ≫ G) := hfinl i
    infer_instance
  have hopenR (i : I) : IsOpenMap ((R i).ι ≫ G) := by
    change IsOpenMap ((l i).opensRange.ι ≫ G)
    rw [← Scheme.Hom.isoOpensRange_inv_comp (l i), Category.assoc]
    exact (hopenl i).comp (l i).isoOpensRange.inv.isOpenEmbedding.isOpenMap
  have hmem (i : I) (x : Y) (hx : x ∈ R i) : x.1.1 ∈ W i := by
    obtain ⟨z, hz⟩ := (Scheme.Hom.mem_opensRange (f := l i)).mp hx
    have hl : (l i z).1 = k i z.1 :=
      morphismRestrict_base_coe (k i) (F ⁻¹ᵁ V) z
    have hk : (k i z.1).1 = z.1.1 := by
      exact Scheme.homOfLE_apply (X := X)
        (show A i ≤ f ⁻¹ᵁ U₀ from inf_le_right) z.1
    have he : z.1.1 = x.1.1 :=
      hk.symm.trans ((congrArg (fun y : X₀ ↦ y.1) hl).symm.trans
        (congrArg (fun y : Y ↦ y.1.1) hz))
    exact he ▸ z.1.2.1
  have hdisj : Pairwise (fun i j ↦ Disjoint (R i) (R j)) := by
    intro i j hij
    apply disjoint_of_isOpenMap_of_generic_fiber_disjoint G ζ hζ (R i) (R j) (hopenR i)
    intro x hxi hxj hGx
    have hfx : f x.1.1 = η := by
      have hG : (G x).1 = F x.1 := morphismRestrict_base_coe F V x
      have hF : (F x.1).1 = f x.1.1 := morphismRestrict_base_coe f U₀ x.1
      calc
        f x.1.1 = (F x.1).1 := hF.symm
        _ = (G x).1.1 := (congrArg (fun y : U₀.toScheme ↦ y.1) hG).symm
        _ = η := congrArg (fun y : V ↦ y.1.1) hGx
    apply hij
    apply Subtype.ext
    exact (hisolate i _ (hmem i x hxi) hfx).symm.trans
      (hisolate j _ (hmem j x hxj) hfx)
  have hcov : iSup R = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover x.1.2)
    let z : A i := ⟨x.1.1, hi, x.1.2⟩
    have hkz : k i z = x.1 := by
      apply Subtype.ext
      exact Scheme.homOfLE_apply (X := X)
        (show A i ≤ f ⁻¹ᵁ U₀ from inf_le_right) z
    have hz : z ∈ k i ⁻¹ᵁ F ⁻¹ᵁ V := by
      change k i z ∈ F ⁻¹ᵁ V
      rw [hkz]
      exact x.2
    have hlz : l i ⟨z, hz⟩ = x := by
      apply Subtype.ext
      exact (morphismRestrict_base_coe (k i) (F ⁻¹ᵁ V) ⟨z, hz⟩).trans hkz
    exact Opens.mem_iSup.mpr
      ⟨i, (Scheme.Hom.mem_opensRange (f := l i)).mpr ⟨⟨z, hz⟩, hlz⟩⟩
  have hG : IsFinite G := isFinite_of_disjoint_openCover G R hdisj hcov hfinR
  let U : S.Opens := U₀.ι ''ᵁ V
  have hηU : η ∈ U := ⟨η₀, hηV, rfl⟩
  refine ⟨U, hηU, ?_, ?_⟩
  · apply dense_iff_closure_eq.mpr
    apply le_antisymm (Set.subset_univ _)
    rw [← hη.def]
    exact closure_mono (Set.singleton_subset_iff.mpr hηU)
  · let : IsFinite ((f ∣_ U₀) ∣_ V) := hG
    rw [Arrow.iso_w' (morphismRestrictRestrict f U₀ V)]
    infer_instance

end AlgebraicGeometry
