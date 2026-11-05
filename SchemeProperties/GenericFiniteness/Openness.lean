/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.Sober
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import MultivariatePolynomials.GenericFreeness

/-!
# Openness of a finite morphism near a generic point

A finite morphism becomes topologically open after restricting to a neighbourhood
of a given generic point of its whole target. The target need not be reduced, and
no nonemptiness assumption is imposed on the source or the generic fibre.

The proof first applies generic freeness over the nilradical quotient of an
affine target. Finiteness is retained under this base change; finite free modules
are finitely presented, so flatness gives openness there. Openness is then
reflected through the quotient map on point spaces. No descent of finiteness
through a nilpotent thickening is used.

## References

* Mathlib's finite-morphism, pullback, and universally-open-morphism APIs.
* The multivariate-polynomials generic-freeness API
  `Algebra.FiniteType.exists_free_localizationAway`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

private lemma isOpenMap_of_isPullback_of_isQuotientMap
    {P X T S : Scheme.{u}} {p : P ⟶ X} {g : P ⟶ T} {f : X ⟶ S} {q : T ⟶ S}
    (H : IsPullback p g f q) (hq : IsQuotientMap q) (hg : IsOpenMap g) :
    IsOpenMap f := by
  intro W hW
  apply hq.isCoinducing.isOpen_preimage.mp
  rw [← Scheme.image_preimage_eq_of_isPullback H W]
  exact hg _ (hW.preimage p.continuous)

private lemma isOpenMap_morphismRestrict_of_iso
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (eX : X ≅ X') (eS : S ≅ S')
    (he : f ≫ eS.hom = eX.hom ≫ f') (V : S'.Opens)
    (hV : IsOpenMap (f' ∣_ V)) : IsOpenMap (f ∣_ eS.hom ⁻¹ᵁ V) := by
  have hc : IsOpenMap ((f ≫ eS.hom) ∣_ V) := by
    rw [he, morphismRestrict_comp]
    exact hV.comp (eX.hom ∣_ f' ⁻¹ᵁ V).isOpenEmbedding.isOpenMap
  have heq : f ∣_ eS.hom ⁻¹ᵁ V =
      ((f ≫ eS.hom) ∣_ V) ≫ inv (eS.hom ∣_ V) := by
    rw [morphismRestrict_comp]
    simp
  rw [heq]
  exact (inv (eS.hom ∣_ V)).isOpenEmbedding.isOpenMap.comp hc

private lemma exists_universallyOpen_localized_tensorProduct
    {R B : Type u} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Module.Finite R B] :
    ∃ r : R, r ≠ 0 ∧ UniversallyOpen (Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] B)))) := by
  obtain ⟨r, hr, hfree⟩ :=
    Algebra.FiniteType.exists_free_localizationAway (A := R) (B := B)
  let R' := Localization.Away r
  let C := R' ⊗[R] B
  have : Module.Free R' C := hfree
  have : Module.Projective R' C := Module.Projective.of_free
  have : Module.FinitePresentation R' C := Module.finitePresentation_of_projective R' C
  have : Algebra.FinitePresentation R' C := inferInstance
  have : Module.Flat R' C := Module.Flat.of_free
  let g := Spec.map (CommRingCat.ofHom (algebraMap R' C))
  have : Flat g := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : LocallyOfFinitePresentation g :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  exact ⟨r, hr, UniversallyOpen.of_flat g⟩

private lemma exists_isOpenMap_specMap_morphismRestrict_of_domain
    {R B : Type u} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Module.Finite R B]
    (η : Spec (CommRingCat.of R)) (hη : IsGenericPoint η (Set.univ : Set (Spec (.of R)))) :
    ∃ U : (Spec (.of R)).Opens, η ∈ U ∧
      IsOpenMap (Spec.map (CommRingCat.ofHom (algebraMap R B)) ∣_ U) := by
  obtain ⟨r, hr, hopen⟩ := exists_universallyOpen_localized_tensorProduct (R := R) (B := B)
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let q := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  have hfst : UniversallyOpen (pullback.fst q f) := by
    apply (MorphismProperty.cancel_left_of_respectsIso
      (P := @UniversallyOpen) (pullbackSpecIso R (Localization.Away r) B).inv _).mp
    simpa only [q, f, pullbackSpecIso_inv_fst'] using hopen
  have hsnd : UniversallyOpen (pullback.snd f q) := by
    rw [← pullbackSymmetry_hom_comp_fst]
    infer_instance
  have hrestrict : UniversallyOpen (f ∣_ q.opensRange) :=
    (MorphismProperty.arrow_mk_iso_iff (P := @UniversallyOpen)
      (morphismRestrictOpensRange f q)).mpr hsnd
  refine ⟨q.opensRange, ?_, (f ∣_ q.opensRange).isOpenMap⟩
  apply (hη.mem_open_set_iff q.opensRange.isOpen).mpr
  rw [Set.univ_inter]
  have hRange : q.opensRange = PrimeSpectrum.basicOpen r :=
    Scheme.Hom.opensRange_localizationAway (R := .of R) r
  have hne : q.opensRange ≠ ⊥ := by
    intro hbot
    have hnil : IsNilpotent r :=
      (PrimeSpectrum.basicOpen_eq_bot_iff r).mp (hRange.symm.trans hbot)
    exact hr hnil.eq_zero
  exact (Opens.ne_bot_iff_nonempty q.opensRange).mp hne

private lemma exists_isOpenMap_morphismRestrict_to_spec_of_domain
    {R : Type u} [CommRing R] [IsDomain R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsFinite f]
    (η : Spec (.of R)) (hη : IsGenericPoint η (Set.univ : Set (Spec (.of R)))) :
    ∃ U : (Spec (.of R)).Opens, η ∈ U ∧ IsOpenMap (f ∣_ U) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let g := X.isoSpec.inv ≫ f
  have : IsFinite g := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  have hfinite : IsFinite (Spec.map φ) := hφ.symm ▸ inferInstance
  let : Algebra R Γ(X, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(X, ⊤) := (IsFinite.SpecMap_iff φ).mp hfinite
  obtain ⟨U, hηU, hopen⟩ :=
    exists_isOpenMap_specMap_morphismRestrict_of_domain (R := R) (B := Γ(X, ⊤)) η hη
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))) = Spec.map φ := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  have hopen' : IsOpenMap (Spec.map φ ∣_ U) :=
    Eq.mp (congrArg (fun k : Spec Γ(X, ⊤) ⟶ Spec (.of R) => IsOpenMap (k ∣_ U)) hmap)
      hopen
  have he : f ≫ (Iso.refl _).hom = X.isoSpec.hom ≫ Spec.map φ := by
    rw [hφ]
    simp [g]
  refine ⟨U, hηU, ?_⟩
  have hU : (Iso.refl (Spec (.of R))).hom ⁻¹ᵁ U = U := Scheme.Hom.id_preimage U
  exact (MorphismProperty.arrow_mk_iso_iff (P := topologically @IsOpenMap)
    (morphismRestrictEq f hU)).mp
      (isOpenMap_morphismRestrict_of_iso f (Spec.map φ)
        X.isoSpec (Iso.refl _) he U hopen')

private lemma exists_isOpenMap_specMap_morphismRestrict
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] [Module.Finite R B]
    (η : Spec (.of R)) (hη : IsGenericPoint η (Set.univ : Set (Spec (.of R)))) :
    ∃ U : (Spec (.of R)).Opens, η ∈ U ∧
      IsOpenMap (Spec.map (CommRingCat.ofHom (algebraMap R B)) ∣_ U) := by
  let : IrreducibleSpace (PrimeSpectrum R) :=
    (irreducibleSpace_def (PrimeSpectrum R)).mpr hη.isIrreducible
  let : (nilradical R).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance
  let Q := R ⧸ nilradical R
  let q : Spec (.of Q) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical R)))
  have hbij : Function.Bijective q :=
    PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical le_rfl
  have : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical R))) Ideal.Quotient.mk_surjective
  have hq : IsHomeomorph q := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨q.isClosedEmbedding.isEmbedding, hbij.2⟩
  obtain ⟨ζ, hζ⟩ := hbij.2 η
  have hgeneric : IsGenericPoint ζ (Set.univ : Set (Spec (.of Q))) := by
    apply isGenericPoint_iff_specializes.mpr
    intro y
    constructor
    · intro _; trivial
    · intro _
      apply hq.isEmbedding.isInducing.specializes_iff.mp
      rw [hζ]
      exact hη.specializes (Set.mem_univ _)
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have : IsFinite f := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  let p := pullback.fst f q
  let g := pullback.snd f q
  have : IsFinite g := inferInstance
  obtain ⟨V, hζV, hopenV⟩ :=
    exists_isOpenMap_morphismRestrict_to_spec_of_domain g ζ hgeneric
  let U : (Spec (.of R)).Opens := ⟨q '' (V : Set (Spec (.of Q))), hq.isOpenMap _ V.isOpen⟩
  have hpre : q ⁻¹ᵁ U = V := Opens.ext (Set.preimage_image_eq _ hbij.1)
  have hopen : IsOpenMap (g ∣_ q ⁻¹ᵁ U) := by rw [hpre]; exact hopenV
  have hpb := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f q)
    (US := U) (UT := q ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U)
    (UY := g ⁻¹ᵁ q ⁻¹ᵁ U) le_rfl le_rfl
    (show g ⁻¹ᵁ q ⁻¹ᵁ U = p ⁻¹ᵁ f ⁻¹ᵁ U ⊓ g ⁻¹ᵁ q ⁻¹ᵁ U by
      simp only [← Scheme.Hom.comp_preimage,
        show p ≫ f = g ≫ q from pullback.condition, inf_idem])
  have hquot : IsQuotientMap (q ∣_ U) := by
    rw [morphismRestrict_base]
    exact (hq.isOpenMap.isQuotientMap q.continuous hbij.2).restrictPreimage_isOpen U.isOpen
  dsimp only [p, g] at hpb hopen
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at hpb
  refine ⟨U, ⟨ζ, hζV, hζ⟩, ?_⟩
  exact isOpenMap_of_isPullback_of_isQuotientMap hpb hquot hopen

private lemma exists_isOpenMap_morphismRestrict_of_isFinite_of_isAffine
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [IsAffine S]
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S)) :
    ∃ U : S.Opens, η ∈ U ∧ IsOpenMap (f ∣_ U) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let R := Γ(S, ⊤)
  let B := Γ(X, ⊤)
  let : Algebra R B := f.appTop.hom.toAlgebra
  have : Module.Finite R B := f.finite_appTop
  have hgeneric : IsGenericPoint (S.isoSpec.hom η)
      (Set.univ : Set (Spec (.of R))) := by
    simpa only [Set.image_univ, S.isoSpec.hom.surjective.range_eq, closure_univ] using
      hη.image S.isoSpec.hom.continuous
  obtain ⟨V, hηV, hopen⟩ :=
    exists_isOpenMap_specMap_morphismRestrict (R := R) (B := B) (S.isoSpec.hom η) hgeneric
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap R B)) = Spec.map f.appTop := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  have hopen' : IsOpenMap (Spec.map f.appTop ∣_ V) :=
    Eq.mp (congrArg (fun k : Spec Γ(X, ⊤) ⟶ Spec Γ(S, ⊤) => IsOpenMap (k ∣_ V)) hmap)
      hopen
  refine ⟨S.isoSpec.hom ⁻¹ᵁ V, hηV, ?_⟩
  exact isOpenMap_morphismRestrict_of_iso f (Spec.map f.appTop) X.isoSpec S.isoSpec
    (Scheme.isoSpec_hom_naturality f).symm V hopen'

/-- A finite morphism is topologically open over some open neighbourhood of a
given generic point of its whole target. The target need not be reduced, and the
source and the generic fibre are allowed to be empty. -/
theorem Scheme.Hom.exists_isOpenMap_morphismRestrict_of_isFinite_of_isGenericPoint
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S)) :
    ∃ U : S.Opens, η ∈ U ∧ IsOpenMap (f ∣_ U) := by
  obtain ⟨A, hA, hηA, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := η) (U := ⊤) trivial
  have : IsAffine A.toScheme := hA
  have hgeneric : IsGenericPoint (⟨η, hηA⟩ : A) (Set.univ : Set A) := by
    apply isGenericPoint_iff_specializes.mpr
    intro y
    constructor
    · intro _; trivial
    · intro _
      exact A.ι.isOpenEmbedding.isInducing.specializes_iff.mp
        (hη.specializes (Set.mem_univ y.1))
  obtain ⟨V, hηV, hopen⟩ :=
    exists_isOpenMap_morphismRestrict_of_isFinite_of_isAffine (f ∣_ A) ⟨η, hηA⟩ hgeneric
  refine ⟨A.ι ''ᵁ V, ?_, ?_⟩
  · exact ⟨⟨η, hηA⟩, hηV, rfl⟩
  · exact (MorphismProperty.arrow_mk_iso_iff
      (P := topologically @IsOpenMap)
      (morphismRestrictRestrict f A V)).mp hopen

end AlgebraicGeometry
