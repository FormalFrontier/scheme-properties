/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.PID
public import SchemeProperties.NormalValuationStalk
public import SchemePropertiesTest.ProjectiveLineCoordinates

/-!
# A disconnected normal arithmetic curve

The spectrum of `ℤ × ℤ` is covered by its two open-and-closed integer components.
It is normal and locally Noetherian, and every point has coheight at most one,
but it is not integral. The principal open defined by `(2, 3)` is dense and omits
the first component's point `(2)`. The stalk at this omitted point is isomorphic
to `ℤ` localized at `(2)`, and is a discrete valuation ring.

Restricting a morphism on this source to that principal open gives a partial map
with a strictly smaller domain. Its original total morphism has the prescribed
restriction and the same rational map.

## References

The component morphisms use Mathlib's spectrum-of-a-product isomorphism, and the
stalk calculation uses its open-immersion stalk isomorphisms and affine stalk
identification. Dimension bounds use the principal-ideal-ring dimension theorem;
the discrete valuation ring calculation uses the Dedekind-domain localization
criterion. Normality uses the stalk definition in `SchemeProperties.Normal`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace SchemePropertiesTest.DisconnectedNormalCurve

noncomputable section

/-- The integer base scheme. -/
abbrev base : Scheme := Spec (.of ℤ)

/-- The spectrum of the product of two copies of the integers. -/
abbrev source : Scheme := Spec (.of (ℤ × ℤ))

/-- The structure morphism induced by the diagonal map on integers. -/
def structureMap : source ⟶ base :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom (ℤ × ℤ)))

instance source_over_base : source.Over base := .ofHom structureMap

/-- The first integer component of the product spectrum. -/
def firstComponent : base ⟶ source :=
  Spec.map (CommRingCat.ofHom (RingHom.fst ℤ ℤ))

/-- The second integer component of the product spectrum. -/
def secondComponent : base ⟶ source :=
  Spec.map (CommRingCat.ofHom (RingHom.snd ℤ ℤ))

instance firstComponent_isOpenImmersion : IsOpenImmersion firstComponent := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.fst ℤ ℤ)))
  rw [← coprodSpec_inl ℤ ℤ]
  infer_instance

instance secondComponent_isOpenImmersion : IsOpenImmersion secondComponent := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.snd ℤ ℤ)))
  rw [← coprodSpec_inr ℤ ℤ]
  infer_instance

/-- Every point is on one of the two integer components. -/
theorem point_cases (x : source) :
    (∃ z : base, firstComponent z = x) ∨ (∃ z : base, secondComponent z = x) := by
  have hinv : coprodSpec ℤ ℤ (inv (coprodSpec ℤ ℤ) x) = x := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    simp
  obtain ⟨z | z, hz⟩ := (coprodMk base base).surjective (inv (coprodSpec ℤ ℤ) x)
  · refine Or.inl ⟨z, ?_⟩
    have h := congrArg (coprodSpec ℤ ℤ) hz
    rw [coprodMk_inl, ← Scheme.Hom.comp_apply, coprodSpec_inl, hinv] at h
    exact h
  · refine Or.inr ⟨z, ?_⟩
    have h := congrArg (coprodSpec ℤ ℤ) hz
    rw [coprodMk_inr, ← Scheme.Hom.comp_apply, coprodSpec_inr, hinv] at h
    exact h

instance source_isNormal : IsNormal source where
  stalk_isDomain x := by
    rcases point_cases x with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact (asIso (firstComponent.stalkMap z)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
    · exact (asIso (secondComponent.stalkMap z)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  stalk_isIntegrallyClosed x := by
    rcases point_cases x with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact IsIntegrallyClosed.of_equiv
        (asIso (firstComponent.stalkMap z)).symm.commRingCatIsoToRingEquiv
    · exact IsIntegrallyClosed.of_equiv
        (asIso (secondComponent.stalkMap z)).symm.commRingCatIsoToRingEquiv

instance source_isLocallyNoetherian : IsLocallyNoetherian source := inferInstance

/-- The two orthogonal nonzero idempotents prevent integrality of the source. -/
theorem source_not_isIntegral : ¬ IsIntegral source := by
  intro h
  letI : IsDomain (ℤ × ℤ) := (affine_isIntegral_iff (.of (ℤ × ℤ))).mp h
  have hmul : ((1, 0) : ℤ × ℤ) * (0, 1) = 0 := by ext <;> simp
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · exact one_ne_zero (congrArg Prod.fst hzero)
  · exact one_ne_zero (congrArg Prod.snd hzero)

private theorem integer_coheight_le_one (z : base) : Order.coheight z ≤ 1 := by
  haveI : z.asIdeal.IsPrime := z.isPrime
  have hdim : ringKrullDim ℤ ≤ 1 := Ring.krullDimLE_iff.mp inferInstance
  have hheight : z.asIdeal.height ≤ 1 := by
    exact_mod_cast z.asIdeal.height_le_ringKrullDim_of_isPrime.trans hdim
  rwa [idealHeight_eq_coheight] at hheight

/-- All points have coheight at most one, including points on either component. -/
theorem coheight_le_one (x : source) : Order.coheight x ≤ 1 := by
  rcases point_cases x with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · rw [coheight_eq_of_isOpenImmersion firstComponent]
    exact integer_coheight_le_one z
  · rw [coheight_eq_of_isOpenImmersion secondComponent]
    exact integer_coheight_le_one z

/-- The disconnected arithmetic source has absolute dimension at most one. -/
instance source_krullDimLE_one : Order.KrullDimLE 1 source where
  krullDim_le := by
    rw [Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun x => ?_
    exact_mod_cast coheight_le_one x

/-- The section whose principal open will be the domain of restriction. -/
def denominator : ℤ × ℤ := (2, 3)

/-- The principal open `D((2, 3))` in the product spectrum. -/
def denseOpen : source.Opens := PrimeSpectrum.basicOpen denominator

@[simp]
theorem firstComponent_preimage_denseOpen :
    firstComponent ⁻¹ᵁ denseOpen = PrimeSpectrum.basicOpen (2 : ℤ) := by
  ext z
  rfl

@[simp]
theorem secondComponent_preimage_denseOpen :
    secondComponent ⁻¹ᵁ denseOpen = PrimeSpectrum.basicOpen (3 : ℤ) := by
  ext z
  rfl

/-- The principal open is dense on both components, hence on the whole source. -/
theorem dense_denseOpen : Dense (denseOpen : Set source) := by
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨x, hx⟩
  rcases point_cases x with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · have hD : Dense ((firstComponent ⁻¹ᵁ denseOpen) : Set base) := by
      apply (firstComponent ⁻¹ᵁ denseOpen).isOpen.dense
      let z : base := ⟨⊥, Ideal.isPrime_bot⟩
      refine ⟨z, ?_⟩
      change (2 : CommRingCat.of ℤ) ∉ (⊥ : Ideal (CommRingCat.of ℤ))
      simpa only [Ideal.mem_bot] using Int.prime_two.ne_zero
    obtain ⟨w, hwU, hwD⟩ := hD.inter_open_nonempty (firstComponent ⁻¹' U)
      (hU.preimage firstComponent.continuous) ⟨z, hx⟩
    exact ⟨firstComponent w, hwU, hwD⟩
  · have hD : Dense ((secondComponent ⁻¹ᵁ denseOpen) : Set base) := by
      apply (secondComponent ⁻¹ᵁ denseOpen).isOpen.dense
      let z : base := ⟨⊥, Ideal.isPrime_bot⟩
      refine ⟨z, ?_⟩
      change (3 : CommRingCat.of ℤ) ∉ (⊥ : Ideal (CommRingCat.of ℤ))
      norm_num
    obtain ⟨w, hwU, hwD⟩ := hD.inter_open_nonempty (secondComponent ⁻¹' U)
      (hU.preimage secondComponent.continuous) ⟨z, hx⟩
    exact ⟨secondComponent w, hwU, hwD⟩

/-- The prime `(2)` of the integer spectrum. -/
def integerTwo : base :=
  ⟨Ideal.span {(2 : ℤ)},
    (Ideal.span_singleton_prime Int.prime_two.ne_zero).mpr Int.prime_two⟩

/-- The first component's point `(2)`, omitted by `D((2, 3))`. -/
def omittedPoint : source := firstComponent integerTwo

/-- Its prime ideal is `(2) × ℤ`. -/
theorem omittedPoint_asIdeal :
    omittedPoint.asIdeal = (Ideal.span {(2 : ℤ)}).prod ⊤ := by
  change Ideal.comap (RingHom.fst ℤ ℤ) (Ideal.span {(2 : ℤ)}) = _
  ext r
  simp [Ideal.prod]

/-- The chosen point does not belong to the dense principal open. -/
theorem omittedPoint_not_mem_denseOpen : omittedPoint ∉ denseOpen := by
  change ¬ ¬ ((2 : ℤ) ∈ Ideal.span {(2 : ℤ)})
  exact not_not_intro (Ideal.subset_span (Set.mem_singleton (2 : ℤ)))

/-- The dense open is strictly smaller than the whole source. -/
theorem denseOpen_lt_top : denseOpen < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro h
  exact omittedPoint_not_mem_denseOpen
    (h.symm ▸ (show omittedPoint ∈ (⊤ : source.Opens) from trivial))

/-- The omitted point has coheight exactly one. -/
theorem omittedPoint_coheight : Order.coheight omittedPoint = 1 := by
  rw [omittedPoint, coheight_eq_of_isOpenImmersion firstComponent,
    ← idealHeight_eq_coheight]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr Int.prime_two.ne_zero)
    Int.prime_two.not_isUnit

private instance integerTwo_isPrime : integerTwo.asIdeal.IsPrime := integerTwo.isPrime

/-- The stalk at the omitted point is the localization of `ℤ` at `(2)`. -/
def omittedPointStalkIso : source.presheaf.stalk omittedPoint ≅
    CommRingCat.of (@Localization.AtPrime (CommRingCat.of ℤ) _
      integerTwo.asIdeal integerTwo.isPrime) := by
  have h : ∀ z : base, IsIso (firstComponent.stalkMap z) := fun z => inferInstance
  haveI : IsIso (firstComponent.stalkMap integerTwo) := h integerTwo
  exact (asIso (firstComponent.stalkMap integerTwo) :
    source.presheaf.stalk (firstComponent integerTwo) ≅ base.presheaf.stalk integerTwo) ≪≫
      Spec.stalkIso (.of ℤ) integerTwo

private theorem twoIdeal_ne_bot : Ideal.span {(2 : ℤ)} ≠ ⊥ := by
  intro h
  have htwo : (2 : ℤ) ∈ Ideal.span {(2 : ℤ)} :=
    Ideal.subset_span (Set.mem_singleton (2 : ℤ))
  rw [h, Ideal.mem_bot] at htwo
  exact Int.prime_two.ne_zero htwo

instance omittedPoint_stalk_isDiscreteValuationRing :
    IsDiscreteValuationRing (source.presheaf.stalk omittedPoint) := by
  have : integerTwo.asIdeal.IsPrime := integerTwo.isPrime
  have hP : integerTwo.asIdeal ≠ ⊥ := by
    change Ideal.span {(2 : ℤ)} ≠ ⊥
    exact twoIdeal_ne_bot
  letI : IsDiscreteValuationRing (Localization.AtPrime integerTwo.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      ℤ hP _
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    omittedPointStalkIso.symm.commRingCatIsoToRingEquiv

/-- The normal coheight criterion applies to the omitted point's domain stalk. -/
theorem omittedPoint_stalk_valuationRing :
    ValuationRing (source.presheaf.stalk omittedPoint) :=
  valuationRing_stalk_of_coheight_le_one omittedPoint omittedPoint_coheight.le

section Restriction

variable {Y : Scheme}

/-- Restriction of a morphism from the product spectrum to `D((2, 3))`. -/
def restrictedMap (f : source ⟶ Y) : source.PartialMap Y :=
  f.toPartialMap.restrict denseOpen dense_denseOpen le_top

@[simp]
theorem restrictedMap_domain (f : source ⟶ Y) : (restrictedMap f).domain = denseOpen := rfl

@[simp]
theorem restrictedMap_hom (f : source ⟶ Y) : (restrictedMap f).hom = denseOpen.ι ≫ f := by
  simp [restrictedMap, Scheme.PartialMap.restrict, Scheme.Hom.toPartialMap]

/-- The total representative contains the omitted point. -/
theorem omittedPoint_mem_total_domain (f : source ⟶ Y) :
    omittedPoint ∈ f.toPartialMap.domain := trivial

/-- The partial representative does not contain the omitted point. -/
theorem omittedPoint_not_mem_restricted_domain (f : source ⟶ Y) :
    omittedPoint ∉ (restrictedMap f).domain := omittedPoint_not_mem_denseOpen

/-- The total representative restricts to the specified partial morphism. -/
theorem total_restrict_readback (f : source ⟶ Y) :
    source.homOfLE (show (restrictedMap f).domain ≤ f.toPartialMap.domain from le_top) ≫
      f.toPartialMap.hom = (restrictedMap f).hom := rfl

/-- Restriction preserves the rational map represented by the original morphism. -/
theorem restrictedMap_toRationalMap (f : source ⟶ Y) :
    (restrictedMap f).toRationalMap = f.toPartialMap.toRationalMap :=
  Scheme.PartialMap.restrict_toRationalMap _ _ _ _

variable [Y.Over base]

/-- An over-base total morphism gives an over-base partial morphism on this open. -/
theorem restrictedMap_isOver (f : source ⟶ Y) [f.IsOver base] :
    (restrictedMap f).IsOver base := by
  dsimp only [Scheme.PartialMap.IsOver, restrictedMap_domain]
  rw [restrictedMap_hom]
  constructor
  calc
    (denseOpen.ι ≫ f) ≫ (Y ↘ base) =
        denseOpen.ι ≫ (f ≫ (Y ↘ base)) := Category.assoc _ _ _
    _ = denseOpen.ι ≫ (source ↘ base) := by rw [CategoryTheory.comp_over f base]
    _ = denseOpen.toScheme ↘ base := denseOpen.ι_comp_over base

/-- The structure-map equation holds on the whole partial domain. -/
theorem restrictedMap_over (f : source ⟶ Y) [f.IsOver base] :
    (restrictedMap f).hom ≫ (Y ↘ base) = (restrictedMap f).domain.ι ≫ structureMap := by
  have : (restrictedMap f).IsOver base := restrictedMap_isOver f
  exact CategoryTheory.comp_over (restrictedMap f).hom base

end Restriction

/-- The independently constructed projective-line morphism `[1:(2,3)]`. -/
def globalMap : source ⟶ ProjectiveLineCoordinates.target :=
  ProjectiveLineCoordinates.point

instance globalMap_isOver : globalMap.IsOver base :=
  ProjectiveLineCoordinates.point_isOver

/-- The projective-line morphism is over the integer spectrum. -/
theorem globalMap_over :
    globalMap ≫ ProjectiveLineCoordinates.structureMap = structureMap :=
  ProjectiveLineCoordinates.point_structureMap

/-- The projective-line partial map with strict dense domain `D((2,3))`. -/
def partialMap : source.PartialMap ProjectiveLineCoordinates.target :=
  restrictedMap globalMap

/-- Its structure-map equation holds on the whole dense domain. -/
theorem partialMap_over :
    partialMap.hom ≫ ProjectiveLineCoordinates.structureMap =
      partialMap.domain.ι ≫ structureMap :=
  restrictedMap_over globalMap

end

end SchemePropertiesTest.DisconnectedNormalCurve
