/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.Integral
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.ZMod
import Mathlib.Topology.Connected.Clopen

/-!
# An integral neighborhood in a disconnected, nonreduced scheme

In `Spec (ℤ × ZMod 4)`, the point induced by the closed prime `(2)` of `ℤ`
has a domain stalk which is not a field. Its specified basic-open neighborhood
`D((1, 0))` is integral, although the ambient scheme is nonreduced and not even
preconnected.

The neighborhood and the stalk are calculated independently of any theorem
spreading a domain-stalk condition. The projection to `ℤ` is a localization away
from `(1, 0)` by Mathlib's `IsLocalization.away_fst`; its Spec map identifies
`Spec ℤ` with this basic open. The scheme-level transports use the stock
open-immersion and stalk-isomorphism APIs, not a new localization construction.

The ambient nilpotent calculation follows the existing mixed-product example in
`SchemePropertiesExamples.ReducedLocus`, with `ℤ` replacing its field factor.
-/

noncomputable section

open CategoryTheory Set TopologicalSpace
open AlgebraicGeometry

namespace SchemePropertiesExamples

private def integerClosedPoint : PrimeSpectrum ℤ :=
  ⟨RingHom.ker (Int.castRingHom (ZMod 2)), RingHom.ker_isPrime _⟩

private theorem integerClosedPoint_ideal :
    integerClosedPoint.asIdeal = Ideal.span ({(2 : ℤ)} : Set ℤ) :=
  ZMod.ker_intCastRingHom 2

private theorem integerClosedPoint_isMaximal : integerClosedPoint.asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (Int.castRingHom (ZMod 2)) ZMod.intCast_surjective

private theorem two_mem_integerClosedPoint : (2 : ℤ) ∈ integerClosedPoint.asIdeal := by
  rw [integerClosedPoint_ideal]
  exact Ideal.subset_span (by simp)

private def mixedScheme : Scheme := Spec (.of (ℤ × ZMod 4))

private def integerComponentInclusion : Spec (.of ℤ) ⟶ mixedScheme :=
  Spec.map (CommRingCat.ofHom (RingHom.fst ℤ (ZMod 4)))

private def domainPoint : mixedScheme := integerComponentInclusion integerClosedPoint

private def integralNeighborhood : mixedScheme.Opens :=
  PrimeSpectrum.basicOpen ((1, 0) : ℤ × ZMod 4)

private theorem mixedScheme_isLocallyNoetherian : IsLocallyNoetherian mixedScheme := by
  change IsLocallyNoetherian (Spec (.of (ℤ × ZMod 4)))
  infer_instance

private theorem integerComponentInclusion_isOpenImmersion :
    IsOpenImmersion integerComponentInclusion := by
  let := (RingHom.fst ℤ (ZMod 4)).toAlgebra
  exact IsOpenImmersion.of_isLocalization ((1, 0) : ℤ × ZMod 4)

private theorem integerComponentInclusion_range :
    Set.range integerComponentInclusion = (integralNeighborhood : Set mixedScheme) := by
  let := (RingHom.fst ℤ (ZMod 4)).toAlgebra
  change Set.range (PrimeSpectrum.comap (RingHom.fst ℤ (ZMod 4))) =
    (PrimeSpectrum.basicOpen ((1, 0) : ℤ × ZMod 4) : Set (PrimeSpectrum (ℤ × ZMod 4)))
  exact PrimeSpectrum.localization_away_comap_range ℤ ((1, 0) : ℤ × ZMod 4)

private theorem domainPoint_mem_integralNeighborhood : domainPoint ∈ integralNeighborhood := by
  change (1 : ℤ) ∉ integerClosedPoint.asIdeal
  exact integerClosedPoint.asIdeal.one_notMem

private theorem integralNeighborhood_isIntegral : IsIntegral integralNeighborhood.toScheme := by
  let : IsOpenImmersion integerComponentInclusion :=
    integerComponentInclusion_isOpenImmersion
  have hrange : integerComponentInclusion.opensRange = integralNeighborhood :=
    SetLike.ext' integerComponentInclusion_range
  have hIntegral : IsIntegral integerComponentInclusion.opensRange.toScheme :=
    IsIntegral.of_isIso integerComponentInclusion.isoOpensRange.hom
  simpa only [hrange] using hIntegral

private theorem integerClosedPoint_stalk_isDomain :
    IsDomain ((Spec (.of ℤ)).presheaf.stalk integerClosedPoint) := by
  let : integerClosedPoint.asIdeal.IsPrime := integerClosedPoint.isPrime
  exact (Spec.stalkIso (.of ℤ) integerClosedPoint).commRingCatIsoToRingEquiv.toMulEquiv.isDomain
    (Localization.AtPrime integerClosedPoint.asIdeal)

private theorem domainPoint_stalk_isDomain :
    IsDomain (mixedScheme.presheaf.stalk domainPoint) := by
  let : IsIso (integerComponentInclusion.stalkMap integerClosedPoint) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp
      integerComponentInclusion_isOpenImmersion).2 integerClosedPoint
  let := integerClosedPoint_stalk_isDomain
  let e := asIso (integerComponentInclusion.stalkMap integerClosedPoint)
  exact e.commRingCatIsoToRingEquiv.toMulEquiv.isDomain
    ((Spec (.of ℤ)).presheaf.stalk integerClosedPoint)

private theorem integerClosedPoint_localization_not_isField :
    ¬ IsField (Localization.AtPrime integerClosedPoint.asIdeal) := by
  let : integerClosedPoint.asIdeal.IsPrime := integerClosedPoint.isPrime
  intro hField
  have htwo : algebraMap ℤ (Localization.AtPrime integerClosedPoint.asIdeal) 2 ≠ 0 := by
    intro hzero
    apply (by decide : (2 : ℤ) ≠ 0)
    apply IsLocalization.injective (Localization.AtPrime integerClosedPoint.asIdeal)
      integerClosedPoint.asIdeal.primeCompl_le_nonZeroDivisors
    exact hzero.trans (map_zero _).symm
  have hunit : IsUnit (algebraMap ℤ (Localization.AtPrime integerClosedPoint.asIdeal) 2) :=
    isUnit_iff_exists_inv.mpr (hField.mul_inv_cancel htwo)
  have hout := (IsLocalization.AtPrime.isUnit_to_map_iff
    (Localization.AtPrime integerClosedPoint.asIdeal) integerClosedPoint.asIdeal 2).mp hunit
  exact hout two_mem_integerClosedPoint

private theorem domainPoint_stalk_not_isField :
    ¬ IsField (mixedScheme.presheaf.stalk domainPoint) := by
  let : IsIso (integerComponentInclusion.stalkMap integerClosedPoint) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp
      integerComponentInclusion_isOpenImmersion).2 integerClosedPoint
  let e := asIso (integerComponentInclusion.stalkMap integerClosedPoint)
  intro hField
  have hInteger : IsField ((Spec (.of ℤ)).presheaf.stalk integerClosedPoint) :=
    e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isField hField
  apply integerClosedPoint_localization_not_isField
  exact MulEquiv.isField hInteger
    (Spec.stalkIso (.of ℤ) integerClosedPoint).symm.commRingCatIsoToRingEquiv.toMulEquiv

private theorem domainPoint_isClosed : IsClosed ({domainPoint} : Set mixedScheme) := by
  let : integerClosedPoint.asIdeal.IsMaximal := integerClosedPoint_isMaximal
  change IsClosed ({PrimeSpectrum.comap (RingHom.fst ℤ (ZMod 4)) integerClosedPoint} :
    Set (PrimeSpectrum (ℤ × ZMod 4)))
  rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  exact Ideal.comap_isMaximal_of_surjective _ Prod.fst_surjective

private theorem mixedScheme_not_isReduced : ¬ AlgebraicGeometry.IsReduced mixedScheme := by
  intro hReduced
  have hRing : _root_.IsReduced (ℤ × ZMod 4) :=
    (affine_isReduced_iff (.of (ℤ × ZMod 4))).mp hReduced
  have hnil : IsNilpotent (((0 : ℤ), (2 : ZMod 4)) : ℤ × ZMod 4) := ⟨2, by decide⟩
  have hzero := congrArg Prod.snd (hRing.eq_zero _ hnil)
  exact (by decide : (2 : ZMod 4) ≠ 0) hzero

private theorem integralNeighborhood_isClopen :
    IsClopen (integralNeighborhood : Set mixedScheme) := by
  exact PrimeSpectrum.isClopen_basicOpen_of_mul_add
    ((1, 0) : ℤ × ZMod 4) ((0, 1) : ℤ × ZMod 4)
    (by ext <;> simp) (by ext <;> simp)

private theorem integralNeighborhood_ne_top : integralNeighborhood ≠ ⊤ := by
  let : Nontrivial (ZMod 4) := ⟨0, 1, by decide⟩
  let q : PrimeSpectrum (ZMod 4) := Classical.choice inferInstance
  intro htop
  have hmem : PrimeSpectrum.comap (RingHom.snd ℤ (ZMod 4)) q ∈ integralNeighborhood := by
    rw [htop]
    trivial
  change (0 : ZMod 4) ∉ q.asIdeal at hmem
  exact hmem q.asIdeal.zero_mem

private theorem mixedScheme_not_preconnected : ¬ PreconnectedSpace mixedScheme := by
  intro hConnected
  let := hConnected
  rcases isClopen_iff.mp integralNeighborhood_isClopen with hempty | huniv
  · have hmem : domainPoint ∈ (∅ : Set mixedScheme) :=
      hempty ▸ domainPoint_mem_integralNeighborhood
    exact Set.notMem_empty domainPoint hmem
  · exact integralNeighborhood_ne_top (SetLike.ext' huniv)

/-- A specified integral basic-open neighborhood and a nonfield domain stalk,
inside a nonreduced and disconnected locally Noetherian scheme. -/
private theorem mixedScheme_integralNeighborhood :
    IsLocallyNoetherian mixedScheme ∧
      IsDomain (mixedScheme.presheaf.stalk domainPoint) ∧
      domainPoint ∈ integralNeighborhood ∧
      IsIntegral integralNeighborhood.toScheme ∧
      ¬ AlgebraicGeometry.IsReduced mixedScheme ∧
      ¬ PreconnectedSpace mixedScheme ∧
      ¬ IsField (mixedScheme.presheaf.stalk domainPoint) ∧
      IsClosed ({domainPoint} : Set mixedScheme) :=
  ⟨mixedScheme_isLocallyNoetherian, domainPoint_stalk_isDomain,
    domainPoint_mem_integralNeighborhood, integralNeighborhood_isIntegral,
    mixedScheme_not_isReduced, mixedScheme_not_preconnected,
    domainPoint_stalk_not_isField, domainPoint_isClosed⟩

private theorem mixedScheme_exists_isIntegral_open :
    ∃ U : mixedScheme.Opens, domainPoint ∈ U ∧ IsIntegral U.toScheme := by
  let : IsLocallyNoetherian mixedScheme := mixedScheme_isLocallyNoetherian
  let : IsDomain (mixedScheme.presheaf.stalk domainPoint) := domainPoint_stalk_isDomain
  exact exists_isIntegral_open_of_isDomain_stalk mixedScheme domainPoint

private theorem mixedScheme_isOpen_setOf_isDomain_stalk :
    IsOpen {x : mixedScheme | IsDomain (mixedScheme.presheaf.stalk x)} := by
  let : IsLocallyNoetherian mixedScheme := mixedScheme_isLocallyNoetherian
  exact isOpen_setOf_isDomain_stalk mixedScheme

end SchemePropertiesExamples
