/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.Integral
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Field.Equiv
public import Mathlib.Algebra.Field.ZMod
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

namespace AlgebraicGeometry.IntProdZModFour

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

/-- The spectrum of `ℤ × ZMod 4`. -/
@[expose] public def scheme : Scheme := Spec (.of (ℤ × ZMod 4))

/-- The ambient scheme is the canonical spectrum of `ℤ × ZMod 4`. -/
public theorem scheme_eq : scheme = Spec (.of (ℤ × ZMod 4)) := rfl

private def integerComponentInclusion : Spec (.of ℤ) ⟶ scheme :=
  Spec.map (CommRingCat.ofHom (RingHom.fst ℤ (ZMod 4)))

/-- The point over `(2)` on the integer component of `Spec (ℤ × ZMod 4)`. -/
@[expose] public def twoPoint : scheme :=
  PrimeSpectrum.comap (RingHom.fst ℤ (ZMod 4))
    ⟨RingHom.ker (Int.castRingHom (ZMod 2)), RingHom.ker_isPrime _⟩

/-- The point is the comap of the kernel of reduction modulo two along the first projection. -/
public theorem twoPoint_eq :
    twoPoint = PrimeSpectrum.comap (RingHom.fst ℤ (ZMod 4))
      ⟨RingHom.ker (Int.castRingHom (ZMod 2)), RingHom.ker_isPrime _⟩ := rfl

/-- The prime ideal of the point over `(2)` is the inverse image of the integer kernel. -/
public theorem twoPoint_asIdeal :
    twoPoint.asIdeal =
      Ideal.comap (RingHom.fst ℤ (ZMod 4)) (RingHom.ker (Int.castRingHom (ZMod 2))) := rfl

/-- The basic open `D((1, 0))` in `Spec (ℤ × ZMod 4)`. -/
@[expose] public def integerOpen : scheme.Opens :=
  PrimeSpectrum.basicOpen ((1, 0) : ℤ × ZMod 4)

/-- The integer-component open is the distinguished open of the first idempotent. -/
public theorem integerOpen_eq :
    integerOpen = PrimeSpectrum.basicOpen ((1, 0) : ℤ × ZMod 4) := rfl

/-- Membership in the integer component means that its idempotent avoids the prime ideal. -/
public theorem mem_integerOpen (p : scheme) :
    p ∈ integerOpen ↔ ((1, 0) : ℤ × ZMod 4) ∉ p.asIdeal :=
  PrimeSpectrum.mem_basicOpen ((1, 0) : ℤ × ZMod 4) p

private theorem scheme_isLocallyNoetherian : IsLocallyNoetherian scheme := by
  change IsLocallyNoetherian (Spec (.of (ℤ × ZMod 4)))
  infer_instance

private theorem integerComponentInclusion_isOpenImmersion :
    IsOpenImmersion integerComponentInclusion := by
  let := (RingHom.fst ℤ (ZMod 4)).toAlgebra
  exact IsOpenImmersion.of_isLocalization ((1, 0) : ℤ × ZMod 4)

private theorem integerComponentInclusion_range :
    Set.range integerComponentInclusion = (integerOpen : Set scheme) := by
  let := (RingHom.fst ℤ (ZMod 4)).toAlgebra
  change Set.range (PrimeSpectrum.comap (RingHom.fst ℤ (ZMod 4))) =
    (PrimeSpectrum.basicOpen ((1, 0) : ℤ × ZMod 4) : Set (PrimeSpectrum (ℤ × ZMod 4)))
  exact PrimeSpectrum.localization_away_comap_range ℤ ((1, 0) : ℤ × ZMod 4)

private theorem twoPoint_mem_integerOpen : twoPoint ∈ integerOpen := by
  rw [mem_integerOpen, twoPoint_asIdeal]
  change (1 : ℤ) ∉ integerClosedPoint.asIdeal
  exact integerClosedPoint.asIdeal.one_notMem

private theorem integerOpen_isIntegral : IsIntegral integerOpen.toScheme := by
  let : IsOpenImmersion integerComponentInclusion :=
    integerComponentInclusion_isOpenImmersion
  have hrange : integerComponentInclusion.opensRange = integerOpen :=
    SetLike.ext' integerComponentInclusion_range
  have hIntegral : IsIntegral integerComponentInclusion.opensRange.toScheme :=
    IsIntegral.of_isIso integerComponentInclusion.isoOpensRange.hom
  simpa only [hrange] using hIntegral

private theorem integerClosedPoint_stalk_isDomain :
    IsDomain ((Spec (.of ℤ)).presheaf.stalk integerClosedPoint) := by
  let : integerClosedPoint.asIdeal.IsPrime := integerClosedPoint.isPrime
  exact (Spec.stalkIso (.of ℤ) integerClosedPoint).commRingCatIsoToRingEquiv.toMulEquiv.isDomain
    (Localization.AtPrime integerClosedPoint.asIdeal)

private theorem twoPoint_stalk_isDomain :
    IsDomain (scheme.presheaf.stalk twoPoint) := by
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

private theorem twoPoint_stalk_not_isField :
    ¬ IsField (scheme.presheaf.stalk twoPoint) := by
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

private theorem twoPoint_isClosed : IsClosed ({twoPoint} : Set scheme) := by
  let : integerClosedPoint.asIdeal.IsMaximal := integerClosedPoint_isMaximal
  change IsClosed ({PrimeSpectrum.comap (RingHom.fst ℤ (ZMod 4)) integerClosedPoint} :
    Set (PrimeSpectrum (ℤ × ZMod 4)))
  rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  exact Ideal.comap_isMaximal_of_surjective _ Prod.fst_surjective

private theorem scheme_not_isReduced : ¬ AlgebraicGeometry.IsReduced scheme := by
  intro hReduced
  have hRing : _root_.IsReduced (ℤ × ZMod 4) :=
    (affine_isReduced_iff (.of (ℤ × ZMod 4))).mp hReduced
  have hnil : IsNilpotent (((0 : ℤ), (2 : ZMod 4)) : ℤ × ZMod 4) := ⟨2, by decide⟩
  have hzero := congrArg Prod.snd (hRing.eq_zero _ hnil)
  exact (by decide : (2 : ZMod 4) ≠ 0) hzero

private theorem integerOpen_isClopen :
    IsClopen (integerOpen : Set scheme) := by
  exact PrimeSpectrum.isClopen_basicOpen_of_mul_add
    ((1, 0) : ℤ × ZMod 4) ((0, 1) : ℤ × ZMod 4)
    (by ext <;> simp) (by ext <;> simp)

private theorem integerOpen_ne_top : integerOpen ≠ ⊤ := by
  let : Nontrivial (ZMod 4) := ⟨0, 1, by decide⟩
  let q : PrimeSpectrum (ZMod 4) := Classical.choice inferInstance
  intro htop
  have hmem : PrimeSpectrum.comap (RingHom.snd ℤ (ZMod 4)) q ∈ integerOpen := by
    rw [htop]
    trivial
  change (0 : ZMod 4) ∉ q.asIdeal at hmem
  exact hmem q.asIdeal.zero_mem

private theorem scheme_not_preconnected : ¬ PreconnectedSpace scheme := by
  intro hConnected
  let := hConnected
  rcases isClopen_iff.mp integerOpen_isClopen with hempty | huniv
  · have hmem : twoPoint ∈ (∅ : Set scheme) :=
      hempty ▸ twoPoint_mem_integerOpen
    exact Set.notMem_empty twoPoint hmem
  · exact integerOpen_ne_top (SetLike.ext' huniv)

/-- The integer component is an integral neighborhood of a closed point with a nonfield
domain stalk, inside a locally Noetherian, nonreduced scheme that is not preconnected. -/
public theorem integerOpen_properties :
    IsLocallyNoetherian scheme ∧
      IsDomain (scheme.presheaf.stalk twoPoint) ∧
      twoPoint ∈ integerOpen ∧
      IsIntegral integerOpen.toScheme ∧
      ¬ AlgebraicGeometry.IsReduced scheme ∧
      ¬ PreconnectedSpace scheme ∧
      ¬ IsField (scheme.presheaf.stalk twoPoint) ∧
      IsClosed ({twoPoint} : Set scheme) :=
  ⟨scheme_isLocallyNoetherian, twoPoint_stalk_isDomain,
    twoPoint_mem_integerOpen, integerOpen_isIntegral,
    scheme_not_isReduced, scheme_not_preconnected,
    twoPoint_stalk_not_isField, twoPoint_isClosed⟩

private theorem scheme_exists_isIntegral_open :
    ∃ U : scheme.Opens, twoPoint ∈ U ∧ IsIntegral U.toScheme := by
  let : IsLocallyNoetherian scheme := integerOpen_properties.1
  let : IsDomain (scheme.presheaf.stalk twoPoint) := integerOpen_properties.2.1
  exact exists_isIntegral_open_of_isDomain_stalk scheme twoPoint

private theorem scheme_isOpen_setOf_isDomain_stalk :
    IsOpen {x : scheme | IsDomain (scheme.presheaf.stalk x)} := by
  let : IsLocallyNoetherian scheme := integerOpen_properties.1
  exact isOpen_setOf_isDomain_stalk scheme

end AlgebraicGeometry.IntProdZModFour
