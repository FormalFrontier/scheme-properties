module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.LocalizationLocalization

public section

set_option warningAsError true

/-!
# Normal schemes

This file defines a normal scheme by requiring every local ring to be a
domain and integrally closed. It proves the basic localization, open-local,
and affine-spectrum API for this property.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v w

namespace IsLocalization.AtPrime

/-- Let `S` and `T` be localizations of `R` at prime ideals `q` and `p`
respectively. If `p ≤ q` and `S` is a domain, then `T` is a domain. -/
theorem isDomain_of_le
    {R : Type u} (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    [IsLocalization.AtPrime S q] [IsLocalization.AtPrime T p]
    (hpq : p ≤ q) [IsDomain S] : IsDomain T := by
  have hcompl : q.primeCompl ≤ p.primeCompl := by
    intro r hrq hrp
    exact hrq (hpq hrp)
  let _ : Algebra S T :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      S T q.primeCompl p.primeCompl hcompl
  let _ : IsScalarTower R S T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      S T q.primeCompl p.primeCompl hcompl
  let _ : IsLocalization (p.primeCompl.map (algebraMap R S)) T :=
    IsLocalization.isLocalization_of_submonoid_le
      S T q.primeCompl p.primeCompl hcompl
  let _ : Nontrivial T := IsLocalization.AtPrime.nontrivial T p
  have hregular : p.primeCompl.map (algebraMap R S) ≤ nonZeroDivisors S := by
    intro z hz
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hz0
    have hzunit := IsLocalization.map_units T ⟨z, hz⟩
    change IsUnit ((algebraMap S T) z) at hzunit
    rw [hz0, map_zero, isUnit_zero_iff] at hzunit
    exact zero_ne_one hzunit
  exact IsLocalization.isDomain_of_le_nonZeroDivisors T hregular

/-- Let `S` and `T` be localizations of `R` at prime ideals `q` and `p`
respectively. If `p ≤ q` and `S` is an integrally closed domain, then `T` is
integrally closed. -/
theorem isIntegrallyClosed_of_le
    {R : Type u} (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    [IsLocalization.AtPrime S q] [IsLocalization.AtPrime T p]
    (hpq : p ≤ q) [IsDomain S] [IsIntegrallyClosed S] : IsIntegrallyClosed T := by
  have hcompl : q.primeCompl ≤ p.primeCompl := by
    intro r hrq hrp
    exact hrq (hpq hrp)
  let _ : Algebra S T :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      S T q.primeCompl p.primeCompl hcompl
  let _ : IsScalarTower R S T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      S T q.primeCompl p.primeCompl hcompl
  let _ : IsLocalization (p.primeCompl.map (algebraMap R S)) T :=
    IsLocalization.isLocalization_of_submonoid_le
      S T q.primeCompl p.primeCompl hcompl
  let _ : Nontrivial T := IsLocalization.AtPrime.nontrivial T p
  have hregular : p.primeCompl.map (algebraMap R S) ≤ nonZeroDivisors S := by
    intro z hz
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hz0
    have hzunit := IsLocalization.map_units T ⟨z, hz⟩
    change IsUnit ((algebraMap S T) z) at hzunit
    rw [hz0, map_zero, isUnit_zero_iff] at hzunit
    exact zero_ne_one hzunit
  exact isIntegrallyClosed_of_isLocalization T _ hregular

end IsLocalization.AtPrime

/-- A commutative ring is locally normal if every localization at a prime ideal
is a domain and integrally closed. Unlike the conjunction of `IsDomain` and
`IsIntegrallyClosed`, this interface also accommodates disconnected rings. -/
class IsLocallyNormalRing (R : Type u) [CommRing R] : Prop where
  isDomain_atPrime (p : PrimeSpectrum R) : IsDomain (Localization.AtPrime p.asIdeal)
  isIntegrallyClosed_atPrime (p : PrimeSpectrum R) :
    IsIntegrallyClosed (Localization.AtPrime p.asIdeal)

attribute [instance] IsLocallyNormalRing.isDomain_atPrime
  IsLocallyNormalRing.isIntegrallyClosed_atPrime

/-- An integrally closed domain is locally normal. -/
instance isLocallyNormalRing_of_isDomain (R : Type u) [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] : IsLocallyNormalRing R where
  isDomain_atPrime p := IsLocalization.isDomain_of_atPrime _ p.asIdeal
  isIntegrallyClosed_atPrime p :=
    isIntegrallyClosed_of_isLocalization _ p.asIdeal.primeCompl
      p.asIdeal.primeCompl_le_nonZeroDivisors

/-- Local normality is preserved by ring equivalences. -/
theorem IsLocallyNormalRing.of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) [IsLocallyNormalRing R] : IsLocallyNormalRing S := by
  constructor
  · intro p
    let _ : IsDomain (Localization.AtPrime (p.asIdeal.comap e)) :=
      IsLocallyNormalRing.isDomain_atPrime ⟨p.asIdeal.comap e, inferInstance⟩
    exact (IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime (p.asIdeal.comap e)) (Localization.AtPrime p.asIdeal)
      e (e.map_primeCompl_comap_eq p.asIdeal)).symm.toMulEquiv.isDomain _
  · intro p
    let _ : IsIntegrallyClosed (Localization.AtPrime (p.asIdeal.comap e)) :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime ⟨p.asIdeal.comap e, inferInstance⟩
    exact IsIntegrallyClosed.of_equiv <| IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime (p.asIdeal.comap e)) (Localization.AtPrime p.asIdeal)
      e (e.map_primeCompl_comap_eq p.asIdeal)

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- A scheme is normal if every local ring is a domain and integrally closed. -/
class IsNormal : Prop where
  stalk_isDomain : ∀ x : X, _root_.IsDomain (X.presheaf.stalk x) := by infer_instance
  stalk_isIntegrallyClosed : ∀ x : X,
    _root_.IsIntegrallyClosed (X.presheaf.stalk x) := by infer_instance

attribute [instance] IsNormal.stalk_isDomain IsNormal.stalk_isIntegrallyClosed

/-- Normality can be proved directly on all stalks. -/
theorem isNormal_of_stalk
    [∀ x : X, _root_.IsDomain (X.presheaf.stalk x)]
    [∀ x : X, _root_.IsIntegrallyClosed (X.presheaf.stalk x)] : IsNormal X :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

/-- Normality is preserved by open immersions. -/
theorem isNormal_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersion f] [IsNormal Y] : IsNormal X := by
  apply +allowSynthFailures isNormal_of_stalk
  · intro x
    exact (asIso (f.stalkMap x)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  · intro x
    exact IsIntegrallyClosed.of_equiv
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

instance {X : Scheme} {U : X.Opens} [IsNormal X] : IsNormal U :=
  isNormal_of_isOpenImmersion U.ι

instance {𝒰 : X.OpenCover} [IsNormal X] (i : 𝒰.I₀) : IsNormal (𝒰.X i) :=
  isNormal_of_isOpenImmersion (𝒰.f i)

instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) (IsNormal ·) :=
  ⟨fun e _ ↦ isNormal_of_isOpenImmersion e.inv⟩

/-- Normality is local on an open cover. -/
theorem IsNormal.of_openCover (𝒰 : X.OpenCover) [∀ i, IsNormal (𝒰.X i)] :
    IsNormal X := by
  apply +allowSynthFailures isNormal_of_stalk
  · intro x
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    exact (asIso ((𝒰.f i).stalkMap y)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  · intro x
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    exact IsIntegrallyClosed.of_equiv
      (asIso ((𝒰.f i).stalkMap y)).symm.commRingCatIsoToRingEquiv

theorem IsNormal.iff_of_openCover (𝒰 : X.OpenCover) :
    IsNormal X ↔ ∀ i, IsNormal (𝒰.X i) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦ of_openCover X 𝒰⟩

set_option backward.isDefEq.respectTransparency.types false in
instance normalSpec {R : CommRingCat.{u}} [IsLocallyNormalRing R] :
    IsNormal (Spec R) := by
  apply +allowSynthFailures isNormal_of_stalk
  · intro x
    let : IsDomain (Localization.AtPrime x.asIdeal) :=
      IsLocallyNormalRing.isDomain_atPrime x
    exact (Spec.stalkIso R x).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  · intro x
    let : IsIntegrallyClosed (Localization.AtPrime x.asIdeal) :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime x
    exact IsIntegrallyClosed.of_equiv
      (Spec.stalkIso R x).symm.commRingCatIsoToRingEquiv

/-- If an affine spectrum is normal, then its coordinate ring is locally
normal. This is deliberately a theorem rather than an instance, to avoid a
typeclass loop with `normalSpec`. -/
theorem isLocallyNormalRing_of_isNormal_spec (R : CommRingCat.{u})
    [IsNormal (Spec R)] : IsLocallyNormalRing R := by
  constructor
  · intro p
    let : IsDomain ((Spec R).presheaf.stalk p) :=
      IsNormal.stalk_isDomain (X := Spec R) p
    exact (Spec.stalkIso R p).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  · intro p
    let : IsIntegrallyClosed ((Spec R).presheaf.stalk p) :=
      IsNormal.stalk_isIntegrallyClosed (X := Spec R) p
    exact IsIntegrallyClosed.of_equiv
      (Spec.stalkIso R p).commRingCatIsoToRingEquiv

/-- A commutative ring is locally normal exactly when its affine spectrum is a
normal scheme. -/
theorem isNormal_spec_iff_isLocallyNormalRing (R : CommRingCat.{u}) :
    IsNormal (Spec R) ↔ IsLocallyNormalRing R := by
  constructor
  · intro h
    let _ := h
    exact isLocallyNormalRing_of_isNormal_spec R
  · intro h
    let _ := h
    infer_instance

instance (priority := 900) isReduced_of_isNormal [IsNormal X] : IsReduced X := by
  exact isReduced_of_isReduced_stalk X

/-- Being a domain is preserved from a scheme stalk to a generalization. -/
theorem isDomain_stalk_of_specializes {x y : X} (hxy : x ⤳ y)
    [_root_.IsDomain (X.presheaf.stalk y)] :
    _root_.IsDomain (X.presheaf.stalk x) := by
  let i := X.affineCover.idx y
  let f := X.affineCover.f i
  let U : X.Opens := f.opensRange
  have hyU : y ∈ U := by
    obtain ⟨y', hy'⟩ := X.affineCover.covers y
    exact ⟨y', hy'⟩
  have hxU : x ∈ U := hxy.mem_open U.isOpen hyU
  let hU : IsAffineOpen U := isAffineOpen_opensRange f
  let p := hU.primeIdealOf ⟨x, hxU⟩
  let q := hU.primeIdealOf ⟨y, hyU⟩
  have hpq : p.asIdeal ≤ q.asIdeal := by
    apply (PrimeSpectrum.le_iff_specializes p q).mpr
    exact ((subtype_specializes_iff _ _).mpr hxy).map hU.isoSpec.hom.continuous
  let _ : Algebra Γ(X, U) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hyU⟩
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk y) q.asIdeal :=
    hU.isLocalization_stalk ⟨y, hyU⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsLocalization.AtPrime.isDomain_of_le
    (R := Γ(X, U)) (X.presheaf.stalk y) (X.presheaf.stalk x)
    (p := p.asIdeal) (q := q.asIdeal) hpq

/-- Integral closedness is preserved from a scheme stalk to a
generalization. -/
theorem isIntegrallyClosed_stalk_of_specializes {x y : X} (hxy : x ⤳ y)
    [_root_.IsDomain (X.presheaf.stalk y)]
    [_root_.IsIntegrallyClosed (X.presheaf.stalk y)] :
    _root_.IsIntegrallyClosed (X.presheaf.stalk x) := by
  let i := X.affineCover.idx y
  let f := X.affineCover.f i
  let U : X.Opens := f.opensRange
  have hyU : y ∈ U := by
    obtain ⟨y', hy'⟩ := X.affineCover.covers y
    exact ⟨y', hy'⟩
  have hxU : x ∈ U := hxy.mem_open U.isOpen hyU
  let hU : IsAffineOpen U := isAffineOpen_opensRange f
  let p := hU.primeIdealOf ⟨x, hxU⟩
  let q := hU.primeIdealOf ⟨y, hyU⟩
  have hpq : p.asIdeal ≤ q.asIdeal := by
    apply (PrimeSpectrum.le_iff_specializes p q).mpr
    exact ((subtype_specializes_iff _ _).mpr hxy).map hU.isoSpec.hom.continuous
  let _ : Algebra Γ(X, U) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hyU⟩
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk y) q.asIdeal :=
    hU.isLocalization_stalk ⟨y, hyU⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsLocalization.AtPrime.isIntegrallyClosed_of_le
    (R := Γ(X, U)) (X.presheaf.stalk y) (X.presheaf.stalk x)
    (p := p.asIdeal) (q := q.asIdeal) hpq

end AlgebraicGeometry
