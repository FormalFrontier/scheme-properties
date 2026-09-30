/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
public import Mathlib.RingTheory.DedekindDomain.Dvr

public section

set_option warningAsError true

/-!
# Factorial schemes

This file defines a factorial scheme by requiring every stalk to be a unique
factorization monoid. Since scheme stalks are nontrivial commutative rings,
this is exactly the usual unique-factorization-domain condition. It proves the
basic localization, open-local, and affine-spectrum API for this property.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v w

namespace IsLocalization.AtPrime

/-- Let `S` and `T` be localizations of `R` at prime ideals `q` and `p`
respectively. If `p ≤ q` and `S` has unique factorization, then so does `T`. -/
theorem uniqueFactorizationMonoid_of_le
    {R : Type u} (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    [IsLocalization.AtPrime S q] [IsLocalization.AtPrime T p]
    (hpq : p ≤ q) [UniqueFactorizationMonoid S] :
    UniqueFactorizationMonoid T := by
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
  exact UniqueFactorizationMonoid.of_isLocalization
    (p.primeCompl.map (algebraMap R S)) T

end IsLocalization.AtPrime

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- A scheme is factorial if every local ring has unique factorization. -/
class IsFactorial : Prop where
  stalk_uniqueFactorizationMonoid : ∀ x : X,
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by infer_instance

attribute [instance] IsFactorial.stalk_uniqueFactorizationMonoid

/-- Every stalk of a factorial scheme is a domain. -/
instance IsFactorial.stalk_isDomain [IsFactorial X] (x : X) :
    _root_.IsDomain (X.presheaf.stalk x) :=
  (isDomain_iff_cancelMulZero_and_nontrivial _).mpr ⟨inferInstance, inferInstance⟩

/-- Factoriality can be proved directly on all stalks. -/
theorem isFactorial_of_stalk
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] :
    IsFactorial X :=
  ⟨fun _ ↦ inferInstance⟩

/-- Empty schemes are factorial. -/
instance (priority := low) [IsEmpty X] : IsFactorial X :=
  ⟨fun x ↦ isEmptyElim x⟩

/-- Factoriality is preserved by open immersions. -/
theorem isFactorial_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersion f] [IsFactorial Y] : IsFactorial X := by
  apply +allowSynthFailures isFactorial_of_stalk
  intro x
  exact (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.toMulEquiv
    |>.uniqueFactorizationMonoid inferInstance

instance {X : Scheme} {U : X.Opens} [IsFactorial X] : IsFactorial U :=
  isFactorial_of_isOpenImmersion U.ι

instance {𝒰 : X.OpenCover} [IsFactorial X] (i : 𝒰.I₀) :
    IsFactorial (𝒰.X i) :=
  isFactorial_of_isOpenImmersion (𝒰.f i)

instance : ObjectProperty.IsClosedUnderIsomorphisms
    (C := Scheme) (IsFactorial ·) :=
  ⟨fun e _ ↦ isFactorial_of_isOpenImmersion e.inv⟩

/-- Factoriality is local on an open cover. -/
theorem IsFactorial.of_openCover (𝒰 : X.OpenCover)
    [∀ i, IsFactorial (𝒰.X i)] : IsFactorial X := by
  apply +allowSynthFailures isFactorial_of_stalk
  intro x
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  exact (asIso ((𝒰.f i).stalkMap y)).symm.commRingCatIsoToRingEquiv.toMulEquiv
    |>.uniqueFactorizationMonoid inferInstance

theorem IsFactorial.iff_of_openCover (𝒰 : X.OpenCover) :
    IsFactorial X ↔ ∀ i, IsFactorial (𝒰.X i) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦ of_openCover X 𝒰⟩

set_option backward.isDefEq.respectTransparency.types false in
instance factorialSpec {R : CommRingCat.{u}} [UniqueFactorizationMonoid R] :
    IsFactorial (Spec R) := by
  apply +allowSynthFailures isFactorial_of_stalk
  intro x
  let _ : UniqueFactorizationMonoid (Localization.AtPrime x.asIdeal) :=
    UniqueFactorizationMonoid.of_isLocalization x.asIdeal.primeCompl _
  exact (Spec.stalkIso R x).symm.commRingCatIsoToRingEquiv.toMulEquiv
    |>.uniqueFactorizationMonoid inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- The spectrum of a Dedekind domain is factorial, even when the domain itself
does not have unique factorization. -/
theorem factorialSpec_of_isDedekindDomain
    {R : CommRingCat.{u}} [IsDedekindDomain R] :
    IsFactorial (Spec R) := by
  apply +allowSynthFailures isFactorial_of_stalk
  intro x
  let _ : IsDedekindDomain (Localization.AtPrime x.asIdeal) := inferInstance
  let _ : IsPrincipalIdealRing (Localization.AtPrime x.asIdeal) := inferInstance
  let _ : UniqueFactorizationMonoid (Localization.AtPrime x.asIdeal) := inferInstance
  exact (Spec.stalkIso R x).symm.commRingCatIsoToRingEquiv.toMulEquiv
    |>.uniqueFactorizationMonoid inferInstance

#print axioms factorialSpec_of_isDedekindDomain

/-- Unique factorization of stalks is preserved under generalization. -/
theorem uniqueFactorizationMonoid_stalk_of_specializes {x y : X} (hxy : x ⤳ y)
    [UniqueFactorizationMonoid (X.presheaf.stalk y)] :
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
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
  exact IsLocalization.AtPrime.uniqueFactorizationMonoid_of_le
    (R := Γ(X, U)) (X.presheaf.stalk y) (X.presheaf.stalk x)
    (p := p.asIdeal) (q := q.asIdeal) hpq

end AlgebraicGeometry
