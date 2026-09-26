module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Localization.LocalizationLocalization

public section

set_option warningAsError true

/-!
# Reducedness under localization and specialization

This file proves that reducedness passes from a localization at a larger prime
to a localization at a smaller prime. Geometrically, it shows that reducedness
of scheme stalks is preserved under generalization.
-/

open AlgebraicGeometry TopologicalSpace

universe u v w

/-- An arbitrary localization of a reduced commutative ring is reduced.

Unlike `isReduced_localizationPreserves`, this form permits the source and
target rings to live in independent universes. -/
theorem IsLocalization.isReduced
    {R : Type u} [CommRing R] (M : Submonoid R) (S : Type v)
    [CommRing S] [Algebra R S] [IsLocalization M S] [IsReduced R] :
    IsReduced S := by
  constructor
  rintro x ⟨_ | n, e⟩
  · simpa using congr_arg (· * x) e
  obtain ⟨⟨y, m⟩, hx⟩ := IsLocalization.surj M x
  dsimp only at hx
  let hx' := congr_arg (· ^ n.succ) hx
  simp only [mul_pow, e, zero_mul, ← map_pow] at hx'
  rw [← (algebraMap R S).map_zero] at hx'
  obtain ⟨m', hm'⟩ := (IsLocalization.eq_iff_exists M S).mp hx'
  apply_fun (· * (m' : R) ^ n) at hm'
  simp only [mul_assoc, zero_mul, mul_zero] at hm'
  rw [← mul_left_comm, ← pow_succ', ← mul_pow] at hm'
  replace hm' := IsNilpotent.eq_zero ⟨_, hm'.symm⟩
  rw [← (IsLocalization.map_units S m).mul_left_inj, hx, zero_mul,
    IsLocalization.map_eq_zero_iff M]
  exact ⟨m', by rw [← hm', mul_comm]⟩

/-- Let `S` and `T` be localizations of `R` at prime ideals `q` and `p`
respectively. If `p ≤ q` and `S` is reduced, then `T` is reduced.

Indeed, `q.primeCompl ≤ p.primeCompl`, so `T` is a further localization of
`S`. -/
theorem IsLocalization.AtPrime.isReduced_of_le
    {R : Type u} (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    [IsLocalization.AtPrime S q] [IsLocalization.AtPrime T p]
    (hpq : p ≤ q) [IsReduced S] : IsReduced T := by
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
  exact IsLocalization.isReduced
    (p.primeCompl.map (algebraMap R S)) T

namespace AlgebraicGeometry

/-- Reducedness of scheme stalks is preserved under generalization: if `x`
specializes to `y` and the stalk at `y` is reduced, then the stalk at `x` is
reduced. -/
theorem isReduced_stalk_of_specializes (X : Scheme.{u}) {x y : X}
    (hxy : x ⤳ y) [_root_.IsReduced (X.presheaf.stalk y)] :
    _root_.IsReduced (X.presheaf.stalk x) := by
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
    have hUxy : (⟨x, hxU⟩ : U) ⤳ ⟨y, hyU⟩ :=
      (subtype_specializes_iff _ _).mpr hxy
    exact hUxy.map hU.isoSpec.hom.continuous
  let _ : Algebra Γ(X, U) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hyU⟩
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk y) q.asIdeal :=
    hU.isLocalization_stalk ⟨y, hyU⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsLocalization.AtPrime.isReduced_of_le
    (R := Γ(X, U)) (X.presheaf.stalk y) (X.presheaf.stalk x)
    (p := p.asIdeal) (q := q.asIdeal) hpq

end AlgebraicGeometry
