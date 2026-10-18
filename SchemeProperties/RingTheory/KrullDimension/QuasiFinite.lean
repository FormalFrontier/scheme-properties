/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Krull dimension and prime height for quasi-finite maps

Quasi-finite ring homomorphisms do not increase Krull dimension. Contraction is
strict on comparable primes; this does not assert injectivity on all primes.

Contraction preserves prime height for quasi-finite algebras with going down.
Consequently, a flat quasi-finite local ring homomorphism preserves Krull dimension.
The rings may have independent universes. No Noetherian or finite-type hypothesis
is required: quasi-finiteness here is Mathlib's residue-field-fibre condition.

## References

* Mathlib's `Order.krullDim_le_of_strictMono` and
  `Order.height_eq_of_strictMono` are the order-dimension and order-height engines.
* Mathlib's quasi-finite incomparability and going-down APIs supply strictness
  and lower lifting; its maximal-ideal height and contraction formulas give
  the local-ring application.
-/

@[expose] public section

universe u v

/-- Contraction along a quasi-finite ring homomorphism is strictly monotone on
prime spectra. This asserts strictness on comparable primes, not global injectivity. -/
theorem RingHom.QuasiFinite.strictMono_comap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.QuasiFinite) : StrictMono (PrimeSpectrum.comap f) := by
  let := f.toAlgebra
  let : Algebra.QuasiFinite R S := hf.toAlgebra
  intro a b hab
  change a.asIdeal.under R < b.asIdeal.under R
  apply lt_of_le_of_ne (Ideal.comap_mono hab.le)
  intro heq
  exact hab.ne (PrimeSpectrum.ext
    (Algebra.QuasiFinite.eq_of_le_of_under_eq a.asIdeal b.asIdeal hab.le heq))

/-- A quasi-finite ring homomorphism does not increase Krull dimension.
The rings may have independent universes, and no flatness hypothesis is required. -/
theorem RingHom.QuasiFinite.ringKrullDim_le
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.QuasiFinite) : ringKrullDim S ≤ ringKrullDim R := by
  exact Order.krullDim_le_of_strictMono _ hf.strictMono_comap

/-- Quasi-finiteness makes contraction strict on comparable primes, and going down
lifts every smaller prime. The stock order-height theorem then preserves prime height. -/
theorem Algebra.QuasiFinite.height_eq_of_hasGoingDown
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S] [Algebra.HasGoingDown R S] (p : PrimeSpectrum S) :
    p.asIdeal.height = (p.asIdeal.under R).height := by
  change p.asIdeal.height = (PrimeSpectrum.comap (algebraMap R S) p).asIdeal.height
  rw [PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.height_eq_orderHeight]
  apply Order.height_eq_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
  · exact RingHom.QuasiFinite.strictMono_comap (f := algebraMap R S)
      (RingHom.quasiFinite_algebraMap.mpr inferInstance)
  · intro a b hba
    obtain ⟨P, hPa, hP, hPover⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt (p := b.asIdeal)
        (q := a.asIdeal.under R) a.asIdeal hba
    exact ⟨⟨P, hP⟩, hPa, PrimeSpectrum.ext hPover.over.symm⟩

/-- A flat quasi-finite local homomorphism
preserves the dimension of the full local ring. The rings may have independent universes. -/
theorem RingHom.Flat.ringKrullDim_eq_of_quasiFinite
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f]
    (hf : f.Flat) (hq : f.QuasiFinite) : ringKrullDim S = ringKrullDim R := by
  let := f.toAlgebra
  let : Module.Flat R S := hf
  let : Algebra.QuasiFinite R S := hq
  have hheight := Algebra.QuasiFinite.height_eq_of_hasGoingDown
    (R := R) (⟨IsLocalRing.maximalIdeal S, inferInstance⟩ : PrimeSpectrum S)
  change (IsLocalRing.maximalIdeal S).height =
    ((IsLocalRing.maximalIdeal S).comap f).height at hheight
  simpa only [IsLocalRing.maximalIdeal_comap f,
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim] using
    congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hheight
