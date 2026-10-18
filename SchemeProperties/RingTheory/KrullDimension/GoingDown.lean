/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Height and dimension bounds from going down

Going down bounds the height of the contraction of an ideal by the height of the ideal.
For a local ring map with local target, lifting generalizations on prime spectra gives
an inequality of Krull dimensions. Flat local ring maps satisfy this condition.

## Main results

- `Ideal.height_under_le_of_hasGoingDown` applies to every ideal, not only prime ideals.
  For a point `q : PrimeSpectrum S`, use it with `I := q.asIdeal`.
- `RingHom.ringKrullDim_le_of_generalizingMap` takes a local ring map whose map on prime
  spectra lifts generalizations. Locality of the source follows from locality of the
  target and `RingHom.domain_isLocalRing`.
- `RingHom.Flat.ringKrullDim_le` supplies the dimension inequality for flat local maps.

Heights take values in `ℕ∞`, and ring dimensions take values in `WithBot ℕ∞`.
The statements include infinite heights and dimensions and the unit ideal. They require
no Noetherian or finite-dimensional hypothesis and do not assert an additive height formula.

## References

- Mathlib, `Ideal.exists_ltSeries_of_hasGoingDown`: lifting finite strict chains of primes
  while preserving their length and last ideal.
- Mathlib, `Order.height_le`, `Order.length_le_height_last`, and
  `Ideal.height_eq_inf_minimalPrimes`: height bounds from chains and minimal primes.
- Mathlib, `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap` and
  `RingHom.Flat.generalizingMap_comap`: going down and lifting generalizations.
- Mathlib, `IsLocalRing.maximalIdeal_comap` and
  `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`: maximal ideals and local dimension.
-/

@[expose] public section

universe u v

private theorem height_under_le_of_isPrime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingDown R S] (P : Ideal S) [P.IsPrime] :
    (P.under R).height ≤ P.height := by
  rw [PrimeSpectrum.height_eq_orderHeight ⟨P.under R, inferInstance⟩,
    PrimeSpectrum.height_eq_orderHeight ⟨P, inferInstance⟩]
  apply Order.height_le
  intro l hl
  have : P.LiesOver l.last.asIdeal := ⟨by rw [hl]⟩
  obtain ⟨L, hlength, hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  rw [← hlength, ← hlast]
  exact Order.length_le_height_last

/-- Under going down, the height of the contraction of any ideal is at most the height
of the ideal. This includes the unit ideal and infinite heights. The chain-lifting
result is Mathlib's `Ideal.exists_ltSeries_of_hasGoingDown`; heights of arbitrary ideals
are described by `Ideal.height_eq_inf_minimalPrimes`. -/
theorem Ideal.height_under_le_of_hasGoingDown
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingDown R S] (I : Ideal S) :
    (I.under R).height ≤ I.height := by
  rw [I.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun P hP ↦ ?_
  have := hP.isPrime
  exact (Ideal.height_mono (Ideal.comap_mono hP.le)).trans
    (height_under_le_of_isPrime P)

/-- A local ring map into a local ring whose map on prime spectra lifts generalizations
bounds the dimension of its source by the dimension of its target. The source is local
by `RingHom.domain_isLocalRing`. Mathlib's
`Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap` identifies the lifting
condition with going down for the algebra induced by the map. -/
theorem RingHom.ringKrullDim_le_of_generalizingMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f]
    (hf : GeneralizingMap (PrimeSpectrum.comap f)) :
    ringKrullDim R ≤ ringKrullDim S := by
  let : IsLocalRing R := f.domain_isLocalRing
  let : Algebra R S := f.toAlgebra
  let : Algebra.HasGoingDown R S :=
    Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mpr hf
  have h := Ideal.height_under_le_of_hasGoingDown (R := R) (IsLocalRing.maximalIdeal S)
  change ((IsLocalRing.maximalIdeal S).comap f).height ≤ _ at h
  rw [IsLocalRing.maximalIdeal_comap f] at h
  simpa only [IsLocalRing.maximalIdeal_height_eq_ringKrullDim] using
    (WithBot.coe_le_coe.mpr h)

/-- A flat local ring map into a local ring bounds the dimension of its source by the
dimension of its target. Flatness gives the lifting of generalizations through Mathlib's
`RingHom.Flat.generalizingMap_comap`. No finiteness hypothesis on either dimension is needed. -/
theorem RingHom.Flat.ringKrullDim_le
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing S] {f : R →+* S} [IsLocalHom f] (hf : f.Flat) :
    ringKrullDim R ≤ ringKrullDim S := by
  exact f.ringKrullDim_le_of_generalizingMap hf.generalizingMap_comap
