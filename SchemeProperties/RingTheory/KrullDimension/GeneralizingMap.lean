/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Global Krull dimension under surjective generalizing maps of spectra

If contraction on prime spectra is generalizing and surjective, the Krull
dimension of the source ring is at most that of the target ring. In particular,
Krull dimension does not decrease under a faithfully flat ring homomorphism.
The rings may lie in independent universes.

The dimensions take values in `WithBot ℕ∞`: no finite-dimensionality or
nontriviality hypothesis is imposed. The zero ring has dimension `⊥`, and an
infinite-dimensional source forces an infinite-dimensional target.

## References

* Mathlib's `Ideal.exists_ltSeries_of_hasGoingDown` lifts finite chains of primes
  with the same length, after choosing a prime above the last member.
* Mathlib's `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`
  identifies going down with generalization lifting on spectra.
* Mathlib's `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective` and
  `RingHom.Flat.generalizingMap_comap` supply the faithfully flat specialization.
-/

@[expose] public section

universe u v

namespace RingHom

/-- A surjective generalizing map `Spec S → Spec R` induced by a ring homomorphism
bounds the global Krull dimension of `R` by that of `S`, in `WithBot ℕ∞`. -/
theorem ringKrullDim_le_of_generalizingMap_comap_of_surjective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)
    (hg : GeneralizingMap (PrimeSpectrum.comap f))
    (hs : Function.Surjective (PrimeSpectrum.comap f)) :
    ringKrullDim R ≤ ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.HasGoingDown R S :=
    Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mpr (by
      simpa only [RingHom.algebraMap_toAlgebra] using hg)
  change (⨆ l : LTSeries (PrimeSpectrum R), (l.length : WithBot ℕ∞)) ≤
    Order.krullDim (PrimeSpectrum S)
  refine iSup_le fun l ↦ ?_
  obtain ⟨q, hq⟩ := hs l.last
  let : q.asIdeal.LiesOver l.last.asIdeal := by
    refine ⟨?_⟩
    simpa only [Ideal.under_def, RingHom.algebraMap_toAlgebra,
      PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hq.symm
  obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l q.asIdeal
  rw [← hlen]
  exact Order.LTSeries.length_le_krullDim L

/-- A faithfully flat ring homomorphism does not decrease global Krull dimension.
For an algebra, apply this to `algebraMap R S` using
`RingHom.faithfullyFlat_algebraMap_iff`. -/
theorem FaithfullyFlat.ringKrullDim_le
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.FaithfullyFlat) : ringKrullDim R ≤ ringKrullDim S := by
  obtain ⟨hflat, hsurj⟩ := FaithfullyFlat.iff_flat_and_comap_surjective.mp hf
  exact ringKrullDim_le_of_generalizingMap_comap_of_surjective f
    (hflat.generalizingMap_comap) hsurj

end RingHom
