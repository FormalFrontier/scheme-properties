/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Faithful flatness of finite families

A finite family of flat commutative-ring maps that is jointly surjective on
prime spectra induces a faithfully flat map to the product. The maps determine
all scalar structures used in the proof. The index may be empty, and the base
and factor rings may be zero rings.

Joint surjectivity on the factor spectra implies surjectivity on the spectrum
of the product for an arbitrary family of commutative semirings. This implication
uses a prime pulled back along one coordinate evaluation, not a classification
of the primes of the product. Finiteness is needed only for product flatness;
no finite jointly covering subfamily is extracted.

## References

* Mathlib's `Module.Flat.directSum`, `DirectSum.linearEquivFunOnFintype` and
  `Module.Flat.of_linearEquiv` supply flatness of the finite product.
* Mathlib's `PrimeSpectrum.comap_comp_apply` supplies functoriality of prime
  pullback along `RingHom.pi` and `Pi.evalRingHom`.
* Mathlib's `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective` supplies the
  flat-and-surjective-spectrum criterion for faithful flatness.
-/

@[expose] public section

universe u v w

namespace PrimeSpectrum

/-- Joint surjectivity on the factor spectra implies surjectivity on the
spectrum of the product for any family of commutative semirings. -/
theorem comap_pi_surjective
    {A : Type u} {ι : Type v} {B : ι → Type w}
    [CommSemiring A] [∀ i, CommSemiring (B i)]
    (f : ∀ i, A →+* B i)
    (hcover : Function.Surjective
      (fun q : Σ i, PrimeSpectrum (B i) ↦ comap (f q.1) q.2)) :
    Function.Surjective (comap (RingHom.pi f)) := by
  intro p
  obtain ⟨⟨i, q⟩, hq⟩ := hcover p
  refine ⟨comap (Pi.evalRingHom B i) q, ?_⟩
  have hcomp : (Pi.evalRingHom B i).comp (RingHom.pi f) = f i := by
    ext a
    rfl
  rw [← comap_comp_apply, hcomp]
  exact hq

end PrimeSpectrum

namespace RingHom.FaithfullyFlat

/-- A finite family of flat ring maps that is jointly surjective on prime
spectra induces a faithfully flat map to the product. -/
theorem pi_of_jointly_surjective
    {A : Type u} {ι : Type v} {B : ι → Type w}
    [CommRing A] [∀ i, CommRing (B i)] [_root_.Finite ι]
    (f : ∀ i, A →+* B i)
    (hf : ∀ i, (f i).Flat)
    (hcover : Function.Surjective
      (fun q : Σ i, PrimeSpectrum (B i) ↦
        PrimeSpectrum.comap (f q.1) q.2)) :
    (RingHom.pi f).FaithfullyFlat := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : ∀ i, Algebra A (B i) := fun i ↦ (f i).toAlgebra
  have : ∀ i, Module.Flat A (B i) := fun i ↦ hf i
  have hflat : (RingHom.pi f).Flat := by
    have hmap : algebraMap A (∀ i, B i) = RingHom.pi f := by
      ext a i
      rfl
    rw [← hmap, RingHom.flat_algebraMap_iff]
    exact Module.Flat.of_linearEquiv
      (DirectSum.linearEquivFunOnFintype A ι B).symm
  exact iff_flat_and_comap_surjective.mpr
    ⟨hflat, PrimeSpectrum.comap_pi_surjective f hcover⟩

end RingHom.FaithfullyFlat
