/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.IsSimpleRing
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Fibres of polynomial spectra under field extension

For fields `K` and `L` with a given `K`-algebra structure on `L`, consider the
contraction map on prime spectra induced by the polynomial coefficient homomorphism.
Its fibre over a nonzero prime of `K[X]` is finite. The generic fibre is finite
exactly when the given field extension is algebraic; in that case it consists
precisely of the zero prime of `L[X]`. Thus all point fibres are finite exactly
when the extension is algebraic.

The fields may have independent universes. These statements concern ordinary
prime-spectrum points, not field-valued morphisms or geometric fibres. Algebraic
extensions need not have finite degree, and no separability assumption is imposed.

## References

* Mathlib's `PrimeSpectrum.comap`, `Polynomial.mapRingHom`, and
  `Algebra.IsAlgebraic` interfaces.
* Mathlib's `IsDedekindDomain.coe_primesOverFinset` and `Ideal.primesOver_bot`
  interfaces for nonzero-prime finiteness and primes over zero.
-/

@[expose] public section

universe u v

namespace Polynomial

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

private theorem isAlgebraic_of_finite_comap_mapRingHom_generic_fiber
    (h : (PrimeSpectrum.comap (Polynomial.mapRingHom (algebraMap K L)) ⁻¹'
      {(⊥ : PrimeSpectrum (Polynomial K))}).Finite) : Algebra.IsAlgebraic K L := by
  classical
  refine ⟨fun a ↦ ?_⟩
  by_contra hnot
  have ha : Transcendental K a := hnot
  -- Positive powers give infinitely many evaluation points, also over finite fields.
  let q : ℕ → PrimeSpectrum (Polynomial L) := fun n ↦
    PrimeSpectrum.comap (Polynomial.evalRingHom (a ^ (n + 1))) (⊥ : PrimeSpectrum L)
  have hq (n : ℕ) :
      q n ∈ PrimeSpectrum.comap (Polynomial.mapRingHom (algebraMap K L)) ⁻¹'
        {(⊥ : PrimeSpectrum (Polynomial K))} := by
    change PrimeSpectrum.comap (Polynomial.mapRingHom (algebraMap K L)) (q n) = ⊥
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro p
    simp only [q, PrimeSpectrum.comap_asIdeal, PrimeSpectrum.asIdeal_bot,
      Ideal.mem_comap, Ideal.mem_bot, coe_mapRingHom, coe_evalRingHom,
      eval_map_algebraMap]
    constructor
    · exact (transcendental_iff.mp (ha.pow (Nat.succ_pos n))) p
    · rintro rfl
      exact map_zero _
  have hq_injective : Function.Injective q := by
    intro m n hmn
    have hx : X - C (a ^ (m + 1)) ∈ (q m).asIdeal := by
      simp [q]
    rw [hmn] at hx
    have hpow : a ^ (m + 1) = a ^ (n + 1) := by
      symm
      simpa [q, sub_eq_zero] using hx
    have hpoly : (X : Polynomial K) ^ (m + 1) = X ^ (n + 1) := by
      apply transcendental_iff_injective.mp ha
      simpa using hpow
    have hsucc : m + 1 = n + 1 := by
      simpa only [natDegree_X_pow] using congrArg natDegree hpoly
    exact Nat.add_right_cancel hsucc
  exact (Set.infinite_of_injective_forall_mem hq_injective hq) h

/-- The generic fibre of the polynomial coefficient-extension spectrum map is
exactly the singleton zero prime if and only if the given field extension is algebraic. -/
theorem comap_mapRingHom_generic_fiber_eq_singleton_iff :
    (PrimeSpectrum.comap (Polynomial.mapRingHom (algebraMap K L)) ⁻¹'
        {(⊥ : PrimeSpectrum (Polynomial K))}) =
      {(⊥ : PrimeSpectrum (Polynomial L))} ↔ Algebra.IsAlgebraic K L := by
  constructor
  · intro h
    apply isAlgebraic_of_finite_comap_mapRingHom_generic_fiber (K := K) (L := L)
    rw [h]
    exact Set.finite_singleton _
  · intro h
    let : Algebra (Polynomial K) (Polynomial L) := Polynomial.algebra K L
    let : Algebra.IsAlgebraic K L := h
    have : Algebra.IsIntegral (Polynomial K) (Polynomial L) := inferInstance
    ext q
    have hmem : q.asIdeal ∈ (⊥ : Ideal (Polynomial K)).primesOver (Polynomial L) ↔
        q.asIdeal = ⊥ := by
      rw [Ideal.primesOver_bot, Set.mem_singleton_iff]
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, PrimeSpectrum.ext_iff,
      PrimeSpectrum.comap_asIdeal, PrimeSpectrum.asIdeal_bot, Ideal.primesOver,
      Set.mem_ofPred_eq, q.isPrime, true_and, Ideal.liesOver_iff, Ideal.under_def,
      Polynomial.algebraMap_def, eq_comm] using hmem

/-- A fibre of the polynomial coefficient-extension spectrum map is finite exactly
when its base prime is nonzero or the given field extension is algebraic. -/
theorem finite_comap_mapRingHom_fiber_iff (p : PrimeSpectrum (Polynomial K)) :
    (PrimeSpectrum.comap (Polynomial.mapRingHom (algebraMap K L)) ⁻¹' {p}).Finite ↔
      p ≠ ⊥ ∨ Algebra.IsAlgebraic K L := by
  classical
  by_cases hp : p = ⊥
  · subst p
    constructor
    · intro h
      exact Or.inr (isAlgebraic_of_finite_comap_mapRingHom_generic_fiber K L h)
    · rintro (h | h)
      · exact (h rfl).elim
      · rw [(comap_mapRingHom_generic_fiber_eq_singleton_iff K L).mpr h]
        exact Set.finite_singleton _
  · constructor
    · intro _
      exact Or.inl hp
    · intro _
      let : Algebra (Polynomial K) (Polynomial L) := Polynomial.algebra K L
      have hp0 : p.asIdeal ≠ ⊥ := by
        intro h
        apply hp
        apply PrimeSpectrum.ext
        simpa only [PrimeSpectrum.asIdeal_bot] using h
      let : p.asIdeal.IsMaximal := p.isPrime.isMaximal hp0
      have hfinite : (p.asIdeal.primesOver (Polynomial L)).Finite := by
        rw [← IsDedekindDomain.coe_primesOverFinset hp0 (Polynomial L)]
        exact (IsDedekindDomain.primesOverFinset p.asIdeal (Polynomial L)).finite_toSet
      refine Set.Finite.of_injOn (f := PrimeSpectrum.asIdeal) ?_ ?_ hfinite
      · intro q hq
        have hq' : PrimeSpectrum.comap (Polynomial.mapRingHom (algebraMap K L)) q = p :=
          Set.mem_singleton_iff.mp hq
        refine ⟨q.isPrime, ⟨?_⟩⟩
        simpa only [Ideal.under_def, Polynomial.algebraMap_def,
          PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hq').symm
      · intro q _ r _ h
        exact PrimeSpectrum.ext h

/-- All ordinary point fibres of the polynomial coefficient-extension spectrum map
are finite if and only if the given field extension is algebraic. -/
theorem finite_comap_mapRingHom_fibers_iff :
    (∀ p : PrimeSpectrum (Polynomial K),
      (PrimeSpectrum.comap (Polynomial.mapRingHom (algebraMap K L)) ⁻¹' {p}).Finite) ↔
      Algebra.IsAlgebraic K L := by
  constructor
  · intro h
    have hzero := (finite_comap_mapRingHom_fiber_iff K L
      (⊥ : PrimeSpectrum (Polynomial K))).mp (h ⊥)
    simpa using hzero
  · intro h p
    exact (finite_comap_mapRingHom_fiber_iff K L p).mpr (Or.inr h)

end Polynomial
