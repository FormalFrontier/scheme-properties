/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.PolynomialPointPrime
public import SchemeProperties.TrivSqZeroExtReducedLocus
public import Mathlib.Algebra.DirectSum.Module

@[expose] public section

set_option warningAsError true

/-!
# Polynomial point modules and the reduced locus of their square-zero extensions

For an arbitrary family of field points, each summand is the polynomial ring
modulo its own evaluation kernel. In particular, repeated points give repeated
summands, and an infinite indexing type can have finite image. The square-zero
statement concerns reducedness of localizations at **all** primes of the extension.

## References

* R. Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, Remark 5.2.2,
  for the motivating non-open reduced-locus phenomenon. These statements concern
  a polynomial point-module square-zero extension, not an identification with the
  generator-and-relation ring in that remark.
* Mathlib's evaluation ideals, module support, and prime-spectrum topology.
* Coherent Modules' square-zero extension and its canonical module actions.
-/

open scoped TrivSqZeroExt

namespace Polynomial

universe u v

variable {K : Type u} [Field K] {ι : Type v} (a : ι → K)

/-- The support of a direct sum of evaluation quotients is the set of evaluation
primes corresponding to the values of the family. Repeated points need not be
discarded from the indexing family. -/
theorem support_directSum_evalQuotient_eq_range :
    Module.support K[X]
      (DirectSum ι (fun i => K[X] ⧸ RingHom.ker (evalRingHom (a i)))) =
        Set.range (fun i : ι => evalPrime (a i)) := by
  classical
  let I (i : ι) : Ideal K[X] := RingHom.ker (evalRingHom (a i))
  let M (i : ι) := K[X] ⧸ I i
  let s : Set (DirectSum ι M) :=
    {m | ∃ i, ∃ v : M i, DirectSum.lof K[X] ι M i v = m}
  have hs : Submodule.span K[X] s = ⊤ := by
    apply top_unique
    intro m _
    induction m using DirectSum.induction_on with
    | zero => exact (Submodule.span K[X] s).zero_mem
    | of i v => exact Submodule.subset_span ⟨i, v, rfl⟩
    | add m n hm hn =>
        exact (Submodule.span K[X] s).add_mem (hm Submodule.mem_top) (hn Submodule.mem_top)
  ext q
  constructor
  · intro hq
    obtain ⟨m, ⟨i, v, rfl⟩, hm⟩ := (Module.mem_support_iff_of_span_eq_top hs).mp hq
    have hker : I i ≤ q.asIdeal := by
      intro p hp
      apply hm
      rw [Submodule.mem_annihilator_span_singleton]
      have hsmul : p • v = 0 := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective v
        change Ideal.Quotient.mk (I i) (p * r) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr ((I i).mul_mem_right r hp)
      rw [← map_smul, hsmul, map_zero]
    have hmax : (evalPrime (a i)).asIdeal.IsMaximal := by
      rw [evalPrime_asIdeal]
      exact RingHom.ker_isMaximal_of_surjective _ (eval_surjective (a i))
    exact ⟨i, PrimeSpectrum.ext (hmax.eq_of_le q.2.ne_top hker)⟩
  · rintro ⟨i, rfl⟩
    have hi : evalPrime (a i) ∈ Module.support K[X] (M i) := by
      rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr (by rw [evalPrime_asIdeal])
    exact (Module.support_subset_of_injective (DirectSum.lof K[X] ι M i)
      (by
        change Function.Injective (DirectSum.of M i)
        exact DirectSum.of_injective i)) hi

/-- Over any field, the support of the point-module sum is closed precisely when
the image of the point family is finite. The index type itself need not be finite. -/
theorem isClosed_support_directSum_evalQuotient_iff_finite_range :
    IsClosed (Module.support K[X]
      (DirectSum ι (fun i => K[X] ⧸ RingHom.ker (evalRingHom (a i))))) ↔
        (Set.range a).Finite := by
  rw [support_directSum_evalQuotient_eq_range]
  have hpoint (x : K) : IsClosed ({evalPrime x} : Set (PrimeSpectrum K[X])) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (by
      rw [evalPrime_asIdeal]
      exact RingHom.ker_isMaximal_of_surjective _ (eval_surjective x))
  constructor
  · intro hclosed
    by_contra hfinite
    have hinfinite : (Set.range a).Infinite := hfinite
    obtain ⟨I, hI⟩ :=
      (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hclosed
    have hIzero : I = ⊥ := by
      apply le_antisymm _ bot_le
      intro p hp
      have hroots : Set.range a ⊆ {x : K | IsRoot p x} := by
        rintro x ⟨i, rfl⟩
        have hmem : evalPrime (a i) ∈ PrimeSpectrum.zeroLocus I := by
          rw [← hI]
          exact ⟨i, rfl⟩
        exact (mem_evalPrime_iff (a i) p).mp
          ((PrimeSpectrum.mem_zeroLocus _ _).mp hmem hp)
      have hpzero : p = 0 := eq_zero_of_infinite_isRoot p (hinfinite.mono hroots)
      simpa only [Ideal.mem_bot] using hpzero
    have hgeneric : (⟨(⊥ : Ideal K[X]), inferInstance⟩ : PrimeSpectrum K[X]) ∈
        Set.range (fun i : ι => evalPrime (a i)) := by
      rw [hI, hIzero, PrimeSpectrum.zeroLocus_bot]
      exact Set.mem_univ _
    obtain ⟨i, hi⟩ := hgeneric
    have hmem : X - C (a i) ∈ (⊥ : Ideal K[X]) := by
      have hmem' : X - C (a i) ∈ (evalPrime (a i)).asIdeal := by simp
      change evalPrime (a i) = (⟨(⊥ : Ideal K[X]), inferInstance⟩ : PrimeSpectrum K[X]) at hi
      rw [hi] at hmem'
      exact hmem'
    exact X_sub_C_ne_zero (a i) (by simpa only [Ideal.mem_bot] using hmem)
  · intro hfinite
    have hrange : Set.range (fun i : ι => evalPrime (a i)) =
        ⋃ x ∈ Set.range a, ({evalPrime x} : Set (PrimeSpectrum K[X])) := by
      ext p
      simp only [Set.mem_range, Set.mem_iUnion, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨a i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [hrange]
    exact hfinite.isClosed_biUnion (fun x _ => hpoint x)

/-- The full prime-localization reduced locus of the square-zero extension is
open precisely when the family has finite image. This uses the general support
criterion for square-zero extensions. -/
theorem isOpen_reduced_atPrime_directSum_evalQuotient_iff_finite_range :
    IsOpen {q : PrimeSpectrum
      (TrivSqZeroExt K[X]
        (DirectSum ι (fun i => K[X] ⧸ RingHom.ker (evalRingHom (a i))))) |
          _root_.IsReduced (Localization.AtPrime q.asIdeal)} ↔
        (Set.range a).Finite := by
  exact (TrivSqZeroExt.isOpen_reduced_atPrime_iff_isClosed_support
    (R := K[X]) (M := DirectSum ι (fun i => K[X] ⧸ RingHom.ker (evalRingHom (a i))))).trans
      (isClosed_support_directSum_evalQuotient_iff_finite_range a)

end Polynomial
