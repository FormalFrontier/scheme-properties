/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ReducedLocus
public import CoherentModules.Algebra.TrivSqZeroExt.Finite
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

@[expose] public section

set_option warningAsError true

/-!
# Reduced prime localizations of trivial square-zero extensions

For a square-zero extension of a commutative ring by an arbitrary module, reducedness
at a prime requires both reducedness of the base localization and vanishing of the
localized module. When the base is reduced, this describes the reduced locus via
module support, without finite generation assumptions.

## References

* R. Vakil, *The Rising Sea: Foundations of Algebraic Geometry*.
* Mathlib's support, prime-localization, square-zero kernel and prime-spectrum APIs.
* Coherent Modules' canonical square-zero actions.
-/

open scoped TrivSqZeroExt

universe u v w x

namespace TrivSqZeroExt

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

private theorem mem_comap_fst_iff (p : PrimeSpectrum R) (s : TrivSqZeroExt R M) :
    s ∈ (PrimeSpectrum.comap (fstHom R R M).toRingHom p).asIdeal ↔
      s.fst ∈ p.asIdeal := by
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  rfl

private theorem not_mem_support_nilradical_iff (p : PrimeSpectrum R) :
    PrimeSpectrum.comap (fstHom R R M).toRingHom p ∉
      Module.support (TrivSqZeroExt R M) (nilradical (TrivSqZeroExt R M)) ↔
    p ∉ Module.support R (nilradical R) ∧ p ∉ Module.support R M := by
  rw [Module.notMem_support_iff', Module.notMem_support_iff',
    Module.notMem_support_iff']
  constructor
  · intro h
    constructor
    · intro a
      have ha : (inl a.val : TrivSqZeroExt R M) ∈
          nilradical (TrivSqZeroExt R M) :=
        mem_nilradical.mpr ((mem_nilradical.mp a.property).map (inlHom R M))
      obtain ⟨s, hs, hz⟩ := h ⟨inl a.val, ha⟩
      refine ⟨s.fst, ?_, ?_⟩
      · simpa only [mem_comap_fst_iff] using hs
      · apply Subtype.ext
        have heq : s * (inl a.val : TrivSqZeroExt R M) = 0 := by
          simpa only [Submodule.coe_smul, Submodule.coe_zero, smul_eq_mul] using
            congrArg Subtype.val hz
        exact congrArg TrivSqZeroExt.fst heq
    · intro m
      have hm : (inr m : TrivSqZeroExt R M) ∈
          nilradical (TrivSqZeroExt R M) :=
        mem_nilradical.mpr ⟨2, by simp [pow_two, inr_mul_inr]⟩
      obtain ⟨s, hs, hz⟩ := h ⟨inr m, hm⟩
      refine ⟨s.fst, ?_, ?_⟩
      · simpa only [mem_comap_fst_iff] using hs
      · have heq : s * (inr m : TrivSqZeroExt R M) = 0 := by
          simpa only [Submodule.coe_smul, Submodule.coe_zero, smul_eq_mul] using
            congrArg Subtype.val hz
        rw [← inl_fst_add_inr_snd_eq s, add_mul, inl_mul_inr, inr_mul_inr,
          add_zero] at heq
        exact inr_injective heq
  · rintro ⟨hbase, hmodule⟩ a
    have ha : a.val.fst ∈ nilradical R :=
      mem_nilradical.mpr ((mem_nilradical.mp a.property).map (fstHom R R M).toRingHom)
    obtain ⟨r, hr, hrzero⟩ := hbase ⟨a.val.fst, ha⟩
    obtain ⟨t, ht, htzero⟩ := hmodule a.val.snd
    refine ⟨inl (r * t), ?_, ?_⟩
    · have hmul : r * t ∉ p.asIdeal := by
        intro h
        rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem
          (inferInstance : p.asIdeal.IsPrime)).mp h with h | h
        · exact hr h
        · exact ht h
      simpa only [mem_comap_fst_iff, fst_inl] using hmul
    · apply Subtype.ext
      simp only [Submodule.coe_smul, Submodule.coe_zero, smul_eq_mul]
      rw [← inl_fst_add_inr_snd_eq a.val, mul_add, inl_mul_inl, inl_mul_inr]
      have hrzero' : r * a.val.fst = 0 := by
        simpa only [Submodule.coe_smul, Submodule.coe_zero, smul_eq_mul] using
          congrArg Subtype.val hrzero
      have hfst : r * t * a.val.fst = 0 := by
        rw [mul_comm r t, mul_assoc, hrzero', mul_zero]
      have hsnd : (r * t) • a.val.snd = 0 := by
        rw [mul_smul, htzero, smul_zero]
      rw [hfst, hsnd, inl_zero, inr_zero, zero_add]

/-- A localization of a trivial square-zero extension at the prime above `p` is reduced
exactly when the base localization is reduced and the module vanishes at `p`.
The localization rings can be any models of prime localization. -/
theorem isReduced_atPrime_iff (p : PrimeSpectrum R)
    (S : Type w) [CommRing S] [Algebra (TrivSqZeroExt R M) S]
    [IsLocalization.AtPrime S
      (PrimeSpectrum.comap (fstHom R R M).toRingHom p).asIdeal]
    (T : Type x) [CommRing T] [Algebra R T] [IsLocalization.AtPrime T p.asIdeal] :
    _root_.IsReduced S ↔ _root_.IsReduced T ∧ p ∉ Module.support R M := by
  rw [IsLocalization.AtPrime.isReduced_iff_not_mem_support_nilradical
      (PrimeSpectrum.comap (fstHom R R M).toRingHom p) S,
    IsLocalization.AtPrime.isReduced_iff_not_mem_support_nilradical p T]
  exact not_mem_support_nilradical_iff p

/-- Over a reduced base, the primes at which the square-zero extension has reduced
localization are exactly the primes outside the module support. -/
theorem reduced_atPrime_comap_eq_compl_support [IsReduced R] :
    {p : PrimeSpectrum R |
      _root_.IsReduced (Localization.AtPrime
        (PrimeSpectrum.comap (fstHom R R M).toRingHom p).asIdeal)} =
      (Module.support R M)ᶜ := by
  ext p
  simpa only [Set.mem_ofPred_eq, Set.mem_compl_iff] using
    (isReduced_atPrime_iff (M := M) p
      (Localization.AtPrime (PrimeSpectrum.comap (fstHom R R M).toRingHom p).asIdeal)
      (Localization.AtPrime p.asIdeal)).trans
      (and_iff_right (inferInstance : _root_.IsReduced (Localization.AtPrime p.asIdeal)))

/-- Over a reduced base, the reduced prime-localization locus of the square-zero
extension is open exactly when the support of the module is closed. -/
theorem isOpen_reduced_atPrime_iff_isClosed_support [IsReduced R] :
    IsOpen {q : PrimeSpectrum (TrivSqZeroExt R M) |
      _root_.IsReduced (Localization.AtPrime q.asIdeal)} ↔
      IsClosed (Module.support R M) := by
  let f : TrivSqZeroExt R M →+* R := (fstHom R R M).toRingHom
  have hf : Function.Surjective f := by
    intro r
    exact ⟨inl r, rfl⟩
  have hker : RingHom.ker f ≤ nilradical (TrivSqZeroExt R M) := by
    intro a ha
    have ha' : a ∈ kerIdeal R M := ha
    have ha2 : a ^ 2 = 0 := by
      have := Ideal.pow_mem_pow ha' 2
      simpa only [kerIdeal_sq, Ideal.mem_bot] using this
    exact mem_nilradical.mpr ⟨2, ha2⟩
  have hhome : IsHomeomorph (PrimeSpectrum.comap f) :=
    PrimeSpectrum.isHomeomorph_comap f (fun r => ⟨1, by omega, by simpa using hf r⟩) hker
  have hpreimage : (PrimeSpectrum.comap f) ⁻¹'
      {q : PrimeSpectrum (TrivSqZeroExt R M) |
        _root_.IsReduced (Localization.AtPrime q.asIdeal)} =
        (Module.support R M)ᶜ := reduced_atPrime_comap_eq_compl_support
  rw [← isOpen_compl_iff, ← hpreimage]
  constructor
  · intro hopen
    exact hopen.preimage hhome.continuous
  · intro hopen
    have himage := hhome.isOpenMap _ hopen
    rwa [Set.image_preimage_eq _ hhome.surjective] at himage

end TrivSqZeroExt
