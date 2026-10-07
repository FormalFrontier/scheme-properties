/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ReducedLocus
public import CoherentModules.Algebra.TrivSqZeroExt.Finite
public import Mathlib.RingTheory.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Squarefree

@[expose] public section

set_option warningAsError true

/-!
# Boundary cases for square-zero reduced localizations

These witnesses use module support and nilpotence directly, independently of the
square-zero localization criterion. They include an empty spectrum, a vanishing
module, dual numbers, a nonreduced base, and an ideal supported on only one
component of a reduced product.
-/

open scoped TrivSqZeroExt

private instance : _root_.IsReduced (ZMod 2) :=
  isReduced_zmod.mpr (Or.inl Nat.squarefree_two)

private instance : Nontrivial (ZMod 4) := ⟨0, 1, by decide⟩

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

example : IsEmpty (PrimeSpectrum (TrivSqZeroExt (ZMod 1) (ZMod 1))) := by
  apply PrimeSpectrum.isEmpty_iff_subsingleton.mpr
  constructor
  intro a b
  exact Prod.ext (Subsingleton.elim a.fst b.fst) (Subsingleton.elim a.snd b.snd)

/-- The trivial extension by the zero ideal has reduced localizations over a field. -/
theorem zero_module_reduced_localization (p : PrimeSpectrum (ZMod 2)) :
    p ∉ Module.support (ZMod 2) (⊥ : Ideal (ZMod 2)) ∧
      _root_.IsReduced (Localization.AtPrime
        (PrimeSpectrum.comap (TrivSqZeroExt.fstHom (ZMod 2) (ZMod 2)
          (⊥ : Ideal (ZMod 2))).toRingHom p).asIdeal) := by
  constructor
  · rw [Module.notMem_support_iff']
    intro m
    refine ⟨1, p.asIdeal.one_notMem, ?_⟩
    exact Subsingleton.elim _ _
  · have hinjective : Function.Injective
        (TrivSqZeroExt.fstHom (ZMod 2) (ZMod 2)
          (⊥ : Ideal (ZMod 2))).toRingHom := by
      intro a b hab
      exact Prod.ext hab (Subsingleton.elim a.snd b.snd)
    have : _root_.IsReduced (TrivSqZeroExt (ZMod 2) (⊥ : Ideal (ZMod 2))) :=
      isReduced_of_injective _ hinjective
    infer_instance

/-- The square-zero element in the dual numbers survives at the prime over the
unique prime of the field. -/
theorem dual_numbers_nonreduced_localization :
    ∃ p : PrimeSpectrum (ZMod 2),
      p ∈ Module.support (ZMod 2) (ZMod 2) ∧
        ¬ _root_.IsReduced (Localization.AtPrime
          (PrimeSpectrum.comap (TrivSqZeroExt.fstHom (ZMod 2) (ZMod 2)
            (ZMod 2)).toRingHom p).asIdeal) := by
  classical
  let p : PrimeSpectrum (ZMod 2) := Classical.choice inferInstance
  let q := PrimeSpectrum.comap (TrivSqZeroExt.fstHom (ZMod 2) (ZMod 2)
    (ZMod 2)).toRingHom p
  have hsupport : p ∈ Module.support (ZMod 2) (ZMod 2) := by
    apply Module.mem_support_iff'.mpr
    refine ⟨1, ?_⟩
    intro r hr hzero
    have hr0 : r ≠ 0 := by
      intro he
      exact hr (he ▸ p.asIdeal.zero_mem)
    have hone : r = 1 := (by decide : ∀ r : ZMod 2, r ≠ 0 → r = 1) r hr0
    rw [hone, one_smul] at hzero
    exact (one_ne_zero : (1 : ZMod 2) ≠ 0) hzero
  have hnot : ¬ _root_.IsReduced (Localization.AtPrime q.asIdeal) := by
    intro hred
    let m : nilradical (TrivSqZeroExt (ZMod 2) (ZMod 2)) :=
      ⟨TrivSqZeroExt.inr 1,
        mem_nilradical.mpr ⟨2, by simp [pow_two, TrivSqZeroExt.inr_mul_inr]⟩⟩
    have hm : q ∈ Module.support (TrivSqZeroExt (ZMod 2) (ZMod 2))
        (nilradical (TrivSqZeroExt (ZMod 2) (ZMod 2))) := by
      apply Module.mem_support_iff'.mpr
      refine ⟨m, ?_⟩
      intro r hr hzero
      have hfst : r.fst ∉ p.asIdeal := by
        simpa [q, PrimeSpectrum.comap_asIdeal] using hr
      have hr0 : r.fst ≠ 0 := by
        intro he
        exact hfst (he ▸ p.asIdeal.zero_mem)
      have hone : r.fst = 1 :=
        (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) r.fst hr0
      have hmul : r * TrivSqZeroExt.inr (1 : ZMod 2) =
          TrivSqZeroExt.inr (1 : ZMod 2) := by
        conv_lhs => rw [← r.inl_fst_add_inr_snd_eq]
        rw [add_mul, TrivSqZeroExt.inl_mul_inr,
          TrivSqZeroExt.inr_mul_inr, add_zero, hone, one_smul]
      have hzero' : r * TrivSqZeroExt.inr (1 : ZMod 2) = 0 := by
        simpa [m] using congrArg Subtype.val hzero
      have hnonzero :
          (TrivSqZeroExt.inr (1 : ZMod 2) :
            TrivSqZeroExt (ZMod 2) (ZMod 2)) ≠ 0 := by
        intro he
        exact (one_ne_zero : (1 : ZMod 2) ≠ 0)
          (by simpa using congrArg TrivSqZeroExt.snd he)
      exact hnonzero (hmul ▸ hzero')
    exact ((IsLocalization.AtPrime.isReduced_iff_not_mem_support_nilradical
      q (Localization.AtPrime q.asIdeal)).mp hred) hm
  exact ⟨p, hsupport, hnot⟩

/-- Vanishing module support does not make a nonreduced base localization reduced. -/
theorem nonreduced_base_zero_module :
    ∃ p : PrimeSpectrum (ZMod 4),
      p ∉ Module.support (ZMod 4) (⊥ : Ideal (ZMod 4)) ∧
        ¬ _root_.IsReduced (Localization.AtPrime p.asIdeal) := by
  have hnon : ¬ _root_.IsReduced (ZMod 4) := by
    intro h
    have hnil : IsNilpotent (2 : ZMod 4) := ⟨2, by decide⟩
    exact (by decide : (2 : ZMod 4) ≠ 0) (h.eq_zero 2 hnil)
  have hpoint : ∃ p : PrimeSpectrum (ZMod 4),
      ¬ _root_.IsReduced (Localization.AtPrime p.asIdeal) := by
    by_contra h
    apply hnon
    apply isReduced_ofLocalizationMaximal (ZMod 4)
    intro J hJ
    have hall : ∀ p : PrimeSpectrum (ZMod 4),
        _root_.IsReduced (Localization.AtPrime p.asIdeal) := by
      simpa only [not_exists, not_not] using h
    exact hall ⟨J, hJ.isPrime⟩
  obtain ⟨p, hp⟩ := hpoint
  exact ⟨p, by
    rw [Module.notMem_support_iff']
    intro m
    exact ⟨1, p.asIdeal.one_notMem, Subsingleton.elim _ _⟩, hp⟩

/-- An ideal in a product of two fields has support on exactly one component. -/
theorem product_ideal_mixed_support :
    ∃ p q : PrimeSpectrum (ZMod 2 × ZMod 2),
      p ∈ Module.support (ZMod 2 × ZMod 2)
        (RingHom.ker (RingHom.snd (ZMod 2) (ZMod 2))) ∧
      q ∉ Module.support (ZMod 2 × ZMod 2)
        (RingHom.ker (RingHom.snd (ZMod 2) (ZMod 2))) := by
  classical
  let fieldPrime : PrimeSpectrum (ZMod 2) := Classical.choice inferInstance
  let p := PrimeSpectrum.comap (RingHom.fst (ZMod 2) (ZMod 2)) fieldPrime
  let q := PrimeSpectrum.comap (RingHom.snd (ZMod 2) (ZMod 2)) fieldPrime
  have hp : p ∈ Module.support (ZMod 2 × ZMod 2)
      (RingHom.ker (RingHom.snd (ZMod 2) (ZMod 2))) := by
    apply Module.mem_support_iff'.mpr
    let m : RingHom.ker (RingHom.snd (ZMod 2) (ZMod 2)) :=
      ⟨(1, 0), by simp [RingHom.mem_ker]⟩
    refine ⟨m, ?_⟩
    intro r hr hzero
    have hr0 : r.1 ≠ 0 := by
      intro he
      apply hr
      change r.1 ∈ fieldPrime.asIdeal
      exact he ▸ fieldPrime.asIdeal.zero_mem
    have hfst : r.1 = 0 := by
      have he := congrArg (fun a : RingHom.ker (RingHom.snd (ZMod 2) (ZMod 2)) =>
        a.val.1) hzero
      simpa [m] using he
    exact hr0 hfst
  have hq : q ∉ Module.support (ZMod 2 × ZMod 2)
      (RingHom.ker (RingHom.snd (ZMod 2) (ZMod 2))) := by
    apply Module.notMem_support_iff'.mpr
    intro m
    refine ⟨(0, 1), ?_, ?_⟩
    · intro hr
      have hmem : (1 : ZMod 2) ∈ fieldPrime.asIdeal := by
        simpa [q, PrimeSpectrum.comap_asIdeal] using hr
      exact fieldPrime.asIdeal.one_notMem hmem
    · have hm : m.val.2 = 0 := (RingHom.mem_ker).mp m.property
      apply Subtype.ext
      apply Prod.ext
      · simp
      · simp [hm]
  exact ⟨p, q, hp, hq⟩

/-- The infinite free module over a field is supported at every prime. -/
theorem infinite_free_module_supported (p : PrimeSpectrum (ZMod 2)) :
    p ∈ Module.support (ZMod 2) (ℕ →₀ ZMod 2) := by
  rw [Module.support_of_isTorsionFree]
  trivial
