/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.TrivSqZeroExtReducedLocus
public import SchemePropertiesExamples.TrivSqZeroExtReducedLocus
import Mathlib.Data.Nat.Squarefree

@[expose] public section

set_option warningAsError true

/-!
# Applications of square-zero reduced-localization statements

These examples apply the square-zero statements to independently proved support
and localization witnesses. Unlike the witnesses, these applications rely on
the square-zero criterion and its topological consequences.
-/

open scoped TrivSqZeroExt

private instance : _root_.IsReduced (ZMod 2) :=
  isReduced_zmod.mpr (Or.inl Nat.squarefree_two)

/-- A vanishing module does not erase the nonreducedness of the base. -/
theorem zmod_four_zero_module_nonreduced_localization :
    ∃ p : PrimeSpectrum (ZMod 4),
    p ∉ Module.support (ZMod 4) (⊥ : Ideal (ZMod 4)) ∧
      ¬ _root_.IsReduced (Localization.AtPrime
        (PrimeSpectrum.comap (TrivSqZeroExt.fstHom (ZMod 4) (ZMod 4)
          (⊥ : Ideal (ZMod 4))).toRingHom p).asIdeal) := by
  obtain ⟨p, hp, hbase⟩ := nonreduced_base_zero_module
  refine ⟨p, hp, ?_⟩
  intro hred
  exact hbase ((TrivSqZeroExt.isReduced_atPrime_iff (M := (⊥ : Ideal (ZMod 4))) p
    (Localization.AtPrime (PrimeSpectrum.comap
      (TrivSqZeroExt.fstHom (ZMod 4) (ZMod 4)
        (⊥ : Ideal (ZMod 4))).toRingHom p).asIdeal)
    (Localization.AtPrime p.asIdeal)).mp hred).1

/-- An infinite free module produces nonreduced square-zero localizations over a field. -/
theorem infinite_free_module_nonreduced_localization (p : PrimeSpectrum (ZMod 2)) :
    ¬ _root_.IsReduced (Localization.AtPrime
      (PrimeSpectrum.comap (TrivSqZeroExt.fstHom (ZMod 2) (ZMod 2)
        (ℕ →₀ ZMod 2)).toRingHom p).asIdeal) := by
  intro hred
  have hs : p ∈ Module.support (ZMod 2) (ℕ →₀ ZMod 2) :=
    infinite_free_module_supported p
  exact ((TrivSqZeroExt.isReduced_atPrime_iff (M := ℕ →₀ ZMod 2) p
    (Localization.AtPrime (PrimeSpectrum.comap
      (TrivSqZeroExt.fstHom (ZMod 2) (ZMod 2)
        (ℕ →₀ ZMod 2)).toRingHom p).asIdeal)
    (Localization.AtPrime p.asIdeal)).mp hred).2 hs

/-- The two components of a reduced product exhibit different reducedness behavior
for the extension by an ideal supported on only one component. -/
theorem product_ideal_reduced_localizations_vary :
    ∃ p q : PrimeSpectrum (ZMod 2 × ZMod 2),
    ¬ _root_.IsReduced (Localization.AtPrime
      (PrimeSpectrum.comap (TrivSqZeroExt.fstHom (ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2)
        (RingHom.ker (RingHom.snd (ZMod 2) (ZMod 2)))).toRingHom p).asIdeal) ∧
      _root_.IsReduced (Localization.AtPrime
        (PrimeSpectrum.comap (TrivSqZeroExt.fstHom (ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2)
          (RingHom.ker (RingHom.snd (ZMod 2) (ZMod 2)))).toRingHom q).asIdeal) := by
  obtain ⟨p, q, hp, hq⟩ := product_ideal_mixed_support
  have hset := TrivSqZeroExt.reduced_atPrime_comap_eq_compl_support
    (R := ZMod 2 × ZMod 2)
    (M := RingHom.ker (RingHom.snd (ZMod 2) (ZMod 2)))
  refine ⟨p, q, ?_, ?_⟩
  · intro hred
    have hcomplement : p ∈ (Module.support (ZMod 2 × ZMod 2)
        (RingHom.ker (RingHom.snd (ZMod 2) (ZMod 2))))ᶜ := by
      rw [← hset]
      exact hred
    exact hcomplement hp
  · have hcomplement : q ∈ (Module.support (ZMod 2 × ZMod 2)
        (RingHom.ker (RingHom.snd (ZMod 2) (ZMod 2))))ᶜ := hq
    rw [← hset] at hcomplement
    exact hcomplement

/-- The reduced localization locus of the dual-number ring is open despite its
nonreduced localization at the prime over the field. -/
theorem dual_numbers_reduced_locus_isOpen :
    IsOpen {q : PrimeSpectrum (TrivSqZeroExt (ZMod 2) (ZMod 2)) |
    _root_.IsReduced (Localization.AtPrime q.asIdeal)} := by
  exact (TrivSqZeroExt.isOpen_reduced_atPrime_iff_isClosed_support
    (R := ZMod 2) (M := ZMod 2)).mpr Module.isClosed_support
