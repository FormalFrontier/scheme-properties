/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.PolynomialPointReducedLocus
import Mathlib.Data.Rat.Cast.Lemmas

@[expose] public section

set_option warningAsError true

/-!
# Uses of polynomial point-module support and reduced-locus statements

The conclusions in this module use the support and reduced-locus statements.
Independent point-family fixtures are in `PolynomialPointFixtures`.
-/

open scoped TrivSqZeroExt

namespace Polynomial

example : Module.support ℚ[X]
    (DirectSum (Fin 2) (fun i => ℚ[X] ⧸ RingHom.ker
      (evalRingHom (if i = 0 then (0 : ℚ) else 1)))) =
    Set.range (fun i : Fin 2 => evalPrime (if i = 0 then (0 : ℚ) else 1)) :=
  support_directSum_evalQuotient_eq_range _

/-- An infinite constant family has closed support. -/
theorem constant_rat_point_family_isClosed_support : IsClosed (Module.support ℚ[X]
    (DirectSum ℕ (fun _ => ℚ[X] ⧸ RingHom.ker (evalRingHom (0 : ℚ))))) :=
  (isClosed_support_directSum_evalQuotient_iff_finite_range
    (fun _ : ℕ => (0 : ℚ))).mpr Set.finite_range_const

/-- The infinite-image rational point family has a non-open reduced locus. -/
theorem infinite_rat_point_family_reduced_locus_not_isOpen : ¬ IsOpen {q : PrimeSpectrum
    (TrivSqZeroExt ℚ[X]
      (DirectSum ℕ (fun n => ℚ[X] ⧸ RingHom.ker (evalRingHom ((n + 1 : ℕ) : ℚ))))) |
    _root_.IsReduced (Localization.AtPrime q.asIdeal)} := by
  intro hopen
  have hfinite := (isOpen_reduced_atPrime_directSum_evalQuotient_iff_finite_range
    (fun n : ℕ => ((n + 1 : ℕ) : ℚ))).mp hopen
  exact (Set.infinite_range_of_injective (fun m n h =>
    Nat.add_right_cancel (Nat.cast_injective h))) hfinite

end Polynomial
