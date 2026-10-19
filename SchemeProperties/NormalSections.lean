/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.FunctionField.Sections
public import SchemeProperties.Normal

/-!
# Integrally closed sections of normal integral schemes

Sections on a nonempty open set of a normal integral scheme are integrally
closed in the scheme's function field. Intrinsic integral closedness holds for
every open set, including the empty open set, whose section ring is the zero ring.

There is no assertion that the function field is a fraction ring of the section
ring on an arbitrary open set. The domain property for nonempty opens is already
provided by `AlgebraicGeometry.IsIntegral.component_integral`.

The proofs use Mathlib's canonical section and stalk maps, the fraction-ring
structure of stalks in the function field, and integral-closedness descent.
-/

public section

universe u

namespace AlgebraicGeometry.IsNormal

/-- Sections on a nonempty open set of a normal integral scheme are integrally
closed in its function field, with respect to the canonical algebra map. -/
theorem isIntegrallyClosedIn_sections {X : Scheme.{u}} [IsNormal X] [IsIntegral X]
    (U : X.Opens) [Nonempty U] : IsIntegrallyClosedIn Γ(X, U) X.functionField := by
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, ?_⟩
  · exact X.germToFunctionField_injective U
  · intro f hf
    apply (Scheme.mem_range_algebraMap_functionField_iff (X := X) U f).mpr
    intro x
    let _ : Algebra Γ(X, U) (X.presheaf.stalk x.1) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf x
    let _ : IsScalarTower Γ(X, U) (X.presheaf.stalk x.1) X.functionField :=
      functionField_isScalarTower X U x
    exact IsIntegrallyClosed.algebraMap_eq_of_integral
      (IsIntegral.tower_top (A := X.presheaf.stalk x.1) hf)

/-- The section ring on every open set of a normal integral scheme is integrally
closed. This includes the zero ring of sections on the empty open set. -/
theorem isIntegrallyClosed_sections {X : Scheme.{u}} [IsNormal X] [IsIntegral X]
    (U : X.Opens) : IsIntegrallyClosed Γ(X, U) := by
  classical
  by_cases hU : Nonempty U
  · let _ : Nonempty U := hU
    let _ : IsIntegrallyClosedIn Γ(X, U) X.functionField :=
      isIntegrallyClosedIn_sections U
    let _ : FaithfulSMul Γ(X, U) X.functionField :=
      IsIntegralClosure.faithfulSMul Γ(X, U) Γ(X, U) X.functionField
    exact IsIntegrallyClosed.of_isIntegrallyClosedIn Γ(X, U) X.functionField
  · have hUempty : U = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      exact (hU ⟨⟨x, hx⟩⟩).elim
    let _ : Subsingleton Γ(X, U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hUempty)
    let _ : Unique (FractionRing Γ(X, U)) := FractionRing.unique _
    refine isIntegrallyClosedIn_iff.mpr ⟨?_, ?_⟩
    · intro a b _
      exact Subsingleton.elim a b
    · intro f _
      exact ⟨0, Subsingleton.elim _ _⟩

end AlgebraicGeometry.IsNormal
