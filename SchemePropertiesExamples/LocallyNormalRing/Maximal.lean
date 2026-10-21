/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.LocallyNormalRing.Maximal
public import SchemePropertiesExamples.LocallyNormalPi
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Ring.PUnit

/-!
# Maximal-localization clients

The integers satisfy the maximal-localization criterion using their stock domain
and GCD structure, and have a maximal ideal. The zero ring `PUnit` has empty prime
spectrum, so its independently constructed local normality gives the maximal
condition as well.
-/

deprecated_module (since := "2026-10-21")
