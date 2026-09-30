/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.JacobsonBirationalObstruction
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Field.ZMod

set_option warningAsError true

open AlgebraicGeometry CategoryTheory
open scoped Polynomial

universe u

namespace SchemePropertiesTest.JacobsonBirationalObstruction

private theorem general {X Y : Scheme.{u}} [Subsingleton X] [JacobsonSpace Y]
    (p : Scheme.PartialIso X Y) : Subsingleton Y :=
  p.subsingleton_target

private theorem generic_point :
    ¬Scheme.Birational (Spec (CommRingCat.of (RatFunc ℚ)))
      (Spec (CommRingCat.of ℚ[X])) :=
  Scheme.not_birational_spec_field_spec_polynomial (RatFunc ℚ) ℚ

private theorem finite_field :
    ¬Scheme.Birational (Spec (CommRingCat.of (ZMod 2)))
      (Spec (CommRingCat.of (ZMod 2)[X])) :=
  Scheme.not_birational_spec_field_spec_polynomial (ZMod 2) (ZMod 2)

private theorem empty_source {Y : Scheme} [JacobsonSpace Y] [Nontrivial Y] :
    ¬Scheme.Birational (Spec (CommRingCat.of (ZMod 1))) Y := by
  have hEmpty : IsEmpty (Spec (CommRingCat.of (ZMod 1))) :=
    PrimeSpectrum.isEmpty_iff_subsingleton.mpr (ZMod.subsingleton_iff.mpr rfl)
  have hSource : Subsingleton (Spec (CommRingCat.of (ZMod 1))) :=
    ⟨fun point _ => (hEmpty.false point).elim⟩
  exact @Scheme.not_birational_of_subsingleton_of_jacobson _ _ hSource
    inferInstance inferInstance

private noncomputable def identity_field : Scheme.PartialIso
    (Spec (CommRingCat.of ℚ)) (Spec (CommRingCat.of ℚ)) :=
  Scheme.PartialIso.refl _

end SchemePropertiesTest.JacobsonBirationalObstruction
