/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.GenericPointRationalNoninvertibility
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Algebra.Field.ZMod

set_option warningAsError true

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SchemePropertiesTest.GenericPointRationalNoninvertibility

private abbrev affineLine := Spec (CommRingCat.of (Polynomial ℚ))

private instance affineLine_nontrivial : Nontrivial affineLine :=
  Scheme.nontrivial_spec_polynomial ℚ

private def affineLineToPoint : affineLine ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ))

private theorem affineLineToPoint_finiteType : LocallyOfFiniteType affineLineToPoint := by
  unfold affineLineToPoint
  apply (HasRingHomProperty.Spec_iff).2
  change (Polynomial.C : ℚ →+* Polynomial ℚ).FiniteType
  have hC : (Polynomial.C : ℚ →+* Polynomial ℚ) =
      algebraMap ℚ (Polynomial ℚ) :=
    RingHom.ext fun element => Polynomial.C_eq_algebraMap element
  rw [hC, RingHom.finiteType_algebraMap]
  infer_instance

private theorem affineLine_boundary :
    LocallyOfFiniteType affineLineToPoint ∧
      ¬ LocallyOfFiniteType
        (affineLine.fromSpecStalk (genericPoint affineLine) ≫ affineLineToPoint) ∧
      IsIso (Scheme.genericPointRationalHom affineLine affineLineToPoint).toRationalMap.functionFieldMap ∧
      ¬ IsIso (Scheme.genericPointRationalHom affineLine affineLineToPoint) := by
  exact ⟨affineLineToPoint_finiteType,
    Scheme.not_locallyOfFiniteType_fromSpecStalk_genericPoint_comp
      affineLine affineLineToPoint,
    (Scheme.genericPointRationalHom_boundary affineLine affineLineToPoint).1,
    (Scheme.genericPointRationalHom_boundary affineLine affineLineToPoint).2⟩

private abbrev finiteLine := Spec (CommRingCat.of (Polynomial (ZMod 2)))

private instance finiteLine_nontrivial : Nontrivial finiteLine :=
  Scheme.nontrivial_spec_polynomial (ZMod 2)

private theorem finite_field_boundary :
    IsIso (Scheme.genericPointRationalHom finiteLine (𝟙 finiteLine)).toRationalMap.functionFieldMap ∧
      ¬ IsIso (Scheme.genericPointRationalHom finiteLine (𝟙 finiteLine)) :=
  Scheme.genericPointRationalHom_boundary finiteLine (𝟙 finiteLine)

end SchemePropertiesTest.GenericPointRationalNoninvertibility
