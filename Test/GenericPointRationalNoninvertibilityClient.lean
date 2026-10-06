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

attribute [local instance] AlgebraicGeometry.Scheme.nontrivial_spec_polynomial

example : LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ))) := by
  apply (HasRingHomProperty.Spec_iff).2
  change (Polynomial.C : ℚ →+* Polynomial ℚ).FiniteType
  have hC : (Polynomial.C : ℚ →+* Polynomial ℚ) =
      algebraMap ℚ (Polynomial ℚ) :=
    RingHom.ext fun element => Polynomial.C_eq_algebraMap element
  rw [hC, RingHom.finiteType_algebraMap]
  infer_instance

example :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ))) ∧
      ¬ LocallyOfFiniteType
        ((Spec (CommRingCat.of (Polynomial ℚ))).fromSpecStalk
          (genericPoint (Spec (CommRingCat.of (Polynomial ℚ)))) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ))) ∧
      IsIso (Scheme.genericPointRationalHom
        (Spec (CommRingCat.of (Polynomial ℚ)))
        (Spec.map (CommRingCat.ofHom
          (Polynomial.C : ℚ →+* Polynomial ℚ)))).toRationalMap.functionFieldMap ∧
      ¬ IsIso (Scheme.genericPointRationalHom
        (Spec (CommRingCat.of (Polynomial ℚ)))
        (Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ)))) := by
  have hFiniteType : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ))) := by
    apply (HasRingHomProperty.Spec_iff).2
    change (Polynomial.C : ℚ →+* Polynomial ℚ).FiniteType
    have hC : (Polynomial.C : ℚ →+* Polynomial ℚ) =
        algebraMap ℚ (Polynomial ℚ) :=
      RingHom.ext fun element => Polynomial.C_eq_algebraMap element
    rw [hC, RingHom.finiteType_algebraMap]
    infer_instance
  exact ⟨hFiniteType,
    Scheme.not_locallyOfFiniteType_fromSpecStalk_genericPoint_comp
      (Spec (CommRingCat.of (Polynomial ℚ)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ))),
    (Scheme.genericPointRationalHom_boundary
      (Spec (CommRingCat.of (Polynomial ℚ)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ)))).1,
    (Scheme.genericPointRationalHom_boundary
      (Spec (CommRingCat.of (Polynomial ℚ)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : ℚ →+* Polynomial ℚ)))).2⟩

example :
    IsIso (Scheme.genericPointRationalHom
      (Spec (CommRingCat.of (Polynomial (ZMod 2))))
      (𝟙 (Spec (CommRingCat.of (Polynomial (ZMod 2)))))).toRationalMap.functionFieldMap ∧
      ¬ IsIso (Scheme.genericPointRationalHom
        (Spec (CommRingCat.of (Polynomial (ZMod 2))))
        (𝟙 (Spec (CommRingCat.of (Polynomial (ZMod 2)))))) :=
  Scheme.genericPointRationalHom_boundary
    (Spec (CommRingCat.of (Polynomial (ZMod 2))))
    (𝟙 (Spec (CommRingCat.of (Polynomial (ZMod 2)))))

end SchemePropertiesTest.GenericPointRationalNoninvertibility
