/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.AffineDensity
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.AlgebraicGeometry.Limits

/-!
# Affine reconstruction and the zero-ring boundary

The affine reconstruction example recovers a natural transformation out of the affine
line over `ℤ` by evaluating at its identity test point, using the density instance and
Mathlib's existing fully faithful reconstruction data.

The two standard polynomial evaluation points are distinct by Γ–Spec faithfulness and
polynomial evaluation alone, independently of the density result. The zero-ring
boundary likewise uses only Mathlib's existing empty-spectrum and initial-object APIs.
No new points functor or affine model is defined here.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u

-- Independent nonvacuity witness: the affine line over ℤ has distinct zero and unit sections.
example :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℤ))) ≠
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : ℤ))) := by
  intro h
  have hX := congrArg
    (fun f : CommRingCat.of (Polynomial ℤ) ⟶ CommRingCat.of ℤ => f.hom Polynomial.X)
    (Spec.map_injective h)
  exact (zero_ne_one : (0 : ℤ) ≠ 1) <| calc
    (0 : ℤ) = (Polynomial.X : Polynomial ℤ).eval 0 := Polynomial.eval_X.symm
    _ = (Polynomial.X : Polynomial ℤ).eval 1 := hX
    _ = 1 := Polynomial.eval_X

-- Recover a transformation from affine-line points by its value on the identity.
example (X : Scheme.{0})
    (α : (Presheaf.restrictedULiftYoneda.{0} Scheme.Spec).obj
        (Spec (CommRingCat.of (Polynomial ℤ))) ⟶
      (Presheaf.restrictedULiftYoneda.{0} Scheme.Spec).obj X) :
    (Functor.FullyFaithful.ofFullyFaithful
      (Presheaf.restrictedULiftYoneda.{0} Scheme.Spec)).preimage α =
      (α.app (op (op (CommRingCat.of (Polynomial ℤ))))
        (ULift.up (𝟙 (Spec (CommRingCat.of (Polynomial ℤ)))))).down := by
  have h := ConcreteCategory.congr_hom (CC := fun Y ↦ Y)
    (NatTrans.congr_app
      ((Functor.FullyFaithful.ofFullyFaithful
        (Presheaf.restrictedULiftYoneda.{0} Scheme.Spec)).map_preimage α)
      (op (op (CommRingCat.of (Polynomial ℤ)))))
    (ULift.up (𝟙 (Spec (CommRingCat.of (Polynomial ℤ)))))
  have h' := congrArg ULift.down h
  change
    (𝟙 _) ≫
        (Functor.FullyFaithful.ofFullyFaithful
          (Presheaf.restrictedULiftYoneda.{0} Scheme.Spec)).preimage α =
      (α.app (op (op (CommRingCat.of (Polynomial ℤ))))
        (ULift.up (𝟙 (Spec (CommRingCat.of (Polynomial ℤ)))))).down at h'
  simpa only [Category.id_comp] using h'

-- Independent boundary: Spec of the zero ring is empty, and its points in every X are unique.
example (X : Scheme.{u}) :
    IsEmpty (Spec (CommRingCat.of PUnit.{u + 1})) ∧
      Subsingleton (Spec (CommRingCat.of PUnit.{u + 1}) ⟶ X) ∧
      Nonempty (Spec (CommRingCat.of PUnit.{u + 1}) ⟶ X) := by
  exact ⟨inferInstance,
    ⟨fun f g ↦ specPUnitIsInitial.hom_ext f g⟩,
    ⟨specPUnitIsInitial.to X⟩⟩
