/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.AffineTestSheaf

/-!
# Descent through the singleton sheaf API

A compatible morphism on an affine test descends uniquely as a morphism over the
given base, by applying the singleton sheaf criterion to its universe lift.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

example {B : Scheme.{u}} (Y : Over B)
    {U V : CostructuredArrow Scheme.Spec B} (f : U ⟶ V)
    [Flat (Scheme.Spec.map f.left)] [Surjective (Scheme.Spec.map f.left)]
    (e : (CostructuredArrow.toOver Scheme.Spec B).obj U ⟶ Y)
    (he : ∀ {W : CostructuredArrow Scheme.Spec B} (p₁ p₂ : W ⟶ U),
      p₁ ≫ f = p₂ ≫ f →
        (CostructuredArrow.toOver Scheme.Spec B).map p₁ ≫ e =
          (CostructuredArrow.toOver Scheme.Spec B).map p₂ ≫ e) :
    ∃! d : (CostructuredArrow.toOver Scheme.Spec B).obj V ⟶ Y,
      (CostructuredArrow.toOver Scheme.Spec B).map f ≫ d = e := by
  have hs := isSheafFor_singleton_restrictedULiftYoneda_toOver.{u, 0} Y f
  obtain ⟨d, hd, hu⟩ := (Presieve.isSheafFor_singleton.mp hs) (ULift.up e) (by
    intro W p₁ p₂ h
    exact congrArg ULift.up (he p₁ p₂ h))
  refine ⟨d.down, congrArg ULift.down hd, ?_⟩
  intro d' hd'
  exact congrArg ULift.down (hu (ULift.up d') (congrArg ULift.up hd'))

end AlgebraicGeometry.Scheme
