/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import SchemeProperties.SpecHomDescent

/-! A morphism already defined on the base is recovered uniquely by tensor descent,
compatibly with any supplied map to an arbitrary base scheme. -/

open CategoryTheory CategoryTheory.Limits TensorProduct Algebra.TensorProduct
  CommRingCat RingHomClass AlgebraicGeometry

universe u

example {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hff : (algebraMap R A).FaithfullyFlat) (B X : Scheme.{u})
    (d : Spec (.of R) ⟶ X) (p : X ⟶ B) :
    ∃! d' : Spec (.of R) ⟶ X,
      Spec.map (ofHom (algebraMap R A)) ≫ d' = Spec.map (ofHom (algebraMap R A)) ≫ d ∧
        d' ≫ p = d ≫ p := by
  apply Scheme.existsUnique_spec_desc_over_of_faithfullyFlat hff B X (d ≫ p) p
  · rw [← pullbackSpecIso_inv_fst R A A, ← pullbackSpecIso_inv_snd R A A]
    simp only [Category.assoc, pullback.condition_assoc]
  · exact Category.assoc _ _ _
