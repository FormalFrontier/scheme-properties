/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.FiniteType
import SchemeProperties.GeometricPointLifting

/-!
# Geometric-point lifting for the affine line

The affine-line projection is induced by the inclusion of constants into a polynomial ring.
Evaluation at zero gives a section and, by composition, lifts points over every test field.
-/

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable (K : Type u) [Field K]

private noncomputable def affineLineProjection : Spec (.of (Polynomial K)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K))

private noncomputable def affineLineZeroSection : Spec (.of K) ⟶ Spec (.of (Polynomial K)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K)))

private theorem affineLineZeroSection_comp :
    affineLineZeroSection K ≫ affineLineProjection K = 𝟙 _ := by
  have h : CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : K)) = 𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    ext a
    exact Polynomial.eval_C
  dsimp only [affineLineZeroSection, affineLineProjection]
  rw [← Spec.map_comp, h, Spec.map_id]

private instance affineLineProjection_locallyOfFiniteType :
    LocallyOfFiniteType (affineLineProjection K) := by
  change LocallyOfFiniteType (Spec.map
    (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K)))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (algebraMap K (Polynomial K)).FiniteType
  exact RingHom.finiteType_algebraMap.mpr
    (inferInstance : Algebra.FiniteType K (Polynomial K))

private instance affineLineProjection_surjective : Surjective (affineLineProjection K) where
  surj y := ⟨affineLineZeroSection K y, by
    simpa [Scheme.Hom.comp_apply] using
      congrArg (fun g : Spec (.of K) ⟶ Spec (.of K) => g y)
        (affineLineZeroSection_comp K)⟩

private theorem affineLine_lifts (L : Type u) [Field L] [IsAlgClosed L]
    (p : Spec (.of L) ⟶ Spec (.of K)) :
    ∃ q : Spec (.of L) ⟶ Spec (.of (Polynomial K)), q ≫ affineLineProjection K = p := by
  refine ⟨p ≫ affineLineZeroSection K, ?_⟩
  rw [Category.assoc, affineLineZeroSection_comp, Category.comp_id]

private theorem affineLine_surjective_via_lifts : Surjective (affineLineProjection K) :=
  Scheme.Hom.surjective_of_lifts_from_isAlgClosed (affineLineProjection K) (affineLine_lifts K)

private theorem affineLine_lifts_via_iff (L : Type u) [Field L] [IsAlgClosed L]
    (p : Spec (.of L) ⟶ Spec (.of K)) :
    ∃ q : Spec (.of L) ⟶ Spec (.of (Polynomial K)), q ≫ affineLineProjection K = p :=
  (Scheme.Hom.surjective_iff_lifts_from_isAlgClosed (affineLineProjection K)).mp
    (affineLineProjection_surjective K) L p

private theorem affineLine_exists_lift [IsAlgClosed K] :
    ∃ q : Spec (.of K) ⟶ Spec (.of (Polynomial K)), q ≫ affineLineProjection K = 𝟙 _ :=
  Scheme.Hom.exists_lift_of_isAlgClosed (affineLineProjection K) (𝟙 _)

end AlgebraicGeometry
