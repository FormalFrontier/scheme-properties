/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RationalPointExtensionality
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Maps.Basic

/-!
# Zariski topology on rational points

For a scheme over a field `K`, its rational points are the morphisms from the
Cartesian unit in `CategoryTheory.Over (Spec (.of K))`. Evaluation at the closed
point of `Spec K` induces their Zariski topology from the underlying scheme.
This is a topological embedding: the section-extensionality theorem in
`SchemeProperties.RationalPointExtensionality` identifies points with equal evaluations.
Every morphism over `K` acts continuously on rational points, and Cartesian
lifting is continuous in either coordinate when the other point is fixed.
The rational-point space is T₁: each section of a field spectrum is a closed immersion.

## Limitations

This is the scheme-induced Zariski topology, not an analytic topology on `K`.
Mathlib's Cartesian Hom equivalence compares product points with pairs as sets;
it need not be a homeomorphism for the ordinary product topology. Continuity in
each fixed coordinate does not assert joint continuity of pairing or group operations.

## References

The construction uses Mathlib's Cartesian structure on slice categories and its
induced-topology API, together with the section-extensionality theorem above:

- [Cartesian slice categories](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/CategoryTheory/Monoidal/Cartesian/Over.lean).
- [Inducing maps and embeddings](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Maps/Basic.lean).
- [Closed immersions and sections of subsingleton schemes](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean).
- [Section extensionality over a field](https://github.com/FormalFrontier/scheme-properties/blob/aa114bd527bb14002a1e337c33cc25f841484093/SchemeProperties/RationalPointExtensionality.lean).
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.Scheme

universe u

variable {K : Type u} [Field K]

/-- Evaluation of a rational point at the closed point of the spectrum of its base field. -/
def pointEval (X : CategoryTheory.Over (Spec (.of K))) :
    (𝟙_ (CategoryTheory.Over (Spec (.of K))) ⟶ X) → X.left :=
  fun p ↦ p.left (IsLocalRing.closedPoint K)

/-- Evaluation is the underlying scheme morphism applied to the closed point. -/
theorem pointEval_apply (X : CategoryTheory.Over (Spec (.of K)))
    (p : 𝟙_ (CategoryTheory.Over (Spec (.of K))) ⟶ X) :
    pointEval X p = p.left (IsLocalRing.closedPoint K) := rfl

/-- The Zariski topology on rational points, induced from the underlying scheme by evaluation. -/
instance pointTopology (X : CategoryTheory.Over (Spec (.of K))) :
    TopologicalSpace (𝟙_ (CategoryTheory.Over (Spec (.of K))) ⟶ X) :=
  TopologicalSpace.induced (pointEval X) inferInstance

variable {X Y : CategoryTheory.Over (Spec (.of K))}

/-- Evaluation commutes with postcomposition by a morphism over the base field. -/
@[simp]
theorem pointEval_comp (p : 𝟙_ (CategoryTheory.Over (Spec (.of K))) ⟶ X) (f : X ⟶ Y) :
    pointEval Y (p ≫ f) = f.left (pointEval X p) :=
  AlgebraicGeometry.Scheme.Hom.comp_apply p.left f.left _

/-- Evaluation induces the Zariski topology on rational points. -/
theorem isInducing_pointEval (X : CategoryTheory.Over (Spec (.of K))) :
    Topology.IsInducing (pointEval X) :=
  Topology.IsInducing.induced _

/-- Rational points embed topologically into the underlying scheme by evaluation. -/
theorem isEmbedding_pointEval (X : CategoryTheory.Over (Spec (.of K))) :
    Topology.IsEmbedding (pointEval X) := by
  refine ⟨isInducing_pointEval X, ?_⟩
  intro p q h
  apply CategoryTheory.Over.OverMorphism.ext
  exact Hom.ext_of_apply_closedPoint_eq_of_comp_eq_id X.hom
    (by simpa only [CategoryTheory.Over.tensorUnit_hom] using p.w)
    (by simpa only [CategoryTheory.Over.tensorUnit_hom] using q.w) h

/-- The Zariski topology on rational points is T₁. -/
instance pointT1Space (X : CategoryTheory.Over (Spec (.of K))) :
    T1Space (𝟙_ (CategoryTheory.Over (Spec (.of K))) ⟶ X) where
  t1 p := by
    have : IsClosedImmersion p.left :=
      AlgebraicGeometry.isClosedImmersion_of_comp_eq_id X.hom p.left
        (by simpa only [CategoryTheory.Over.tensorUnit_hom] using p.w)
    have hr : Set.range p.left = {pointEval X p} :=
      Set.range_eq_singleton (f := fun z : Spec (.of K) ↦ p.left z) fun z ↦
        congrArg p.left (Subsingleton.elim z (IsLocalRing.closedPoint K))
    have hc : IsClosed ({pointEval X p} : Set X.left) := by
      rw [← hr]
      exact p.left.isClosedEmbedding.isClosed_range
    have hp := (isInducing_pointEval X).isClosed_preimage _ hc
    rwa [← Set.image_singleton (f := pointEval X),
      Set.preimage_image_eq _ (isEmbedding_pointEval X).injective] at hp

/-- Every morphism over the base field acts continuously on rational points. -/
theorem continuous_point_comp (f : X ⟶ Y) :
    Continuous (fun p : 𝟙_ (CategoryTheory.Over (Spec (.of K))) ⟶ X => p ≫ f) := by
  apply (isInducing_pointEval Y).continuous_iff.mpr
  simpa only [Function.comp_def, pointEval_comp] using
    f.left.continuous.comp (isInducing_pointEval X).continuous

/-- Cartesian lifting is continuous in the left coordinate for a fixed right rational point. -/
theorem continuous_point_lift_left
    (y : 𝟙_ (CategoryTheory.Over (Spec (.of K))) ⟶ Y) :
    Continuous (fun x : 𝟙_ (CategoryTheory.Over (Spec (.of K))) ⟶ X => lift x y) := by
  simpa only [comp_lift, Category.comp_id, comp_toUnit_assoc, toUnit_unit,
    Category.id_comp] using continuous_point_comp (lift (𝟙 X) (toUnit X ≫ y))

/-- Cartesian lifting is continuous in the right coordinate for a fixed left rational point. -/
theorem continuous_point_lift_right
    (x : 𝟙_ (CategoryTheory.Over (Spec (.of K))) ⟶ X) :
    Continuous (fun y : 𝟙_ (CategoryTheory.Over (Spec (.of K))) ⟶ Y => lift x y) := by
  simpa only [comp_lift, comp_toUnit_assoc, toUnit_unit, Category.id_comp,
    Category.comp_id] using continuous_point_comp (lift (toUnit Y ≫ x) (𝟙 Y))

end AlgebraicGeometry.Scheme
