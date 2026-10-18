/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Lifting geometric points

A locally finite type morphism of schemes is surjective if and only if every point valued in
an algebraically closed field lifts over that same field. The implication from lifting to
surjectivity does not require the locally finite type hypothesis.

## References

The closed-point interpretation of points over an algebraically closed field is formalized by
Andrew Yang in Mathlib's `Mathlib.AlgebraicGeometry.AlgClosed.Basic`.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}}

/-- Every point valued in an algebraically closed field lifts along a surjective locally finite
type morphism, without extending the field.

Local finite type supplies a closed point in the nonempty fiber whose residue field is the test
field. Without this hypothesis, `Spec K(t) → Spec K` can be surjective
without a `K`-valued point. -/
theorem exists_lift_of_isAlgClosed (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f]
    {K : Type u} [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ Y) :
    ∃ q : Spec (.of K) ⟶ X, q ≫ f = p := by
  let P : Scheme.{u} := Limits.pullback f p
  let g : P ⟶ Spec (.of K) := Limits.pullback.snd f p
  have hP : (Set.univ : Set P).Nonempty := by
    obtain ⟨x, -⟩ := g.surjective (IsLocalRing.closedPoint K)
    exact ⟨x, Set.mem_univ x⟩
  have : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace g
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints hP isOpen_univ.isLocallyClosed
  have hx' : IsClosed ({x} : Set P) := mem_closedPoints_iff.mp hx
  refine ⟨pointOfClosedPoint g x hx' ≫ Limits.pullback.fst f p, ?_⟩
  rw [Category.assoc, Limits.pullback.condition, ← Category.assoc,
    pointOfClosedPoint_comp, Category.id_comp]

/-- A morphism of schemes is surjective if every point valued in an algebraically closed field
lifts over that same field. -/
theorem surjective_of_lifts_from_isAlgClosed (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ Y),
      ∃ q : Spec (.of K) ⟶ X, q ≫ f = p) : Surjective f := by
  constructor
  intro y
  let K := AlgebraicClosure (Y.residueField y)
  obtain ⟨q, hq⟩ := h K (Spec.algebraMap (Y.residueField y) K ≫
    Y.fromSpecResidueField y)
  refine ⟨q (default : Spec (.of K)), ?_⟩
  have hqy := congrArg (fun g : Spec (.of K) ⟶ Y => g (default : Spec (.of K))) hq
  simp only [Scheme.Hom.comp_apply] at hqy
  exact hqy.trans (Scheme.fromSpecResidueField_apply y _)

/-- A locally finite type morphism of schemes is surjective if and only if every point valued
in an algebraically closed field lifts over that same field. -/
theorem surjective_iff_lifts_from_isAlgClosed (f : X ⟶ Y) [LocallyOfFiniteType f] :
    Surjective f ↔ ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ Y),
      ∃ q : Spec (.of K) ⟶ X, q ≫ f = p := by
  constructor
  · intro hf
    let : Surjective f := hf
    intro K _ _ p
    exact exists_lift_of_isAlgClosed f p
  · exact surjective_of_lifts_from_isAlgClosed f

end AlgebraicGeometry.Scheme.Hom
