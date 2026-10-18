/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.RationalPointExtensionality
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Coordinate uses of rational-point extensionality

The affine line over the rationals supplies sections and their structural identities
independently of extensionality. Equality of their image points then implies equality
of their rational coordinates. For an affine line over an algebraically closed field,
the closed-point sections determine the action of an endomorphism on its coordinate.

The compatibility lemmas compare the generalized criteria with Mathlib's criteria
under the latter's hypotheses, without changing any of the morphisms or scalar data.
The constructions and coordinate formulas are Mathlib's affine-space and residue-field
APIs, due to its contributors, especially Andrew Yang.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

private lemma closedPoint_ext_compatibility
    {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}}
    {f g : Spec ↧K ⟶ Y} (i : Y ⟶ Spec ↧K) [LocallyOfFiniteType i]
    (hf : f ≫ i = 𝟙 _) (hg : g ≫ i = 𝟙 _)
    (H : f (IsLocalRing.closedPoint K) = g (IsLocalRing.closedPoint K)) :
    Scheme.Hom.ext_of_apply_closedPoint_eq_of_comp_eq_id i hf hg H =
      AlgebraicGeometry.ext_of_apply_closedPoint_eq i hf hg H :=
  Subsingleton.elim _ _

private lemma dense_closedPoints_ext_compatibility
    {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    {f g : X ⟶ Y} (i : Y ⟶ Spec ↧K) [IsSeparated i] [LocallyOfFiniteType i]
    [IsReduced X] [LocallyOfFiniteType (f ≫ i)]
    (S : Set X) (hS : IsLocallyClosed S) (hS' : Dense S)
    (H : ∀ x ∈ S, IsClosed {x} → f x = g x)
    (H' : f ≫ i = g ≫ i) :
    Scheme.Hom.ext_of_apply_eq_on_dense_closedPoints i S hS hS' H H' =
      AlgebraicGeometry.ext_of_apply_eq i S hS hS' H H' :=
  Subsingleton.elim _ _

/-- The zero coordinate constructs a closed section over the rationals directly. -/
example : IsClosedImmersion
    (AffineSpace.homOfVector (𝟙 (Spec ↧ℚ))
      (fun _ : PUnit => (Scheme.ΓSpecIso ↧ℚ).inv 0)) := by
  exact isClosedImmersion_of_comp_eq_id
    (AffineSpace PUnit (Spec ↧ℚ) ↘ Spec ↧ℚ) _
    (AffineSpace.homOfVector_over _ _)

/-- Point agreement for two coordinate sections forces equality of their rational parameters. -/
example (a b : ℚ)
    (H : (AffineSpace.homOfVector (𝟙 (Spec ↧ℚ))
        (fun _ : PUnit => (Scheme.ΓSpecIso ↧ℚ).inv a)) (IsLocalRing.closedPoint ℚ) =
      (AffineSpace.homOfVector (𝟙 (Spec ↧ℚ))
        (fun _ : PUnit => (Scheme.ΓSpecIso ↧ℚ).inv b)) (IsLocalRing.closedPoint ℚ)) :
    a = b := by
  let s : Spec ↧ℚ ⟶ AffineSpace PUnit (Spec ↧ℚ) :=
    AffineSpace.homOfVector (𝟙 (Spec ↧ℚ))
      (fun _ : PUnit => (Scheme.ΓSpecIso ↧ℚ).inv a)
  let t : Spec ↧ℚ ⟶ AffineSpace PUnit (Spec ↧ℚ) :=
    AffineSpace.homOfVector (𝟙 (Spec ↧ℚ))
      (fun _ : PUnit => (Scheme.ΓSpecIso ↧ℚ).inv b)
  have hs : s ≫ (AffineSpace PUnit (Spec ↧ℚ) ↘ Spec ↧ℚ) = 𝟙 _ :=
    AffineSpace.homOfVector_over _ _
  have ht : t ≫ (AffineSpace PUnit (Spec ↧ℚ) ↘ Spec ↧ℚ) = 𝟙 _ :=
    AffineSpace.homOfVector_over _ _
  have hst : s = t := Scheme.Hom.ext_of_apply_closedPoint_eq_of_comp_eq_id
    (AffineSpace PUnit (Spec ↧ℚ) ↘ Spec ↧ℚ) hs ht H
  have hcoord := congrArg
    (fun e : Spec ↧ℚ ⟶ AffineSpace PUnit (Spec ↧ℚ) =>
      e.appTop (AffineSpace.coord (Spec ↧ℚ) PUnit.unit)) hst
  have hsections : (Scheme.ΓSpecIso ↧ℚ).inv a = (Scheme.ΓSpecIso ↧ℚ).inv b := by
    simpa only [s, t, AffineSpace.homOfVector_appTop_coord] using hcoord
  exact (Scheme.ΓSpecIso ↧ℚ).inv.hom.injective hsections

/-- Closed-point sections determine the coordinate pullback of affine-line endomorphisms. -/
example {K : Type u} [Field K] [IsAlgClosed K]
    {f g : AffineSpace PUnit (Spec ↧K) ⟶ AffineSpace PUnit (Spec ↧K)}
    [f.IsOver (Spec ↧K)] [g.IsOver (Spec ↧K)]
    (H : ∀ (x : AffineSpace PUnit (Spec ↧K)) (hx : IsClosed {x}),
      f (pointOfClosedPoint (AffineSpace PUnit (Spec ↧K) ↘ Spec ↧K) x hx
        (IsLocalRing.closedPoint K)) =
      g (pointOfClosedPoint (AffineSpace PUnit (Spec ↧K) ↘ Spec ↧K) x hx
        (IsLocalRing.closedPoint K))) :
    f.appTop (AffineSpace.coord (Spec ↧K) PUnit.unit) =
      g.appTop (AffineSpace.coord (Spec ↧K) PUnit.unit) := by
  have hf : f ≫ (AffineSpace PUnit (Spec ↧K) ↘ Spec ↧K) =
      (AffineSpace PUnit (Spec ↧K) ↘ Spec ↧K) := comp_over f _
  have hg : g ≫ (AffineSpace PUnit (Spec ↧K) ↘ Spec ↧K) =
      (AffineSpace PUnit (Spec ↧K) ↘ Spec ↧K) := comp_over g _
  have : LocallyOfFiniteType (f ≫ (AffineSpace PUnit (Spec ↧K) ↘ Spec ↧K)) := by
    rw [hf]
    infer_instance
  have hfg : f = g := Scheme.Hom.ext_of_apply_eq_on_dense_closedPoints
    (AffineSpace PUnit (Spec ↧K) ↘ Spec ↧K) Set.univ
    isOpen_univ.isLocallyClosed dense_univ
    (by
      intro x _ hx
      have hp :
          pointOfClosedPoint (AffineSpace PUnit (Spec ↧K) ↘ Spec ↧K) x hx
            (IsLocalRing.closedPoint K) = x :=
        AlgebraicGeometry.pointOfClosedPoint_apply
          (AffineSpace PUnit (Spec ↧K) ↘ Spec ↧K) x hx (IsLocalRing.closedPoint K)
      exact (congrArg f hp).symm.trans ((H x hx).trans (congrArg g hp)))
    (hf.trans hg.symm)
  exact congrArg (fun e : AffineSpace PUnit (Spec ↧K) ⟶ AffineSpace PUnit (Spec ↧K) =>
    e.appTop (AffineSpace.coord (Spec ↧K) PUnit.unit)) hfg
