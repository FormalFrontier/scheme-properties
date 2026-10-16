/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
The Mathlib notice above applies to the adapted total-space integrality and composition proofs.
Modifications by Formal Frontier Agents: remove the locally Noetherian hypothesis using the
finite-component reducedness theorem, and deduce composition and product statements.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Integrality of total spaces and products

A flat, universally open, geometrically integral morphism with integral target has integral
source. No locally Noetherian assumption on the target is necessary: an integral scheme has
only one irreducible component, so Mathlib's finite-component reducedness theorem applies.

The pullback application generalizes the integrality instance in
`Mathlib.AlgebraicGeometry.Geometrically.Integral`, recovering its conclusion under its original
hypotheses. Composition then gives geometric integrality of products in `Over S` when one
factor is flat and universally open over `S`. Over a field these two conditions are automatic;
neither factor needs to be locally Noetherian, locally of finite type, or quasi-compact.
These results are named lemmas, not instances overlapping Mathlib's integrality instances.

All schemes use the common universe required by Mathlib's category of schemes and geometric
morphism-property API.

## References

* Mathlib, Andrew Yang, `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian` and
  `GeometricallyIrreducible.comp`, whose proofs are adapted here.
* Mathlib, `GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents` and
  `GeometricallyIrreducible.irreducibleSpace`, for reducedness and irreducibility of the total
  space.
-/

public section

set_option warningAsError true

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

universe u

variable {X Y Z S : Scheme.{u}}

/-- A flat, universally open, geometrically integral morphism with integral target has integral
source. This generalizes `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian` by removing
the locally Noetherian hypothesis on the target. -/
lemma GeometricallyIntegral.isIntegral_of_flat_of_universallyOpen (f : X ⟶ S)
    [GeometricallyIntegral f] [Flat f] [UniversallyOpen f] [IsIntegral S] : IsIntegral X := by
  have : Finite (irreducibleComponents S) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨GeometricallyIrreducible.irreducibleSpace f f.isOpenMap,
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents f⟩

/-- Base change of a flat, universally open, geometrically integral morphism to an integral
scheme has integral total space. In particular, this recovers Mathlib's pullback-integrality
instance without its locally Noetherian hypothesis on `Y`. -/
lemma GeometricallyIntegral.isIntegral_pullback_of_flat_of_universallyOpen
    (f : X ⟶ S) (g : Y ⟶ S) [GeometricallyIntegral f] [Flat f] [UniversallyOpen f]
    [IsIntegral Y] : IsIntegral (pullback f g) :=
  GeometricallyIntegral.isIntegral_of_flat_of_universallyOpen (pullback.snd f g)

/-- A composite of geometrically integral morphisms is geometrically integral if the first
morphism is flat and universally open. No flatness or openness condition on the second
morphism, and no locally Noetherian hypothesis on any of the schemes, is required. -/
lemma GeometricallyIntegral.comp_of_flat_of_universallyOpen
    (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyIntegral f] [Flat f] [UniversallyOpen f]
    [GeometricallyIntegral g] : GeometricallyIntegral (f ≫ g) := by
  constructor
  intro K _ x P fst snd h
  have : IsIntegral (pullback g x) :=
    pullback_of_geometrically (f := g) GeometricallyIntegral.geometrically_isIntegral K x
  have : IsIntegral (pullback f (pullback.fst g x)) :=
    GeometricallyIntegral.isIntegral_pullback_of_flat_of_universallyOpen f (pullback.fst g x)
  have : IsIntegral (pullback (f ≫ g) x) :=
    IsIntegral.of_isIso (pullbackRightPullbackFstIso g x f).hom
  exact IsIntegral.of_isIso h.isoPullback.inv

/-- The product over `S` of two geometrically integral schemes is geometrically integral if
its second factor is flat and universally open over `S`. In particular this applies to any
two geometrically integral schemes over a field, since the flatness and openness assumptions
are then automatic. -/
lemma GeometricallyIntegral.tensorObj_of_flat_of_universallyOpen
    (X Y : Over S) [GeometricallyIntegral X.hom] [GeometricallyIntegral Y.hom]
    [Flat Y.hom] [UniversallyOpen Y.hom] : GeometricallyIntegral (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom]
  exact GeometricallyIntegral.comp_of_flat_of_universallyOpen
    (pullback.fst X.hom Y.hom) X.hom

end AlgebraicGeometry
