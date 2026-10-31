/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RingTheory.FlatSourceCancellation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flatness under flat surjective source precomposition

For arbitrary scheme morphisms `p : X ⟶ Y` and `f : Y ⟶ Z`, if `p` is flat and
surjective and `p ≫ f` is flat, then `f` is flat. No quasi-compactness assumption
is needed.

At each point of `Y`, choose a point of `X` above it. The stalk map of `p` is
flat and local, hence faithfully flat. Ring-tower cancellation then gives
flatness of the stalk map of `f`.

## References

* Mathlib's stalkwise flatness criterion `AlgebraicGeometry.Flat.of_stalkMap`
  and flatness of stalk maps `AlgebraicGeometry.Flat.stalkMap`.
* Mathlib's `Module.FaithfullyFlat.of_flat_of_isLocalHom` for local rings.
* `RingHom.Flat.of_comp_of_faithfullyFlat` for cancellation in a ring tower.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Flat

/-- Flatness of a composite descends through a flat surjective first morphism,
without a quasi-compactness assumption. -/
theorem of_comp
    {X Y Z : Scheme.{u}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Flat p] [Surjective p] [Flat (p ≫ f)] : Flat f := by
  apply Flat.of_stalkMap
  intro y
  obtain ⟨x, rfl⟩ := p.surjective y
  have hp : (p.stalkMap x).hom.FaithfullyFlat := by
    let : Algebra (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) :=
      (p.stalkMap x).hom.toAlgebra
    have : Module.Flat (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) :=
      Flat.stalkMap p x
    have : IsLocalHom
        (algebraMap (Y.presheaf.stalk (p x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (p.stalkMap x).hom)
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr
      Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply RingHom.Flat.of_comp_of_faithfullyFlat hp
  rw [← CommRingCat.hom_comp (f.stalkMap (p x)) (p.stalkMap x),
    ← Scheme.Hom.stalkMap_comp p f x]
  exact Flat.stalkMap (p ≫ f) x

end AlgebraicGeometry.Flat
