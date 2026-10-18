/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.CategoryTheory.Generator.Basic

/-!
# Affine schemes as test objects

Affine schemes form a separating family of objects in the category of schemes.
Consequently, a scheme morphism is a monomorphism exactly when postcomposition
is injective on points valued in every commutative ring in the scheme universe.

The separating-family argument uses an affine open cover of the source and
Mathlib's `Scheme.Cover.hom_ext`. The monomorphism criterion specializes
`ObjectProperty.IsSeparating.mono_iff`, using `Scheme.isoSpec` to pass from
arbitrary affine schemes to spectra. No finiteness or reducedness assumption
is imposed; zero rings and empty schemes are included.

Field-valued points alone are insufficient for this criterion. For a field `k`,
the map `Spec (k[ε]/(ε²)) ⟶ Spec k` is injective on field-valued points, but
is not a monomorphism: the identity and the endomorphism sending `ε` to zero
are distinct maps over `k`.

## References

* Mathlib's `AlgebraicGeometry.Cover.Open` and `AlgebraicGeometry.Gluing`:
  affine open covers and equality of morphisms on an open cover.
* Mathlib's `CategoryTheory.Generator.Basic`: separating object properties
  and their monomorphism criterion.
* Mathlib's `AlgebraicGeometry.AffineScheme`: the canonical spectrum
  isomorphism of an affine scheme.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Affine schemes form a separating family: two scheme morphisms are equal
if their precompositions with every morphism from an affine scheme agree.
The affine-open-cover argument uses Mathlib's `Scheme.Cover.hom_ext`. -/
theorem isSeparating_isAffine :
    ObjectProperty.IsSeparating (fun T : Scheme.{u} ↦ IsAffine T) := by
  intro X Y f g H
  refine X.affineOpenCover.openCover.hom_ext f g ?_
  intro i
  exact H _ inferInstance (X.affineOpenCover.f i)

/-- A scheme morphism is a monomorphism if and only if postcomposition is
injective on points valued in every commutative ring in the scheme universe.
This is the affine-scheme specialization of Mathlib's
`ObjectProperty.IsSeparating.mono_iff`. -/
theorem mono_iff_injective_spec {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mono f ↔ ∀ (R : Type u) [CommRing R],
      Function.Injective (fun g : Spec (.of R) ⟶ X ↦ g ≫ f) := by
  rw [isSeparating_isAffine.mono_iff f]
  constructor
  · intro H R _ g h e
    exact H _ inferInstance g h e
  · intro H T hT g h e
    letI := hT
    apply (cancel_epi T.isoSpec.inv).mp
    apply H Γ(T, ⊤)
    simpa only [Category.assoc] using congrArg (fun k ↦ T.isoSpec.inv ≫ k) e

end AlgebraicGeometry.Scheme
