/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.AffineTestObjects
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# An affine line in an affine plane

The closed immersion of the rational affine line into the affine plane is
induced by evaluating the outer polynomial variable at zero. Its monomorphism
property is obtained independently from Mathlib's surjective-ring-map
criterion for closed immersions. The separating-family and ring-point APIs
apply to this morphism. The source has distinct rational points given by
evaluation at zero and one, and their images remain distinct.

## References

Mathlib supplies `Polynomial.eval_surjective`,
`IsClosedImmersion.spec_of_surjective`, the monomorphism instance for
preimmersions, `Spec.map_injective` and the polynomial evaluation identities.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private abbrev affineLine : Scheme := Spec (.of (Polynomial ℚ))

private abbrev affinePlane : Scheme := Spec (.of (Polynomial (Polynomial ℚ)))

private def lineInPlane : affineLine ⟶ affinePlane :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Polynomial ℚ)))

private theorem lineInPlane_closedImmersion : IsClosedImmersion lineInPlane :=
  IsClosedImmersion.spec_of_surjective _ (Polynomial.eval_surjective (0 : Polynomial ℚ))

private theorem lineInPlane_mono : Mono lineInPlane := by
  letI := lineInPlane_closedImmersion
  infer_instance

private def rationalPoint (a : ℚ) : Spec (.of ℚ) ⟶ affineLine :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))

private theorem rationalPoint_zero_ne_one : rationalPoint 0 ≠ rationalPoint 1 := by
  intro h
  have he : CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℚ)) =
      CommRingCat.ofHom (Polynomial.evalRingHom (1 : ℚ)) := Spec.map_injective h
  have hx := congrArg
    (fun k : CommRingCat.of (Polynomial ℚ) ⟶ CommRingCat.of ℚ ↦ k.hom Polynomial.X) he
  change Polynomial.eval (0 : ℚ) Polynomial.X = Polynomial.eval (1 : ℚ) Polynomial.X at hx
  have h01 : (0 : ℚ) = 1 := by simpa only [Polynomial.eval_X] using hx
  exact zero_ne_one h01

private theorem lineInPlane_affine_cancellation :
    ∀ (T : Scheme.{0}) (_ : IsAffine T) (g h : T ⟶ affineLine),
      g ≫ lineInPlane = h ≫ lineInPlane → g = h :=
  (isSeparating_isAffine.mono_iff lineInPlane).mp lineInPlane_mono

private theorem lineInPlane_injective_ring_points :
    ∀ (R : Type) [CommRing R],
      Function.Injective (fun g : Spec (.of R) ⟶ affineLine ↦ g ≫ lineInPlane) :=
  (mono_iff_injective_spec lineInPlane).mp lineInPlane_mono

private theorem rationalPoint_images_ne :
    rationalPoint 0 ≫ lineInPlane ≠ rationalPoint 1 ≫ lineInPlane := by
  intro h
  exact rationalPoint_zero_ne_one (lineInPlane_injective_ring_points ℚ h)

end AlgebraicGeometry.Scheme
