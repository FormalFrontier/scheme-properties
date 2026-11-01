/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.EffectiveEpi
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Sites.IsSheafFor

/-!
# Descent of sections on affine tests

Morphisms to an arbitrary scheme over a base satisfy the singleton sheaf condition
for flat surjective maps between affine tests over that base. The self-pullback is
taken over the common affine test, so no affineness condition on the base is needed.
The proof combines Mathlib's scheme effective-epimorphism theorem with its singleton
presieve criterion and the cofork universal property.

## References

* The Stacks Project, [Tag 023Q](https://stacks.math.columbia.edu/tag/023Q),
  for descent of scheme morphisms.
* Mathlib, `Mathlib.AlgebraicGeometry.EffectiveEpi`, for the affine descent formalization.
* Mathlib, `CategoryTheory.Presieve.isSheafFor_singleton` and
  `CategoryTheory.Limits.Cofork.IsColimit.existsUnique`, for the singleton and cofork APIs.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The restriction of a represented presheaf on `Over B` to affine tests is a
sheaf for every flat surjective singleton cover.

This is the affine-test, over-base consequence of descent in the Stacks Project,
[Tag 023Q](https://stacks.math.columbia.edu/tag/023Q), as formalized by Mathlib's
scheme effective-epimorphism theorem in `Mathlib.AlgebraicGeometry.EffectiveEpi`. -/
theorem isSheafFor_singleton_restrictedULiftYoneda_toOver
    {B : Scheme.{u}} (Y : Over B)
    {U V : CostructuredArrow Scheme.Spec B} (f : U ⟶ V)
    [Flat (Scheme.Spec.map f.left)] [Surjective (Scheme.Spec.map f.left)] :
    Presieve.IsSheafFor
      ((Presheaf.restrictedULiftYoneda.{w}
        (CostructuredArrow.toOver Scheme.Spec B)).obj Y)
      (Presieve.singleton f) := by
  let : PreservesLimits Scheme.Spec.{u} := ΓSpec.adjunction.rightAdjoint_preservesLimits
  let F : CostructuredArrow Scheme.Spec B ⥤ Scheme :=
    CostructuredArrow.proj Scheme.Spec B ⋙ Scheme.Spec
  have hpb := F.map_isPullback (IsPullback.of_hasPullback f f)
  have : EffectiveEpi (Scheme.Spec.map f.left) :=
    (isRegularEpi_iff_effectiveEpi _).mp
      (isRegularEpi_of_flat_of_surjective_of_isAffine _)
  rw [Presieve.isSheafFor_singleton]
  intro x hx
  have he : Scheme.Spec.map (pullback.fst f f).left ≫ x.down.left =
      Scheme.Spec.map (pullback.snd f f).left ≫ x.down.left := by
    exact congrArg (fun z => z.down.left)
      (hx (pullback.fst f f) (pullback.snd f f) pullback.condition)
  obtain ⟨d, hd, huniq⟩ := Cofork.IsColimit.existsUnique
    ((EffectiveEpi.getStruct (Scheme.Spec.map f.left)).isColimitCoforkOfIsPullback hpb)
    x.down.left he
  have hd' : Scheme.Spec.map f.left ≫ d = x.down.left := hd
  have hb : d ≫ Y.hom = V.hom := by
    apply (cancel_epi (Scheme.Spec.map f.left)).mp
    rw [← Category.assoc, hd']
    exact x.down.w.trans f.w.symm
  refine ⟨ULift.up (Over.homMk d hb), ?_, ?_⟩
  · apply ULift.ext
    apply Over.OverMorphism.ext
    exact hd'
  · intro y hy
    apply ULift.ext
    apply Over.OverMorphism.ext
    exact huniq y.down.left (congrArg (fun z => z.down.left) hy)

end AlgebraicGeometry.Scheme
