/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

@[expose] public section

/-!
# Faithfully flat morphisms between affine tests

For a scheme `B`, the category `CostructuredArrow Scheme.Spec B` consists of spectra
with their structural maps to `B`. These structural maps are unrestricted, and the
rings need not be finitely generated. The property `affineFpqcMorphisms B` selects
those test morphisms whose induced scheme morphisms are flat and surjective.

Every morphism between these affine endpoints is quasi-compact. Consequently a
morphism satisfying `affineFpqcMorphisms B` gives a singleton cover in the fpqc
precoverage on schemes.

The test category has pullbacks by the connected-limit construction for
costructured arrows. These are pullbacks over a common affine test target, not
products of unrelated tests over `B`. The projection preserves connected limits;
the additional preservation by `Scheme.Spec` follows from `ΓSpec.adjunction`.
Together these facts give base-change stability for the property. No assertion
about terminal objects or binary products over an arbitrary base is made here.

For an affine base `Spec R`, the existing `commAlgCatEquivUnder`, opposite-slice
equivalences and fully faithful spectrum functor give the all-`R`-algebra
interpretation. The structural maps `Spec.algebraMap` and the compatible-arrow
equivalence `Spec.homEquivAlgHom` use the supplied algebra structures.

## Implementation notes

This module packages the scheme properties Flat and Surjective through existing
comma-category and morphism-property interfaces. It concerns affine tests over
arbitrary schemes, with no finite-generation or field restriction; it does not
assert a descent or representability theorem for presheaves on these tests.
-/

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- The morphisms between affine tests over `B` whose induced scheme morphisms are
flat and surjective. Their quasi-compactness follows from their affine endpoints. -/
def affineFpqcMorphisms (B : Scheme.{u}) :
    MorphismProperty (CostructuredArrow Scheme.Spec B) :=
  (((@AlgebraicGeometry.Flat) ⊓ (@AlgebraicGeometry.Surjective)) :
      MorphismProperty Scheme.{u}).inverseImage
    ((CostructuredArrow.proj Scheme.Spec B) ⋙ Scheme.Spec)

/-- An affine-test morphism is an fpqc morphism exactly when its induced scheme
morphism is flat and surjective. -/
@[simp]
theorem affineFpqcMorphisms_iff (B : Scheme.{u})
    {X Y : CostructuredArrow Scheme.Spec B} (f : X ⟶ Y) :
    affineFpqcMorphisms B f ↔
      Flat (Scheme.Spec.map f.left) ∧ Surjective (Scheme.Spec.map f.left) :=
  Iff.rfl

/-- An affine-test morphism is fpqc exactly when its underlying ring homomorphism
is faithfully flat. -/
theorem affineFpqcMorphisms_iff_faithfullyFlat
    (B : Scheme.{u})
    {X Y : CostructuredArrow Scheme.Spec B} (f : X ⟶ Y) :
    affineFpqcMorphisms B f ↔ (f.left.unop).hom.FaithfullyFlat :=
  (affineFpqcMorphisms_iff B f).trans
    (AlgebraicGeometry.flat_and_surjective_SpecMap_iff f.left.unop)

/-- The scheme morphism induced by an fpqc morphism of affine tests is flat. -/
theorem affineFpqcMorphisms_flat (B : Scheme.{u})
    {X Y : CostructuredArrow Scheme.Spec B} {f : X ⟶ Y}
    (hf : affineFpqcMorphisms B f) : Flat (Scheme.Spec.map f.left) :=
  ((affineFpqcMorphisms_iff B f).mp hf).1

/-- The scheme morphism induced by an fpqc morphism of affine tests is surjective. -/
theorem affineFpqcMorphisms_surjective (B : Scheme.{u})
    {X Y : CostructuredArrow Scheme.Spec B} {f : X ⟶ Y}
    (hf : affineFpqcMorphisms B f) : Surjective (Scheme.Spec.map f.left) :=
  ((affineFpqcMorphisms_iff B f).mp hf).2

instance affineFpqcMorphisms_isMultiplicative (B : Scheme.{u}) :
    (affineFpqcMorphisms B).IsMultiplicative := by
  unfold affineFpqcMorphisms
  let h : (((@Flat.{u}) ⊓ (@Surjective.{u})) :
      MorphismProperty Scheme.{u}).IsMultiplicative :=
    MorphismProperty.IsMultiplicative.inf (P := @Flat.{u}) (Q := @Surjective.{u})
  exact
    { toContainsIdentities :=
        @MorphismProperty.ContainsIdentities.inverseImage _ _ _ _ _
          h.toContainsIdentities _
      toIsStableUnderComposition :=
        @MorphismProperty.IsStableUnderComposition.inverseImage _ _ _ _ _
          h.toIsStableUnderComposition _ }

instance affineFpqcMorphisms_respectsIso (B : Scheme.{u}) :
    (affineFpqcMorphisms B).RespectsIso := by
  unfold affineFpqcMorphisms
  let hFlatIso : MorphismProperty.RespectsIso (@Flat.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Flat.{u})
  exact @MorphismProperty.RespectsIso.inverseImage _ _ _ _ _
    (@MorphismProperty.RespectsIso.inf _ _ _ _ hFlatIso inferInstance) _

instance affineFpqcMorphisms_isStableUnderBaseChange (B : Scheme.{u}) :
    (affineFpqcMorphisms B).IsStableUnderBaseChange := by
  let : PreservesLimits Scheme.Spec.{u} :=
    (ΓSpec.adjunction.{u}).rightAdjoint_preservesLimits
  let F : CostructuredArrow Scheme.Spec B ⥤ Scheme :=
    (CostructuredArrow.proj Scheme.Spec B) ⋙ Scheme.Spec
  change ((((@Flat) ⊓ (@Surjective)) :
    MorphismProperty Scheme.{u}).inverseImage F).IsStableUnderBaseChange
  apply @MorphismProperty.IsStableUnderBaseChange.mk' _ _ _
    (affineFpqcMorphisms_respectsIso B)
  intro X Y S f g _ hg
  change Flat (F.map g) ∧ Surjective (F.map g) at hg
  change Flat (F.map (pullback.fst f g)) ∧ Surjective (F.map (pullback.fst f g))
  let : Flat (F.map g) := hg.1
  let : Surjective (F.map g) := hg.2
  rw [← PreservesPullback.iso_hom_fst F f g]
  let hFlatIso : MorphismProperty.RespectsIso (@Flat.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Flat.{u})
  constructor
  · exact @MorphismProperty.RespectsIso.precomp _ _ (@Flat.{u}) hFlatIso
      _ _ _ _ inferInstance _ inferInstance
  · exact @MorphismProperty.RespectsIso.precomp _ _ (@Surjective.{u}) inferInstance
      _ _ _ _ inferInstance _ inferInstance

/-- An fpqc morphism of affine tests gives a singleton cover in the fpqc
precoverage on schemes; quasi-compactness is supplied by the affine endpoints. -/
theorem affineFpqcMorphisms_singleton_mem_fpqcPrecoverage (B : Scheme.{u})
    {X Y : CostructuredArrow Scheme.Spec B} (f : X ⟶ Y)
    (hf : affineFpqcMorphisms B f) :
    Presieve.singleton (Scheme.Spec.map f.left) ∈
      Scheme.fpqcPrecoverage (Scheme.Spec.obj Y.left) := by
  let : IsAffineHom (Scheme.Spec.map f.left) := isAffineHom_of_isAffine _
  let : QuasiCompact (Scheme.Spec.map f.left) := inferInstance
  let : Flat (Scheme.Spec.map f.left) := affineFpqcMorphisms_flat B hf
  let : Surjective (Scheme.Spec.map f.left) := affineFpqcMorphisms_surjective B hf
  exact Scheme.Hom.singleton_mem_fpqcPrecoverage (Scheme.Spec.map f.left)

end AlgebraicGeometry.Scheme
