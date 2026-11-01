/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import SchemeProperties.AffineFpqc
public import SchemeProperties.FiniteTypeSingleCover

@[expose] public section

/-!
# Algebra spectra and affine faithfully-flat tests

The functor `algSpecComma R` lifts the algebra spectrum functor to the category
of affine tests over `Spec R`. It retains the given underlying ring, scalar map,
and underlying ring homomorphism. Its structural maps and induced scheme
morphisms agree with Mathlib's existing Over-valued functor `algSpec R`.

An algebra morphism gives an affine fpqc test arrow exactly when its underlying
ring homomorphism is faithfully flat. Restriction along the existing finitely
generated algebra inclusion recovers `faithfullyFlatTestMorphisms`.

## Implementation notes

The base ring, algebra carriers, and schemes share a common universe. No field,
finite-generation, or nontriviality hypothesis is imposed on the all-algebra
comparison.

## References

This construction uses Mathlib's commutative-algebra/under-category equivalence,
opposite-slice equivalence, and algebra spectrum functor. The faithful-flatness
comparison uses Mathlib's characterization by flatness and surjectivity of the
spectrum map through the affine fpqc test criterion.
-/

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- The spectrum functor on `R`-algebras, retaining the opposite underlying ring
and its structural map to `Spec R`. -/
@[implicit_reducible] noncomputable def algSpecComma
    (R : CommRingCat.{u}) :
    (CommAlgCat.{u} R)ᵒᵖ ⥤
      CostructuredArrow
        (Scheme.Spec : CommRingCat.{u}ᵒᵖ ⥤ Scheme.{u})
        (Scheme.Spec.obj (op R)) :=
  (commAlgCatEquivUnder R).functor.op ⋙
    (Over.opEquivOpUnder R).inverse ⋙
    CostructuredArrow.post (𝟭 (CommRingCat.{u}ᵒᵖ)) Scheme.Spec (op R)

section

variable {R : CommRingCat.{u}}

/-- The raw ring component is the given underlying ring of the algebra. -/
@[simp] theorem algSpecComma_obj_left (X : (CommAlgCat.{u} R)ᵒᵖ) :
    ((algSpecComma R).obj X).left = op (CommRingCat.of X.unop) := rfl

/-- The structural map is the spectrum of the given scalar map. -/
@[simp] theorem algSpecComma_obj_hom (X : (CommAlgCat.{u} R)ᵒᵖ) :
    ((algSpecComma R).obj X).hom = Spec.algebraMap R X.unop := rfl

/-- The raw morphism component is the opposite of the given underlying ring map. -/
@[simp] theorem algSpecComma_map_left
    {X Y : (CommAlgCat.{u} R)ᵒᵖ} (f : X ⟶ Y) :
    ((algSpecComma R).map f).left =
      (CommRingCat.ofHom f.unop.hom.toRingHom).op := rfl

/-- The induced ring homomorphism is the underlying homomorphism of the given
algebra morphism. -/
theorem algSpecComma_map_left_unop_hom
    {X Y : (CommAlgCat.{u} R)ᵒᵖ} (f : X ⟶ Y) :
    (((algSpecComma R).map f).left.unop).hom = f.unop.hom.toRingHom := rfl

/-- The comma lift has the same structural map as the existing algebra spectrum
functor over `Spec R`. -/
theorem algSpecComma_obj_hom_eq_algSpec_obj_hom
    (X : (CommAlgCat.{u} R)ᵒᵖ) :
    ((algSpecComma R).obj X).hom = ((algSpec R).obj X).hom := by
  simp [Spec.algebraMap]

/-- Applying spectrum to the raw component of the comma lift gives the morphism
of the existing algebra spectrum functor over `Spec R`. -/
theorem algSpecComma_map_left_spec_eq_algSpec_map_left
    {X Y : (CommAlgCat.{u} R)ᵒᵖ} (f : X ⟶ Y) :
    Scheme.Spec.map ((algSpecComma R).map f).left =
      ((algSpec R).map f).left := by
  simp [AlgHom.toUnder]
  rfl

/-- An algebra morphism gives an affine fpqc test arrow exactly when its given
underlying ring homomorphism is faithfully flat. -/
theorem affineFpqcMorphisms_algSpecComma_map_iff
    {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    Scheme.affineFpqcMorphisms (Spec R) ((algSpecComma R).map f.op) ↔
      f.hom.toRingHom.FaithfullyFlat := by
  rw [Scheme.affineFpqcMorphisms_iff_faithfullyFlat, algSpecComma_map_left_unop_hom]
  rfl

end

/-- Restricting the affine fpqc test arrows along the existing finitely generated
algebra inclusion recovers the existing faithfully-flat test morphisms. -/
theorem affineFpqcMorphisms_algSpecComma_fg_eq
    (K : Type u) [CommRing K] :
    (fun _ _ f ↦
      Scheme.affineFpqcMorphisms (Spec (.of K))
        (((ObjectProperty.ι _).op ⋙ algSpecComma (.of K)).map f) :
      MorphismProperty ((FGAlgCat.{u} K)ᵒᵖ)) =
        faithfullyFlatTestMorphisms K := by
  funext X Y f
  apply propext
  exact affineFpqcMorphisms_algSpecComma_map_iff
    (R := CommRingCat.of K) (A := Y.unop.obj) (B := X.unop.obj) f.unop.hom

end AlgebraicGeometry
