/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Faithfully flat descent of morphisms from spectra

A scheme morphism from `Spec A` descends uniquely along a faithfully flat algebra map
`R → A` precisely when its two pullbacks to `Spec (A ⊗[R] A)` agree.
The target is an arbitrary scheme. The proof uses Mathlib's effective epimorphism
property of fpqc covers and its canonical tensor-product description of the pullback.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct Algebra.TensorProduct
  CommRingCat RingHomClass

namespace AlgebraicGeometry.Scheme

/-- A morphism from `Spec A` to any scheme descends uniquely along a faithfully flat
algebra map `R → A` if its two canonical tensor-product pullbacks agree. -/
theorem existsUnique_spec_desc_of_faithfullyFlat
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hff : (algebraMap R A).FaithfullyFlat) (X : Scheme.{u})
    (e : Spec (.of A) ⟶ X)
    (he : Spec.map (ofHom (includeLeftRingHom : A →+* A ⊗[R] A)) ≫ e =
      Spec.map (ofHom (toRingHom (includeRight : A →ₐ[R] A ⊗[R] A))) ≫ e) :
    ∃! d : Spec (.of R) ⟶ X, Spec.map (ofHom (algebraMap R A)) ≫ d = e := by
  let q := Spec.map (ofHom (algebraMap R A))
  have hfs : Flat q ∧ Surjective q :=
    (flat_and_surjective_SpecMap_iff (ofHom (algebraMap R A))).2 hff
  have : Flat q := hfs.1
  have : Surjective q := hfs.2
  have hp : pullback.fst q q ≫ e = pullback.snd q q ≫ e := by
    apply (cancel_epi (pullbackSpecIso R A A).inv).1
    simpa only [q, ← Category.assoc, pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd] using he
  exact Cofork.IsColimit.existsUnique
    ((EffectiveEpi.getStruct q).isColimitCoforkOfIsPullback
      (IsPullback.of_hasPullback q q)) e hp

/-- The unique faithfully flat descent of a morphism respects any given base triangle.
Neither the base nor the target scheme is required to be affine. -/
theorem existsUnique_spec_desc_over_of_faithfullyFlat
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hff : (algebraMap R A).FaithfullyFlat) (B X : Scheme.{u})
    (a : Spec (.of R) ⟶ B) (p : X ⟶ B) (e : Spec (.of A) ⟶ X)
    (he : Spec.map (ofHom (includeLeftRingHom : A →+* A ⊗[R] A)) ≫ e =
      Spec.map (ofHom (toRingHom (includeRight : A →ₐ[R] A ⊗[R] A))) ≫ e)
    (hbase : e ≫ p = Spec.map (ofHom (algebraMap R A)) ≫ a) :
    ∃! d : Spec (.of R) ⟶ X,
      Spec.map (ofHom (algebraMap R A)) ≫ d = e ∧ d ≫ p = a := by
  obtain ⟨d, hd, huniq⟩ := existsUnique_spec_desc_of_faithfullyFlat hff X e he
  have hfs := (flat_and_surjective_SpecMap_iff (ofHom (algebraMap R A))).2 hff
  have : Flat (Spec.map (ofHom (algebraMap R A))) := hfs.1
  have : Surjective (Spec.map (ofHom (algebraMap R A))) := hfs.2
  have hdp : d ≫ p = a := by
    apply (cancel_epi (Spec.map (ofHom (algebraMap R A)))).1
    rw [← Category.assoc, hd, hbase]
  exact ⟨d, ⟨hd, hdp⟩, fun d' hd' ↦ huniq d' hd'.1⟩

end AlgebraicGeometry.Scheme
