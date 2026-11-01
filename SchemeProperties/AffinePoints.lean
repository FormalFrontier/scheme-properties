/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Limits.Presheaf
public import SchemeProperties.AffineFpqc
public import SchemeProperties.SingleCoverExtension
import SchemeProperties.AffineDensity
import SchemeProperties.AffineTestSheaf
import SchemeProperties.DenseOver

/-!
# Morphisms from dense affine-point subfunctors

For schemes over an arbitrary base, a natural transformation from a one-cover-dense
subfunctor of the full affine-point functor is induced by a unique scheme morphism.
The equation retains the original inclusion of the subfunctor and the original base
triangles. No sheaf condition on the source or its subfunctor is needed.

The proof composes Mathlib's fully faithful restricted Yoneda hom-map with
`CategoryTheory.Subfunctor.oneCoverExtensionEquiv`. Slice density and fpqc descent
supply full faithfulness and the target singleton sheaf condition, respectively.
The affine-point functor is Mathlib's `Presheaf.restrictedULiftYoneda`.

## References

J. S. Milne, *Algebraic Groups* (2017), Proposition 5.10, motivates the restriction
principle. Here the base and both schemes are arbitrary, and one-cover density is
used directly, without a finite-product condition on the subfunctor. The proof uses
Mathlib's restricted Yoneda API and this library's target-only single-cover extension
and affine-test descent APIs.
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A transformation on a one-cover-dense subfunctor of affine points comes from a
unique morphism over the original base. Only the target needs singleton descent,
which is supplied by fpqc descent rather than assumed by the caller.

This generalizes the restriction principle of Milne, *Algebraic Groups* (2017),
Proposition 5.10: the base and both schemes are arbitrary, and no finite-product
condition on the subfunctor is assumed. -/
theorem existsUnique_hom_of_isOneCoverDense
    {B : Scheme.{u}} {X Y : Over B}
    (D : Subfunctor
      ((Presheaf.restrictedULiftYoneda.{w}
        (CostructuredArrow.toOver Scheme.Spec B)).obj X))
    (hD : D.IsOneCoverDense (affineFpqcMorphisms B))
    (α : D.toFunctor ⟶
      (Presheaf.restrictedULiftYoneda.{w}
        (CostructuredArrow.toOver Scheme.Spec B)).obj Y) :
    ∃! f : X ⟶ Y,
      D.ι ≫
        (Presheaf.restrictedULiftYoneda.{w}
          (CostructuredArrow.toOver Scheme.Spec B)).map f = α := by
  have hY : ∀ {T U : CostructuredArrow Scheme.Spec B} (f : U ⟶ T),
      affineFpqcMorphisms B f →
        Presieve.IsSheafFor
          ((Presheaf.restrictedULiftYoneda.{w}
            (CostructuredArrow.toOver Scheme.Spec B)).obj Y)
          (Presieve.singleton f) := by
    intro T U f hf
    let : Flat (Scheme.Spec.map f.left) := affineFpqcMorphisms_flat B hf
    let : Surjective (Scheme.Spec.map f.left) := affineFpqcMorphisms_surjective B hf
    exact isSheafFor_singleton_restrictedULiftYoneda_toOver Y f
  have h := (Subfunctor.oneCoverExtensionEquiv hD hY).bijective.comp
    ((Functor.FullyFaithful.ofFullyFaithful
      (Presheaf.restrictedULiftYoneda.{w}
        (CostructuredArrow.toOver Scheme.Spec B))).map_bijective X Y)
  simp only [Function.comp_def, Subfunctor.oneCoverExtensionEquiv_apply] at h
  obtain ⟨f, hf⟩ := h.2 α
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact h.1 (hg.trans hf.symm)

end AlgebraicGeometry.Scheme
