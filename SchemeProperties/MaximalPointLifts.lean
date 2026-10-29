/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ClosedPointLifts
public import SchemeProperties.MaximalPointMorphisms

/-!
# Lifting morphisms to maximal-point spaces

For a commutative Jacobson ring `R`, morphisms from any locally ringed space `X`
to the existing `Spec.maximalPointSpace R` correspond to morphisms `X → Spec R`
whose image points all correspond to maximal ideals. The forward map is
composition with the given `Spec.maximalPointInclusion R`. The inverse is the
generic closed-point lift, with its image predicate expressed in terms of ideals.
No Jacobson hypothesis on `X` or its global sections is needed.

The comparisons below retain the full section rings and stalks, including
nilpotents, and read back the original coordinate homomorphism. Source
naturality holds for every locally ringed space morphism. Target naturality uses
the existing `Spec.maximalPointMap` and precisely its maximal-ideal contraction
hypothesis. Supplied structure-map triangles are preserved without replacing
any of their maps.

## References

The construction specializes
`LocallyRingedSpace.closedPointInclusionHomEquiv` from
`SchemeProperties.ClosedPointLifts`, using Mathlib's
`PrimeSpectrum.isClosed_singleton_iff_isMaximal`. The section, stalk and coordinate
comparisons are those of `SchemeProperties.MaximalPointSpace`; target naturality
uses `SchemeProperties.MaximalPointMorphisms`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory TopCat TopologicalSpace Opposite
open AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry.Spec

/-- The target-inclusion universal property of the maximal-point space, for an
arbitrary locally ringed source. This is the closed-point-target equivalence with
the image predicate expressed as maximality of the corresponding ideals. -/
def maximalPointInclusionHomEquiv (X : LocallyRingedSpace.{u}) (R : Type u)
    [CommRing R] [IsJacobsonRing R] :
    (X ⟶ maximalPointSpace R) ≃
      {f : X ⟶ locallyRingedSpaceObj (CommRingCat.of R) //
        ∀ x : X, (f.base x).asIdeal.IsMaximal} :=
  (closedPointInclusionHomEquiv X (locallyRingedSpaceObj (CommRingCat.of R))).trans
    { toFun := fun f => ⟨f.val, fun x =>
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal (f.val.base x)).mp (f.property x)⟩
      invFun := fun f => ⟨f.val, fun x =>
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal (f.val.base x)).mpr (f.property x)⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

variable {T X B : LocallyRingedSpace.{u}}
variable {R : Type u} [CommRing R] [IsJacobsonRing R]

/-- The forward equivalence is composition with the given maximal-point inclusion. -/
@[simp]
lemma maximalPointInclusionHomEquiv_apply_val (g : X ⟶ maximalPointSpace R) :
    (maximalPointInclusionHomEquiv X R g).val = g ≫ maximalPointInclusion R := rfl

variable (f : {f : X ⟶ locallyRingedSpaceObj (CommRingCat.of R) //
  ∀ x : X, (f.base x).asIdeal.IsMaximal})

/-- The inverse is the generic closed-point lift with the closed/maximal
point-predicate identification. -/
lemma maximalPointInclusionHomEquiv_symm_apply :
    (maximalPointInclusionHomEquiv X R).symm f =
      closedPointLift f.val (fun x =>
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal (f.val.base x)).mpr (f.property x)) :=
  rfl

/-- The inverse does not depend on the proof of maximality of the image ideals. -/
lemma maximalPointInclusionHomEquiv_symm_proof_irrel
    (g : X ⟶ locallyRingedSpaceObj (CommRingCat.of R))
    (hg hg' : ∀ x : X, (g.base x).asIdeal.IsMaximal) :
    (maximalPointInclusionHomEquiv X R).symm ⟨g, hg⟩ =
      (maximalPointInclusionHomEquiv X R).symm ⟨g, hg'⟩ := rfl

/-- Composing the inverse with the given inclusion recovers the full original arrow. -/
@[simp, reassoc]
lemma maximalPointInclusionHomEquiv_symm_comp_inclusion :
    (maximalPointInclusionHomEquiv X R).symm f ≫ maximalPointInclusion R = f.val :=
  closedPointLift_comp_fromClosedPoints f.val _

/-- Every full factorization through the inclusion is the inverse image of the
original arrow under the equivalence. -/
lemma maximalPointInclusionHomEquiv_symm_unique (g : X ⟶ maximalPointSpace R)
    (hg : g ≫ maximalPointInclusion R = f.val) :
    g = (maximalPointInclusionHomEquiv X R).symm f :=
  closedPointLift_unique f.val _ g hg

/-- The point map is the original point map with its closed-point proof. -/
@[simp]
lemma maximalPointInclusionHomEquiv_symm_base_apply (x : X) :
    ((maximalPointInclusionHomEquiv X R).symm f).base x =
      ⟨f.val.base x,
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal (f.val.base x)).mpr (f.property x)⟩ :=
  rfl

/-- On ambient opens the inverse has the original inverse-image map. -/
@[simp]
lemma maximalPointInclusionHomEquiv_symm_preimage (U : Opens (PrimeSpectrum R)) :
    (Opens.map ((maximalPointInclusionHomEquiv X R).symm f).base).obj
        ((Opens.closedPointsOrderIso (PrimeSpectrum R)) U) =
      (Opens.map f.val.base).obj U :=
  closedPointLift_preimage f.val _ U

/-- An arbitrary maximal-point open is read back through its canonical ambient
extension. This equality supplies the transport for the section comparison. -/
lemma maximalPointInclusionHomEquiv_symm_preimage_extendOpen
    (W : Opens (maximalPointSpace R)) :
    (Opens.map ((maximalPointInclusionHomEquiv X R).symm f).base).obj W =
      (Opens.map f.val.base).obj ((Opens.closedPointsOrderIso (PrimeSpectrum R)).symm W) :=
  closedPointLift_preimage_extendOpen f.val _ W

/-- On every ambient open, the given full section comparison followed by the
inverse's component is the original section homomorphism. -/
@[reassoc]
lemma maximalPointInclusionHomEquiv_symm_c_app (U : Opens (PrimeSpectrum R)) :
    CommRingCat.ofHom (maximalPointSectionsIso R U).toRingHom ≫
        ((maximalPointInclusionHomEquiv X R).symm f).c.app
          (op ((Opens.closedPointsOrderIso (PrimeSpectrum R)) U)) =
      f.val.c.app (op U) :=
  closedPointLift_c_app f.val _ U

-- Unfold the given section-ring aliases when elaborating the inverse comparison.
set_option backward.isDefEq.respectTransparency false in
/-- On every maximal-point open, the full section component is the original
component through the given section comparison and the canonical open transports. -/
lemma maximalPointInclusionHomEquiv_symm_c_app_eq (W : Opens (maximalPointSpace R)) :
    ((maximalPointInclusionHomEquiv X R).symm f).c.app (op W) =
      (maximalPointSpace R).presheaf.map
          (eqToHom (congrArg op
            ((Opens.closedPointsOrderIso (PrimeSpectrum R)).apply_symm_apply W).symm)) ≫
        CommRingCat.ofHom
          (maximalPointSectionsIso R
            ((Opens.closedPointsOrderIso (PrimeSpectrum R)).symm W)).symm.toRingHom ≫
          f.val.c.app (op ((Opens.closedPointsOrderIso (PrimeSpectrum R)).symm W)) ≫
            X.presheaf.map (eqToHom (congrArg op
              (maximalPointInclusionHomEquiv_symm_preimage_extendOpen f W).symm)) :=
  closedPointLift_c_app_eq f.val _ W

-- Elaborate the given full-stalk comparison and its canonical base equality transport.
set_option backward.isDefEq.respectTransparency false in
/-- The given comparison of full stalks followed by the inverse's local map is
the original stalk map, with the canonical equality transport on its domain. -/
@[reassoc]
lemma maximalPointInclusionHomEquiv_symm_stalkMap (x : X) :
    CommRingCat.ofHom
        (maximalPointStalkComparison R
          (((maximalPointInclusionHomEquiv X R).symm f).base x)).toRingHom ≫
        ((maximalPointInclusionHomEquiv X R).symm f).stalkMap x =
      eqToHom (congrArg (fun y : PrimeSpectrum R => (structureSheaf R).presheaf.stalk y)
        (congrArg Subtype.val (maximalPointInclusionHomEquiv_symm_base_apply f x))) ≫
        f.val.stalkMap x := by
  have h := LocallyRingedSpace.stalkMap_congr_hom
    ((maximalPointInclusionHomEquiv X R).symm f ≫ maximalPointInclusion R) f.val
    (maximalPointInclusionHomEquiv_symm_comp_inclusion f) x
  ext s
  change ((maximalPointInclusionHomEquiv X R).symm f).stalkMap x
      (maximalPointStalkComparison R
        (((maximalPointInclusionHomEquiv X R).symm f).base x) s) = f.val.stalkMap x s
  rw [maximalPointStalkComparison_apply]
  simpa only [stalkMap_comp, comp_base, TopCat.comp_app,
    maximalPointInclusion_base_apply, maximalPointInclusionHomEquiv_symm_base_apply,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, CommRingCat.comp_apply] using
    congrArg (fun k => k s) h

-- Unfold the actual pushforward-top and global-section aliases while rewriting.
set_option backward.isDefEq.respectTransparency false in
/-- The original coordinate homomorphism `R → Γ(X)` is read back through the
existing maximal-point coordinates. This follows from the full factorization. -/
@[reassoc]
lemma maximalPointInclusionHomEquiv_symm_coordinates :
    CommRingCat.ofHom (maximalPointCoordinates R).toRingHom ≫
        LocallyRingedSpace.Γ.map ((maximalPointInclusionHomEquiv X R).symm f).op =
      toSpecΓ (CommRingCat.of R) ≫ LocallyRingedSpace.Γ.map f.val.op := by
  rw [maximalPointCoordinates_hom, ← LocallyRingedSpace.Γ_map_op,
    Category.assoc, ← Functor.map_comp, ← op_comp,
    maximalPointInclusionHomEquiv_symm_comp_inclusion]

/-- A supplied structure-map triangle is inherited as an equality of full
locally ringed space arrows, without changing the supplied maps. -/
lemma maximalPointInclusionHomEquiv_symm_comp_structure
    (σR : locallyRingedSpaceObj (CommRingCat.of R) ⟶ B) (σX : X ⟶ B)
    (h : f.val ≫ σR = σX) :
    (maximalPointInclusionHomEquiv X R).symm f ≫ maximalPointInclusion R ≫ σR = σX :=
  closedPointLift_comp_structure f.val _ σR σX h

/-- The inverse is natural under every source morphism, with no source Jacobson
or scheme hypothesis. -/
@[simp]
lemma maximalPointInclusionHomEquiv_symm_precomp (g : T ⟶ X) :
    (maximalPointInclusionHomEquiv T R).symm
        ⟨g ≫ f.val, fun t => f.property (g.base t)⟩ =
      g ≫ (maximalPointInclusionHomEquiv X R).symm f :=
  closedPointLift_precomp f.val _ g

/-- The forward equivalence is natural under every source morphism. -/
lemma maximalPointInclusionHomEquiv_precomp (g : T ⟶ X) (k : X ⟶ maximalPointSpace R) :
    maximalPointInclusionHomEquiv T R (g ≫ k) =
      ⟨g ≫ (maximalPointInclusionHomEquiv X R k).val,
        fun t => (maximalPointInclusionHomEquiv X R k).property (g.base t)⟩ :=
  Subtype.ext (Category.assoc g k (maximalPointInclusion R))

/-- A full arrow admits a unique maximal-point lift exactly when every image
point corresponds to a maximal ideal. -/
lemma existsUnique_maximalPointLift_iff
    (f : X ⟶ locallyRingedSpaceObj (CommRingCat.of R)) :
    (∃! g : X ⟶ maximalPointSpace R, g ≫ maximalPointInclusion R = f) ↔
      ∀ x : X, (f.base x).asIdeal.IsMaximal :=
  (existsUnique_closedPointLift_iff f).trans
    ⟨fun hf x => (PrimeSpectrum.isClosed_singleton_iff_isMaximal (f.base x)).mp (hf x),
      fun hf x => (PrimeSpectrum.isClosed_singleton_iff_isMaximal (f.base x)).mpr (hf x)⟩

section TargetNaturality

variable {S : Type u} [CommRing S] [IsJacobsonRing S]
variable (φ : R →+* S)
variable (hφ : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
  (n.asIdeal.comap φ).IsMaximal)
variable (fS : {f : X ⟶ locallyRingedSpaceObj (CommRingCat.of S) //
  ∀ x : X, (f.base x).asIdeal.IsMaximal})

-- Unfold maximalPointSpace to the existing closedPointSpace specialization.
set_option backward.isDefEq.respectTransparency false in
/-- Target naturality is with the given maximal-point map, under exactly its
hypothesis that maximal ideals remain maximal under contraction. -/
lemma maximalPointInclusionHomEquiv_symm_postcomp :
    (maximalPointInclusionHomEquiv X R).symm
        ⟨fS.val ≫ locallyRingedSpaceMap (CommRingCat.ofHom φ),
          fun x => hφ (fS.val.base x) (fS.property x)⟩ =
      (maximalPointInclusionHomEquiv X S).symm fS ≫ maximalPointMap φ hφ := by
  simpa only [maximalPointInclusionHomEquiv_symm_apply, maximalPointMap] using
    (closedPointLift_postcomp fS.val (fun x =>
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal (fS.val.base x)).mpr (fS.property x))
      (locallyRingedSpaceMap (CommRingCat.ofHom φ))
      (locallyRingedSpaceMap_mapsTo_closedPoints φ hφ))

/-- The forward equivalence respects the given maximal-point map and its full
commuting square with the affine spectra. -/
lemma maximalPointInclusionHomEquiv_postcomp (g : X ⟶ maximalPointSpace S) :
    maximalPointInclusionHomEquiv X R (g ≫ maximalPointMap φ hφ) =
      ⟨(maximalPointInclusionHomEquiv X S g).val ≫
          locallyRingedSpaceMap (CommRingCat.ofHom φ),
        fun x => hφ ((maximalPointInclusionHomEquiv X S g).val.base x)
          ((maximalPointInclusionHomEquiv X S g).property x)⟩ := by
  apply Subtype.ext
  change (g ≫ maximalPointMap φ hφ) ≫ maximalPointInclusion R =
    (g ≫ maximalPointInclusion S) ≫ locallyRingedSpaceMap (CommRingCat.ofHom φ)
  rw [Category.assoc, maximalPointMap_comp_inclusion, ← Category.assoc]

end TargetNaturality

end AlgebraicGeometry.Spec
