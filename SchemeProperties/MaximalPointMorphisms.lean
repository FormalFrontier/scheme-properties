/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.MaximalPointSheaf
public import SchemeProperties.ClosedPointMorphisms
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Homomorphisms preserving maximal points

A ring homomorphism between Jacobson rings induces a morphism of their
maximal-point locally ringed spaces when it preserves maximal ideals under
contraction. This hypothesis is necessary for general Jacobson rings.
The square with the affine spectra is an equality of full locally ringed space
morphisms, not merely of their maps on points. The coordinate action determines
the maps on every open and the full localization maps on principal opens and
stalks; no reduction or nonemptiness assumption is used.

The contraction hypothesis cannot be dropped: the inclusions `ℤ → ℚ` and
`K[T] → K(T)` (for a field `K`) contract the maximal zero ideal to a nonmaximal
ideal. Finite-type homomorphisms from a Jacobson ring do preserve maximal points.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory TopCat TopologicalSpace Opposite
open AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry.Spec

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [IsJacobsonRing R] [IsJacobsonRing S] [IsJacobsonRing T]
variable (φ : R →+* S)
variable (hφ : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
  (n.asIdeal.comap φ).IsMaximal)

omit [IsJacobsonRing R] [IsJacobsonRing S] in
include hφ in
/-- If maximal ideals remain maximal under contraction, the affine map preserves
closed points. This implication does not require either ring to be Jacobson. -/
lemma locallyRingedSpaceMap_mapsTo_closedPoints :
    Set.MapsTo (locallyRingedSpaceMap (CommRingCat.ofHom φ)).base
      (closedPoints (PrimeSpectrum S)) (closedPoints (PrimeSpectrum R)) := by
  intro x hx
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
    (hφ x ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx))

/-- The full locally ringed space morphism induced by a homomorphism preserving
maximal ideals under contraction. -/
def maximalPointMap : maximalPointSpace S ⟶ maximalPointSpace R :=
  closedPointMap (locallyRingedSpaceMap (CommRingCat.ofHom φ))
    (locallyRingedSpaceMap_mapsTo_closedPoints φ hφ)

@[simp]
lemma maximalPointMap_base_apply (x : maximalPointSpace S) :
    ((maximalPointMap φ hφ).base x).val = PrimeSpectrum.comap φ x.val := rfl

/-- The canonical square commutes, including its full sheaf component. -/
@[reassoc]
lemma maximalPointMap_comp_inclusion :
    maximalPointMap φ hφ ≫ maximalPointInclusion R =
      maximalPointInclusion S ≫ locallyRingedSpaceMap (CommRingCat.ofHom φ) :=
  closedPointMap_comp_fromClosedPoints _ _

set_option backward.isDefEq.respectTransparency false in
/-- On global coordinates the induced morphism is the given ring homomorphism. -/
@[reassoc]
lemma maximalPointMap_coordinates :
    CommRingCat.ofHom (maximalPointCoordinates R).toRingHom ≫
        LocallyRingedSpace.Γ.map (maximalPointMap φ hφ).op =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (maximalPointCoordinates S).toRingHom := by
  have hs := congrArg (fun g : maximalPointSpace S ⟶ locallyRingedSpaceObj (CommRingCat.of R) =>
      LocallyRingedSpace.Γ.map g.op) (maximalPointMap_comp_inclusion φ hφ)
  simp only [op_comp, Functor.map_comp] at hs
  change (toSpecΓ (CommRingCat.of R) ≫
      LocallyRingedSpace.Γ.map (maximalPointInclusion R).op) ≫
        LocallyRingedSpace.Γ.map (maximalPointMap φ hφ).op =
    CommRingCat.ofHom φ ≫ (toSpecΓ (CommRingCat.of S) ≫
      LocallyRingedSpace.Γ.map (maximalPointInclusion S).op)
  calc
    _ = toSpecΓ (CommRingCat.of R) ≫
        (LocallyRingedSpace.Γ.map (maximalPointInclusion R).op ≫
          LocallyRingedSpace.Γ.map (maximalPointMap φ hφ).op) := Category.assoc _ _ _
    _ = toSpecΓ (CommRingCat.of R) ≫
        (LocallyRingedSpace.Γ.map (locallyRingedSpaceMap (CommRingCat.ofHom φ)).op ≫
          LocallyRingedSpace.Γ.map (maximalPointInclusion S).op) :=
      congrArg (fun k => toSpecΓ (CommRingCat.of R) ≫ k) hs
    _ = (toSpecΓ (CommRingCat.of R) ≫
        LocallyRingedSpace.Γ.map (locallyRingedSpaceMap (CommRingCat.ofHom φ)).op) ≫
          LocallyRingedSpace.Γ.map (maximalPointInclusion S).op :=
      (Category.assoc _ _ _).symm
    _ = (CommRingCat.ofHom φ ≫ toSpecΓ (CommRingCat.of S)) ≫
        LocallyRingedSpace.Γ.map (maximalPointInclusion S).op := by
      exact congrArg (fun k : CommRingCat.of R ⟶
          LocallyRingedSpace.Γ.obj (op (locallyRingedSpaceObj (CommRingCat.of S))) =>
        k ≫ LocallyRingedSpace.Γ.map (maximalPointInclusion S).op)
        (Spec_Γ_naturality (CommRingCat.ofHom φ)).symm
    _ = _ := Category.assoc _ _ _

lemma maximalPointMap_coordinates_apply (r : R) :
    (maximalPointMap φ hφ).c.app (op ⊤) (maximalPointCoordinates R r) =
      maximalPointCoordinates S (φ r) :=
  congrArg (fun g => g r) (maximalPointMap_coordinates φ hφ)

set_option backward.isDefEq.respectTransparency false in
/-- The section map on every open preserves the coordinate homomorphism. -/
@[simp]
lemma maximalPointMap_app_algebraMap (W : Opens (maximalPointSpace R)) (r : R) :
    CommRingCat.Hom.hom
        (S := (maximalPointSpace S).presheaf.obj
          (op ((Opens.map (maximalPointMap φ hφ).base).obj W)))
        ((maximalPointMap φ hφ).c.app (op W))
        (algebraMap R ((maximalPointSpace R).presheaf.obj (op W)) r) =
      algebraMap S ((maximalPointSpace S).presheaf.obj
        (op ((Opens.map (maximalPointMap φ hφ).base).obj W))) (φ r) := by
  have hc := maximalPointMap_coordinates_apply φ hφ r
  simp only [maximalPointCoordinates_apply] at hc
  let i : W ⟶ (⊤ : Opens (maximalPointSpace R)) := homOfLE le_top
  have h := congrArg
    (fun k : (maximalPointSpace R).presheaf.obj (op ⊤) ⟶
        (maximalPointSpace S).presheaf.obj
          (op ((Opens.map (maximalPointMap φ hφ).base).obj W)) =>
      k (algebraMap R ((maximalPointSpace R).presheaf.obj (op ⊤)) r))
    ((maximalPointMap φ hφ).c.naturality i.op)
  calc
    _ = (maximalPointMap φ hφ).c.app (op W)
        ((maximalPointSpace R).presheaf.map i.op
          (algebraMap R ((maximalPointSpace R).presheaf.obj (op ⊤)) r)) :=
      congrArg ((maximalPointMap φ hφ).c.app (op W))
        (maximalPoint_map_algebraMap R i r).symm
    _ = (maximalPointSpace S).presheaf.map
        ((Opens.map (maximalPointMap φ hφ).base).map i).op
          ((maximalPointMap φ hφ).c.app (op ⊤)
            (algebraMap R ((maximalPointSpace R).presheaf.obj (op ⊤)) r)) := by
      simpa only [CommRingCat.comp_apply, Presheaf.pushforward_obj_map,
        Presheaf.pushforward_obj_obj, Quiver.Hom.unop_op] using h
    _ = (maximalPointSpace S).presheaf.map
        ((Opens.map (maximalPointMap φ hφ).base).map i).op
          (algebraMap S ((maximalPointSpace S).presheaf.obj (op ⊤)) (φ r)) :=
      congrArg ((maximalPointSpace S).presheaf.map
        ((Opens.map (maximalPointMap φ hφ).base).map i).op) hc
    _ = _ := maximalPoint_map_algebraMap S
      ((Opens.map (maximalPointMap φ hφ).base).map i) (φ r)

/-- The global component preserves any pair of compatible supplied scalar maps. -/
lemma maximalPointMap_scalars {K : Type v} [CommRing K]
    (κR : K →+* R) (κS : K →+* S) (hκ : φ.comp κR = κS) :
    ((maximalPointMap φ hφ).c.app (op ⊤)).hom.comp (maximalPointScalars R κR) =
      maximalPointScalars S κS := by
  ext k
  exact (maximalPointMap_coordinates_apply φ hφ (κR k)).trans
    (congrArg (maximalPointCoordinates S) (RingHom.congr_fun hκ k))

/-- On every open the full section component preserves compatible supplied scalars. -/
lemma maximalPointMap_app_scalars {K : Type v} [CommRing K]
    (κR : K →+* R) (κS : K →+* S) (hκ : φ.comp κR = κS)
    (W : Opens (maximalPointSpace R)) :
    ((maximalPointMap φ hφ).c.app (op W)).hom.comp (maximalPointOpenScalars R κR W) =
      maximalPointOpenScalars S κS ((Opens.map (maximalPointMap φ hφ).base).obj W) := by
  ext k
  exact (maximalPointMap_app_algebraMap φ hφ W (κR k)).trans
    (congrArg (algebraMap S ((maximalPointSpace S).presheaf.obj
      (op ((Opens.map (maximalPointMap φ hφ).base).obj W)))) (RingHom.congr_fun hκ k))

set_option backward.isDefEq.respectTransparency false in
/-- The stalk map preserves the coordinate homomorphism. -/
@[simp]
lemma maximalPointMap_stalkMap_algebraMap (x : maximalPointSpace S) (r : R) :
    (maximalPointMap φ hφ).stalkMap x
        (algebraMap R ((maximalPointSpace R).presheaf.stalk ((maximalPointMap φ hφ).base x)) r) =
      algebraMap S ((maximalPointSpace S).presheaf.stalk x) (φ r) := by
  have hx : (maximalPointMap φ hφ).base x ∈ (⊤ : Opens (maximalPointSpace R)) := by
    trivial
  calc
    _ = (maximalPointMap φ hφ).stalkMap x
        ((maximalPointSpace R).presheaf.germ ⊤ ((maximalPointMap φ hφ).base x) hx
          (algebraMap R ((maximalPointSpace R).presheaf.obj (op ⊤)) r)) :=
      congrArg ((maximalPointMap φ hφ).stalkMap x)
        (maximalPoint_germ_algebraMap R ⊤ ((maximalPointMap φ hφ).base x) hx r).symm
    _ = (maximalPointSpace S).presheaf.germ
        ((Opens.map (maximalPointMap φ hφ).base).obj ⊤) x hx
          ((maximalPointMap φ hφ).c.app (op ⊤)
            (algebraMap R ((maximalPointSpace R).presheaf.obj (op ⊤)) r)) :=
      LocallyRingedSpace.stalkMap_germ_apply (maximalPointMap φ hφ) ⊤ x hx _
    _ = (maximalPointSpace S).presheaf.germ
        ((Opens.map (maximalPointMap φ hφ).base).obj ⊤) x hx
          (algebraMap S ((maximalPointSpace S).presheaf.obj
            (op ((Opens.map (maximalPointMap φ hφ).base).obj ⊤))) (φ r)) :=
      congrArg ((maximalPointSpace S).presheaf.germ
        ((Opens.map (maximalPointMap φ hφ).base).obj ⊤) x hx)
        (maximalPointMap_app_algebraMap φ hφ ⊤ r)
    _ = _ := maximalPoint_germ_algebraMap S
      ((Opens.map (maximalPointMap φ hφ).base).obj ⊤) x hx (φ r)

/-- The canonical stalk component preserves compatible supplied scalar maps. -/
lemma maximalPointMap_stalkMap_scalars {K : Type v} [CommRing K]
    (κR : K →+* R) (κS : K →+* S) (hκ : φ.comp κR = κS)
    (x : maximalPointSpace S) :
    ((maximalPointMap φ hφ).stalkMap x).hom.comp
        (maximalPointStalkScalars R κR ((maximalPointMap φ hφ).base x)) =
      maximalPointStalkScalars S κS x := by
  ext k
  exact (maximalPointMap_stalkMap_algebraMap φ hφ x (κR k)).trans
    (congrArg (algebraMap S _) (RingHom.congr_fun hκ k))

set_option backward.isDefEq.respectTransparency false in
/-- On full localizations, the stalk map is the canonical local ring homomorphism. -/
lemma maximalPointMap_stalkMap_localization (x : maximalPointSpace S) :
    ((maximalPointMap φ hφ).stalkMap x).hom.comp
        (maximalPointStalkIso R ((maximalPointMap φ hφ).base x)).toRingHom =
      (maximalPointStalkIso S x).toRingHom.comp
        (Localization.localRingHom (PrimeSpectrum.comap φ x.val).asIdeal x.val.asIdeal φ rfl) := by
  apply IsLocalization.ringHom_ext (R := R)
    (S := Localization.AtPrime (((maximalPointMap φ hφ).base x).val.asIdeal))
    (P := (maximalPointSpace S).presheaf.stalk x)
    ((maximalPointMap φ hφ).base x).val.asIdeal.primeCompl
  ext r
  simp only [RingHom.comp_apply]
  calc
    _ = (maximalPointMap φ hφ).stalkMap x
        (algebraMap R ((maximalPointSpace R).presheaf.stalk
          ((maximalPointMap φ hφ).base x)) r) :=
      congrArg ((maximalPointMap φ hφ).stalkMap x)
        (maximalPointStalkIso_algebraMap R ((maximalPointMap φ hφ).base x) r)
    _ = algebraMap S ((maximalPointSpace S).presheaf.stalk x) (φ r) :=
      maximalPointMap_stalkMap_algebraMap φ hφ x r
    _ = (maximalPointStalkIso S x).toRingHom
        (algebraMap S (Localization.AtPrime x.val.asIdeal) (φ r)) :=
      (maximalPointStalkIso_algebraMap S x (φ r)).symm
    _ = _ := by
      simpa only [RingHom.comp_apply, maximalPointMap_base_apply] using
        congrArg (maximalPointStalkIso S x).toRingHom
          (Localization.localRingHom_to_map
            (I := (PrimeSpectrum.comap φ x.val).asIdeal) x.val.asIdeal φ rfl r).symm

set_option backward.isDefEq.respectTransparency false in
/-- Reading the stalk homomorphism back through the localization comparisons gives
`Localization.localRingHom`, including on elements not represented by coordinates. -/
lemma maximalPointMap_stalkMap_readback (x : maximalPointSpace S) :
    (maximalPointStalkIso S x).symm.toRingHom.comp
        (((maximalPointMap φ hφ).stalkMap x).hom.comp
          (maximalPointStalkIso R ((maximalPointMap φ hφ).base x)).toRingHom) =
      Localization.localRingHom (PrimeSpectrum.comap φ x.val).asIdeal x.val.asIdeal φ rfl := by
  ext z
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    AlgEquiv.coe_ringEquiv, AlgEquiv.symm_apply_apply] using
    congrArg (maximalPointStalkIso S x).symm
      (DFunLike.congr_fun (maximalPointMap_stalkMap_localization φ hφ x) z)

/-- The map is independent of the proof that contraction preserves maximal ideals. -/
lemma maximalPointMap_proof_irrel (hφ' : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
    (n.asIdeal.comap φ).IsMaximal) :
    maximalPointMap φ hφ = maximalPointMap φ hφ' := rfl

/-- Inverse image takes a principal open to the principal open of the image element. -/
@[simp]
lemma maximalPointMap_preimage_basicOpen (f : R) :
    (Opens.map (maximalPointMap φ hφ).base).obj (maximalPointBasicOpen R f) =
      maximalPointBasicOpen S (φ f) := by
  ext x
  rfl

/-- The principal-open section homomorphism, with its target identified using
inverse image of principal opens. -/
def maximalPointMapBasicOpenHom (f : R) :
    ((maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R f))) →+*
      ((maximalPointSpace S).presheaf.obj (op (maximalPointBasicOpen S (φ f)))) :=
  ((maximalPointSpace S).presheaf.map
    (eqToHom (congrArg op (maximalPointMap_preimage_basicOpen φ hφ f)))).hom.comp
      ((maximalPointMap φ hφ).c.app (op (maximalPointBasicOpen R f))).hom

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma maximalPointMapBasicOpenHom_algebraMap (f r : R) :
    maximalPointMapBasicOpenHom φ hφ f (algebraMap R _ r) = algebraMap S _ (φ r) := by
  calc
    _ = (maximalPointSpace S).presheaf.map
        (eqToHom (congrArg op (maximalPointMap_preimage_basicOpen φ hφ f)))
          (algebraMap S ((maximalPointSpace S).presheaf.obj
            (op ((Opens.map (maximalPointMap φ hφ).base).obj (maximalPointBasicOpen R f))))
              (φ r)) :=
      congrArg ((maximalPointSpace S).presheaf.map
        (eqToHom (congrArg op (maximalPointMap_preimage_basicOpen φ hφ f))))
        (maximalPointMap_app_algebraMap φ hφ (maximalPointBasicOpen R f) r)
    _ = _ := by
      simpa only [eqToHom_op] using
        maximalPoint_map_algebraMap S
          (eqToHom (maximalPointMap_preimage_basicOpen φ hφ f).symm) (φ r)

/-- The principal-open section component preserves compatible supplied scalar maps. -/
lemma maximalPointMapBasicOpenHom_scalars {K : Type v} [CommRing K]
    (κR : K →+* R) (κS : K →+* S) (hκ : φ.comp κR = κS) (f : R) :
    (maximalPointMapBasicOpenHom φ hφ f).comp
        (maximalPointOpenScalars R κR (maximalPointBasicOpen R f)) =
      maximalPointOpenScalars S κS (maximalPointBasicOpen S (φ f)) := by
  ext k
  exact (maximalPointMapBasicOpenHom_algebraMap φ hφ f (κR k)).trans
    (congrArg (algebraMap S _) (RingHom.congr_fun hκ k))

/-- On principal-open localizations the section homomorphism is the canonical
localization of the original ring homomorphism. -/
lemma maximalPointMapBasicOpenHom_localization (f : R) :
    (maximalPointMapBasicOpenHom φ hφ f).comp (maximalPointBasicOpenIso R f).toRingHom =
      (maximalPointBasicOpenIso S (φ f)).toRingHom.comp
        (IsLocalization.Away.map (Localization.Away f) (Localization.Away (φ f)) φ f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  simp only [RingHom.comp_apply, IsLocalization.Away.map, IsLocalization.map_eq]
  calc
    _ = maximalPointMapBasicOpenHom φ hφ f
        (algebraMap R ((maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R f))) r) :=
      congrArg (maximalPointMapBasicOpenHom φ hφ f) (maximalPointBasicOpenIso_algebraMap R f r)
    _ = algebraMap S
        ((maximalPointSpace S).presheaf.obj (op (maximalPointBasicOpen S (φ f)))) (φ r) :=
      maximalPointMapBasicOpenHom_algebraMap φ hφ f r
    _ = _ := (maximalPointBasicOpenIso_algebraMap S (φ f) (φ r)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Reading the principal-open section map back through the localization comparisons
gives the localization of `φ`, also when the principal open is empty. -/
lemma maximalPointMapBasicOpenHom_readback (f : R) :
    (maximalPointBasicOpenIso S (φ f)).symm.toRingHom.comp
        ((maximalPointMapBasicOpenHom φ hφ f).comp
          (maximalPointBasicOpenIso R f).toRingHom) =
      IsLocalization.Away.map (Localization.Away f) (Localization.Away (φ f)) φ f := by
  ext z
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    AlgEquiv.coe_ringEquiv, AlgEquiv.symm_apply_apply] using
    congrArg (maximalPointBasicOpenIso S (φ f)).symm
      (DFunLike.congr_fun (maximalPointMapBasicOpenHom_localization φ hφ f) z)

/-- Extending an arbitrary open to the affine spectrum commutes with inverse image. -/
lemma maximalPointMap_extendOpen (W : Opens (maximalPointSpace R)) :
    (Opens.closedPointsOrderIso (PrimeSpectrum S)).symm
        ((Opens.map (maximalPointMap φ hφ).base).obj W) =
      (Opens.map (locallyRingedSpaceMap (CommRingCat.ofHom φ)).base).obj
        ((Opens.closedPointsOrderIso (PrimeSpectrum R)).symm W) :=
  closedPointMap_extendOpen (locallyRingedSpaceMap (CommRingCat.ofHom φ))
    (locallyRingedSpaceMap_mapsTo_closedPoints φ hφ) W

/-- Full maps into a maximal-point space are determined by their affine comparison. -/
lemma maximalPointMap_unique (g : maximalPointSpace S ⟶ maximalPointSpace R)
    (hg : g ≫ maximalPointInclusion R =
      maximalPointInclusion S ≫ locallyRingedSpaceMap (CommRingCat.ofHom φ)) :
    g = maximalPointMap φ hφ :=
  closedPointMap_unique _ _ g hg

set_option backward.isDefEq.respectTransparency false in
/-- Full morphisms between maximal-point spaces are determined by their
homomorphisms on global coordinates. -/
lemma maximalPoint_hom_ext {g h : maximalPointSpace S ⟶ maximalPointSpace R}
    (H : CommRingCat.ofHom (maximalPointCoordinates R).toRingHom ≫
        LocallyRingedSpace.Γ.map g.op =
      CommRingCat.ofHom (maximalPointCoordinates R).toRingHom ≫
        LocallyRingedSpace.Γ.map h.op) : g = h := by
  apply fromClosedPoints_hom_ext (locallyRingedSpaceObj (CommRingCat.of R))
  apply (ΓSpec.locallyRingedSpaceAdjunction.homEquiv (maximalPointSpace S)
    (op (CommRingCat.of R))).symm.injective
  erw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  apply Quiver.Hom.unop_inj
  have HΓ : (toSpecΓ (CommRingCat.of R) ≫
        LocallyRingedSpace.Γ.map (maximalPointInclusion R).op) ≫
          LocallyRingedSpace.Γ.map g.op =
      (toSpecΓ (CommRingCat.of R) ≫
        LocallyRingedSpace.Γ.map (maximalPointInclusion R).op) ≫
          LocallyRingedSpace.Γ.map h.op := by
    simpa only [maximalPointCoordinates_hom, Γ_map_op] using H
  simpa only [unop_comp, Functor.rightOp_map_unop,
    ΓSpec.unop_locallyRingedSpaceAdjunction_counit_app', op_comp, Functor.map_comp,
    ΓSpec.toSpecΓ_of, Functor.rightOp_obj, unop_op, maximalPointInclusion,
    ← Category.assoc] using HΓ

/-- A given morphism with the original coordinate homomorphism is the constructed
morphism, including its full sheaf component. -/
lemma maximalPointMap_eq_of_coordinates (g : maximalPointSpace S ⟶ maximalPointSpace R)
    (hg : CommRingCat.ofHom (maximalPointCoordinates R).toRingHom ≫
        LocallyRingedSpace.Γ.map g.op =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (maximalPointCoordinates S).toRingHom) :
    g = maximalPointMap φ hφ :=
  maximalPoint_hom_ext (hg.trans (maximalPointMap_coordinates φ hφ).symm)

set_option backward.isDefEq.respectTransparency false in
/-- Identity homomorphisms induce identity morphisms. -/
@[simp]
lemma maximalPointMap_id :
    maximalPointMap (RingHom.id R)
        (fun (n : PrimeSpectrum R) (hn : n.asIdeal.IsMaximal) => by
          simpa only [Ideal.comap_id] using hn) = 𝟙 (maximalPointSpace R) := by
  simpa only [maximalPointMap, maximalPointSpace, CommRingCat.ofHom_id,
    locallyRingedSpaceMap_id] using
    (closedPointMap_id (X := locallyRingedSpaceObj (CommRingCat.of R)))

set_option backward.isDefEq.respectTransparency false in
/-- The construction is contravariantly compatible with composition. -/
lemma maximalPointMap_comp (ψ : S →+* T)
    (hψ : ∀ n : PrimeSpectrum T, n.asIdeal.IsMaximal →
      (n.asIdeal.comap ψ).IsMaximal) :
    maximalPointMap (ψ.comp φ)
        (fun (n : PrimeSpectrum T) (hn : n.asIdeal.IsMaximal) => by
          have hnψ : (PrimeSpectrum.comap ψ n).asIdeal.IsMaximal := by
            simpa only [PrimeSpectrum.comap_asIdeal] using hψ n hn
          simpa only [PrimeSpectrum.comap_asIdeal, Ideal.comap_comap] using
            hφ (PrimeSpectrum.comap ψ n) hnψ) =
      maximalPointMap ψ hψ ≫ maximalPointMap φ hφ := by
  have h := closedPointMap_comp (locallyRingedSpaceMap (CommRingCat.ofHom ψ))
    (locallyRingedSpaceMap_mapsTo_closedPoints ψ hψ)
    (locallyRingedSpaceMap (CommRingCat.ofHom φ))
    (locallyRingedSpaceMap_mapsTo_closedPoints φ hφ)
  simpa only [maximalPointMap, CommRingCat.ofHom_comp, locallyRingedSpaceMap_comp] using h

omit [IsJacobsonRing S] [IsJacobsonRing T] in
/-- A finite-type homomorphism with Jacobson scheme target `Spec R` preserves
maximal points. No Jacobson hypothesis on the ring `S` is needed. -/
lemma maximal_comap_of_finiteType (h : φ.FiniteType)
    (n : PrimeSpectrum S) (hn : n.asIdeal.IsMaximal) :
    (n.asIdeal.comap φ).IsMaximal := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom φ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr h
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
    ((Spec.map (CommRingCat.ofHom φ)).closePoints_subset_preimage_closedPoints
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal n).mpr hn))

omit [IsJacobsonRing S] [IsJacobsonRing T] in
/-- A homomorphism of scalar algebras into a finite-type scalar algebra preserves
maximal ideals under contraction when `Spec R` is Jacobson. The scalar ring may
lie in a different universe and need not be Jacobson. -/
lemma maximal_comap_of_algHom {K : Type v} [CommRing K] [Algebra K R] [Algebra K S]
    [Algebra.FiniteType K S] (φ : R →ₐ[K] S)
    (n : PrimeSpectrum S) (hn : n.asIdeal.IsMaximal) :
    (n.asIdeal.comap φ.toRingHom).IsMaximal := by
  have h : φ.toRingHom.FiniteType :=
    RingHom.FiniteType.of_comp_finiteType (f := algebraMap K R) <| by
      have hcomp : φ.toRingHom.comp (algebraMap K R) = algebraMap K S :=
        φ.comp_algebraMap
      exact hcomp.symm ▸ (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact maximal_comap_of_finiteType φ.toRingHom h n hn

/-- A scalar-linear homomorphism into a finite-type scalar algebra induces a map
of maximal-point spaces. In particular this applies to finitely generated
algebras over an arbitrary field. -/
def maximalPointMapOfAlgHom {K : Type v} [CommRing K] [Algebra K R] [Algebra K S]
    [Algebra.FiniteType K S] (φ : R →ₐ[K] S) :
    maximalPointSpace S ⟶ maximalPointSpace R :=
  maximalPointMap φ.toRingHom (maximal_comap_of_algHom φ)

/-- The scalar-linear construction is the ring-homomorphism construction with
its maximal-contraction proof supplied by finite type. -/
lemma maximalPointMapOfAlgHom_eq {K : Type v} [CommRing K] [Algebra K R] [Algebra K S]
    [Algebra.FiniteType K S] (φ : R →ₐ[K] S) :
    maximalPointMapOfAlgHom φ =
      maximalPointMap φ.toRingHom (maximal_comap_of_algHom φ) := rfl

/-- On global coordinates the scalar-linear construction induces the supplied
algebra homomorphism. -/
@[reassoc]
lemma maximalPointMapOfAlgHom_coordinates {K : Type v} [CommRing K]
    [Algebra K R] [Algebra K S] [Algebra.FiniteType K S] (φ : R →ₐ[K] S) :
    CommRingCat.ofHom (maximalPointCoordinates R).toRingHom ≫
        LocallyRingedSpace.Γ.map (maximalPointMapOfAlgHom φ).op =
      CommRingCat.ofHom φ.toRingHom ≫
        CommRingCat.ofHom (maximalPointCoordinates S).toRingHom :=
  maximalPointMap_coordinates φ.toRingHom (maximal_comap_of_algHom φ)

end AlgebraicGeometry.Spec
