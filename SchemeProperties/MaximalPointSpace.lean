/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ClosedPointLocallyRingedSpace
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# The locally ringed space of maximal points of an affine spectrum

For a commutative Jacobson ring `R`, `Spec.maximalPointSpace R` is the locally
ringed space on the existing closed-point subspace of `PrimeSpectrum R`.
Its sheaf has the full localization rings, including nilpotents. The canonical
map to `Spec R` induces isomorphisms on all section rings and all stalks.

The construction reuses Mathlib's full affine structure sheaf, its localization
instances and its global-section isomorphism. The zero ring is allowed.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory TopCat TopologicalSpace Opposite Topology
open AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry.Spec

variable (R : Type u) [CommRing R] [IsJacobsonRing R]

/-- The underlying space of the affine locally ringed space of a Jacobson ring
is Jacobson. -/
instance locallyRingedSpaceObj_jacobsonSpace :
    JacobsonSpace (locallyRingedSpaceObj (CommRingCat.of R)).toTopCat :=
  inferInstanceAs (JacobsonSpace (PrimeSpectrum R))

/-- The locally ringed space on the maximal points of the affine spectrum. -/
def maximalPointSpace : LocallyRingedSpace :=
  (locallyRingedSpaceObj (CommRingCat.of R)).closedPointSpace

/-- The inclusion of maximal points as a morphism of locally ringed spaces. -/
def maximalPointInclusion : maximalPointSpace R ⟶ locallyRingedSpaceObj (CommRingCat.of R) :=
  (locallyRingedSpaceObj (CommRingCat.of R)).fromClosedPoints

@[simp]
lemma maximalPointInclusion_base_apply (x : maximalPointSpace R) :
    (maximalPointInclusion R).base x = x.val := rfl

/-- Inverse image under the inclusion is the closed-point trace of an ambient open. -/
@[simp]
lemma maximalPointInclusion_preimage (U : Opens (PrimeSpectrum R)) :
    (Opens.map (maximalPointInclusion R).base).obj U =
      (Opens.closedPointsOrderIso (PrimeSpectrum R)) U := rfl

/-- A point of the maximal-point space corresponds to a maximal ideal. -/
instance maximalPoint_asIdeal_isMaximal (x : maximalPointSpace R) :
    x.val.asIdeal.IsMaximal :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal (x.val : PrimeSpectrum R)).mp x.property

/-- The full sheaf comparison for the inclusion of maximal points. -/
def maximalPointSheafIso : (structureSheaf R).obj ≅
    (maximalPointInclusion R).base _* (maximalPointSpace R).presheaf :=
  (locallyRingedSpaceObj (CommRingCat.of R)).closedPointSheafIso

@[simp]
lemma maximalPointSheafIso_hom :
    (maximalPointSheafIso R).hom = (maximalPointInclusion R).c := rfl

/-- The full sheaf component of the canonical inclusion is an isomorphism. -/
instance maximalPointInclusion_c_isIso : IsIso (maximalPointInclusion R).c :=
  (maximalPointSheafIso R).isIso_hom

/-- Sections on every open carry their given coordinate-ring algebra structure. -/
instance maximalPointOpenAlgebra (W : (Opens (maximalPointSpace R))ᵒᵖ) :
    Algebra R ((maximalPointSpace R).presheaf.obj W) :=
  inferInstanceAs (Algebra R ((structureSheaf R).obj.obj
    (op ((Opens.closedPointsOrderIso (PrimeSpectrum R)).symm W.unop))))

/-- Restrictions preserve coordinates on every open. -/
@[simp, reassoc]
lemma maximalPoint_algebraMap_map {U V : Opens (maximalPointSpace R)} (i : U ⟶ V) :
    CommRingCat.ofHom (algebraMap R ((maximalPointSpace R).presheaf.obj (op V))) ≫
        (maximalPointSpace R).presheaf.map i.op =
      CommRingCat.ofHom (algebraMap R ((maximalPointSpace R).presheaf.obj (op U))) :=
  StructureSheaf.algebraMap_self_map R _ _
    (((Opens.closedPointsOrderIso (PrimeSpectrum R)).symm.monotone.functor.map i).op)

/-- Coordinate elements are preserved under every restriction. -/
@[simp]
lemma maximalPoint_map_algebraMap {U V : Opens (maximalPointSpace R)} (i : U ⟶ V) (r : R) :
    (maximalPointSpace R).presheaf.map i.op (algebraMap R _ r) = algebraMap R _ r :=
  congrArg (fun g => g r) (maximalPoint_algebraMap_map R i)

/-- The all-open section comparison, as an algebra isomorphism over `R`. -/
def maximalPointSectionsIso (U : Opens (PrimeSpectrum R)) :
    (structureSheaf R).obj.obj (op U) ≃ₐ[R]
      (maximalPointSpace R).presheaf.obj
        (op ((Opens.closedPointsOrderIso (PrimeSpectrum R)) U)) where
  __ := ((maximalPointSheafIso R).app (op U)).commRingCatIsoToRingEquiv
  commutes' r := by
    change ((structureSheaf R).obj.map _).hom (algebraMap R _ r) = algebraMap R _ r
    exact congrArg (fun g => g r) (StructureSheaf.algebraMap_self_map R _ _ _)

@[simp]
lemma maximalPointSectionsIso_apply (U : Opens (PrimeSpectrum R))
    (s : (structureSheaf R).obj.obj (op U)) :
    maximalPointSectionsIso R U s = (maximalPointInclusion R).c.app (op U) s := rfl

/-- The basic open of maximal points on which `f` is invertible. -/
def maximalPointBasicOpen (f : R) : Opens (maximalPointSpace R) :=
  (Opens.closedPointsOrderIso (PrimeSpectrum R)) (PrimeSpectrum.basicOpen f)

@[simp]
lemma mem_maximalPointBasicOpen (f : R) (x : maximalPointSpace R) :
    x ∈ maximalPointBasicOpen R f ↔ f ∉ x.val.asIdeal := Iff.rfl

/-- The sections on a principal open form a localization, including an empty open. -/
instance maximalPointBasicOpen_isLocalization (f : R) :
    IsLocalization.Away f ((maximalPointSpace R).presheaf.obj
      (op (maximalPointBasicOpen R f))) :=
  IsLocalization.isLocalization_of_algEquiv (Submonoid.powers f)
    (maximalPointSectionsIso R (PrimeSpectrum.basicOpen f))

/-- The principal-open comparison with the localization away from `f`. -/
def maximalPointBasicOpenIso (f : R) :
    Localization.Away f ≃ₐ[R]
      (maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R f)) :=
  IsLocalization.algEquiv (Submonoid.powers f) _ _

/-- The principal-open localization isomorphism reads coordinates as the canonical
coordinate map, including through its underlying ring homomorphism. -/
lemma maximalPointBasicOpenIso_algebraMap (f r : R) :
    (maximalPointBasicOpenIso R f).toRingHom (algebraMap R (Localization.Away f) r) =
      algebraMap R ((maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R f))) r :=
  (maximalPointBasicOpenIso R f).commutes r

/-- Restriction on principal opens is the unique homomorphism preserving coordinates. -/
lemma maximalPointBasicOpen_restriction_unique (f g : R)
    (i : maximalPointBasicOpen R g ⟶ maximalPointBasicOpen R f)
    (ψ : ((maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R f))) →+*
      ((maximalPointSpace R).presheaf.obj (op (maximalPointBasicOpen R g))))
    (hψ : ψ.comp (algebraMap R _) = algebraMap R _) :
    ψ = ((maximalPointSpace R).presheaf.map i.op).hom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  exact (RingHom.congr_fun hψ r).trans (maximalPoint_map_algebraMap R i r).symm

/-- The canonical map from the affine stalk is an isomorphism. -/
instance maximalPointInclusion_stalkMap_isIso (x : maximalPointSpace R) :
    IsIso ((maximalPointInclusion R).stalkMap x) :=
  fromClosedPoints_stalkMap_isIso _ x

/-- The coordinate action on a full maximal stalk, via the canonical stalk map. -/
instance maximalPointStalkAlgebra (x : maximalPointSpace R) :
    Algebra R ((maximalPointSpace R).presheaf.stalk x) :=
  letI := StructureSheaf.stalkAlgebra R (x.val : PrimeSpectrum R)
  (((maximalPointInclusion R).stalkMap x).hom.comp
    (algebraMap R ((structureSheaf R).presheaf.stalk x.val))).toAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- Germs preserve the coordinate action on every open. -/
@[simp]
lemma maximalPoint_germ_algebraMap (W : Opens (maximalPointSpace R))
    (x : maximalPointSpace R) (hx : x ∈ W) (r : R) :
    (maximalPointSpace R).presheaf.germ W x hx (algebraMap R _ r) =
      algebraMap R ((maximalPointSpace R).presheaf.stalk x) r := by
  let := StructureSheaf.stalkAlgebra R (x.val : PrimeSpectrum R)
  obtain ⟨U, rfl⟩ := (Opens.closedPointsOrderIso (PrimeSpectrum R)).surjective W
  rw [← (maximalPointSectionsIso R U).commutes r, maximalPointSectionsIso_apply]
  have h := LocallyRingedSpace.stalkMap_germ_apply (maximalPointInclusion R) U x hx
    (algebraMap R ((structureSheaf R).obj.obj (op U)) r)
  have hA : (locallyRingedSpaceObj (CommRingCat.of R)).presheaf.germ U x.val hx
      (algebraMap R ((structureSheaf R).obj.obj (op U)) r) =
        algebraMap R ((structureSheaf R).presheaf.stalk x.val) r :=
    StructureSheaf.algebraMap_germ_apply U (x.val : PrimeSpectrum R) hx r
  calc
    _ = (maximalPointInclusion R).stalkMap x
        ((locallyRingedSpaceObj (CommRingCat.of R)).presheaf.germ U x.val hx
          (algebraMap R ((structureSheaf R).obj.obj (op U)) r)) := by
      simpa only [maximalPointInclusion_preimage, maximalPointInclusion_base_apply] using h.symm
    _ = _ := congrArg ((maximalPointInclusion R).stalkMap x) hA

/-- The canonical stalk map as an algebra isomorphism. -/
def maximalPointStalkComparison (x : maximalPointSpace R) :
    letI := StructureSheaf.stalkAlgebra R (x.val : PrimeSpectrum R);
    (structureSheaf R).presheaf.stalk x.val ≃ₐ[R] (maximalPointSpace R).presheaf.stalk x := by
  letI := StructureSheaf.stalkAlgebra R (x.val : PrimeSpectrum R)
  exact
    { __ := (asIso ((maximalPointInclusion R).stalkMap x)).commRingCatIsoToRingEquiv
      commutes' := fun _ => rfl }

@[simp]
lemma maximalPointStalkComparison_apply (x : maximalPointSpace R)
    (s : (structureSheaf R).presheaf.stalk x.val) :
    maximalPointStalkComparison R x s = (maximalPointInclusion R).stalkMap x s := rfl

/-- A maximal stalk is the full localization at the corresponding maximal ideal. -/
instance maximalPointStalk_isLocalization (x : maximalPointSpace R) :
    IsLocalization.AtPrime ((maximalPointSpace R).presheaf.stalk x) x.val.asIdeal := by
  let := StructureSheaf.stalkAlgebra R (x.val : PrimeSpectrum R)
  have : IsLocalization.AtPrime ((structureSheaf R).presheaf.stalk x.val) x.val.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R (x.val : PrimeSpectrum R)
  exact IsLocalization.isLocalization_of_algEquiv x.val.asIdeal.primeCompl
    (maximalPointStalkComparison R x)

/-- The full localization at a maximal ideal identifies with the stalk. -/
def maximalPointStalkIso (x : maximalPointSpace R) :
    Localization.AtPrime x.val.asIdeal ≃ₐ[R] (maximalPointSpace R).presheaf.stalk x :=
  IsLocalization.algEquiv x.val.asIdeal.primeCompl _ _

/-- The maximal localization isomorphism reads coordinates as the canonical
coordinate action on the full maximal-ideal stalk. -/
lemma maximalPointStalkIso_algebraMap (x : maximalPointSpace R) (r : R) :
    (maximalPointStalkIso R x).toRingHom (algebraMap R (Localization.AtPrime x.val.asIdeal) r) =
      algebraMap R ((maximalPointSpace R).presheaf.stalk x) r :=
  (maximalPointStalkIso R x).commutes r

set_option backward.isDefEq.respectTransparency false in
/-- The localization comparison factors through the canonical affine stalk map. -/
lemma maximalPointStalkIso_eq (x : maximalPointSpace R) :
    maximalPointStalkIso R x =
      (StructureSheaf.stalkIso R x.val :
        @AlgEquiv R (Localization.AtPrime x.val.asIdeal)
          ((structureSheaf R).presheaf.stalk x.val) _ _ _ _
          (StructureSheaf.stalkAlgebra R (x.val : PrimeSpectrum R))).trans
        (maximalPointStalkComparison R x) := by
  let := StructureSheaf.stalkAlgebra R (x.val : PrimeSpectrum R)
  apply AlgEquiv.coe_toAlgHom_injective
  exact (IsLocalization.algHom_subsingleton x.val.asIdeal.primeCompl).elim _ _

set_option backward.isDefEq.respectTransparency false in
/-- A principal-open germ is the canonical homomorphism from the away
localization to the localization at the maximal ideal. This also determines
germs of fractions by the localization universal property. -/
lemma maximalPointBasicOpen_germ_localization (f : R) (x : maximalPointSpace R)
    (hx : x ∈ maximalPointBasicOpen R f) :
    ((maximalPointSpace R).presheaf.germ (maximalPointBasicOpen R f) x hx).hom.comp
        (maximalPointBasicOpenIso R f).toRingHom =
      (maximalPointStalkIso R x).toRingHom.comp
        (IsLocalization.map (Localization.AtPrime x.val.asIdeal) (RingHom.id R)
          (show Submonoid.powers f ≤ Submonoid.comap (RingHom.id R) x.val.asIdeal.primeCompl
            from Submonoid.powers_le.mpr hx)) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  simp only [RingHom.comp_apply, maximalPointBasicOpenIso_algebraMap,
    maximalPoint_germ_algebraMap, IsLocalization.map_eq, RingHom.id_apply]
  exact (maximalPointStalkIso_algebraMap R x r).symm

/-- The global coordinate isomorphism, induced by the canonical inclusion. -/
def maximalPointCoordinates : R ≃+* ((maximalPointSpace R).presheaf.obj (op ⊤)) :=
  ((StructureSheaf.globalSectionsIso R) ≪≫
    (maximalPointSheafIso R).app (op ⊤)).commRingCatIsoToRingEquiv

/-- The coordinate homomorphism is the global section map of the inclusion after
Mathlib's canonical affine coordinate homomorphism. -/
lemma maximalPointCoordinates_hom :
    CommRingCat.ofHom (maximalPointCoordinates R).toRingHom =
      toSpecΓ (CommRingCat.of R) ≫ (maximalPointInclusion R).c.app (op ⊤) := by
  rw [ΓSpec.toSpecΓ_of]
  rfl

@[simp]
lemma maximalPointCoordinates_apply (r : R) :
    maximalPointCoordinates R r = algebraMap R _ r :=
  (maximalPointSectionsIso R ⊤).commutes r

/-- Any supplied scalar homomorphism acts through the coordinate isomorphism. -/
def maximalPointScalars {K : Type v} [CommRing K] (κ : K →+* R) :
    K →+* ((maximalPointSpace R).presheaf.obj (op ⊤)) :=
  (maximalPointCoordinates R).toRingHom.comp κ

@[simp]
lemma maximalPointScalars_apply {K : Type v} [CommRing K] (κ : K →+* R) (k : K) :
    maximalPointScalars R κ k = algebraMap R _ (κ k) := by
  simp [maximalPointScalars]

/-- The scalar map on an arbitrary open, for any supplied scalar homomorphism. -/
def maximalPointOpenScalars {K : Type v} [CommRing K] (κ : K →+* R)
    (W : Opens (maximalPointSpace R)) :
    K →+* ((maximalPointSpace R).presheaf.obj (op W)) :=
  (algebraMap R _).comp κ

/-- The scalar map on the full stalk. -/
def maximalPointStalkScalars {K : Type v} [CommRing K] (κ : K →+* R)
    (x : maximalPointSpace R) : K →+* ((maximalPointSpace R).presheaf.stalk x) :=
  (algebraMap R _).comp κ

@[simp]
lemma maximalPointOpenScalars_apply {K : Type v} [CommRing K] (κ : K →+* R)
    (W : Opens (maximalPointSpace R)) (k : K) :
    maximalPointOpenScalars R κ W k = algebraMap R _ (κ k) := rfl

@[simp]
lemma maximalPointStalkScalars_apply {K : Type v} [CommRing K] (κ : K →+* R)
    (x : maximalPointSpace R) (k : K) :
    maximalPointStalkScalars R κ x k = algebraMap R _ (κ k) := rfl

/-- Every restriction preserves the supplied scalar map. -/
lemma maximalPointOpenScalars_restriction {K : Type v} [CommRing K] (κ : K →+* R)
    {U V : Opens (maximalPointSpace R)} (i : U ⟶ V) :
    ((maximalPointSpace R).presheaf.map i.op).hom.comp (maximalPointOpenScalars R κ V) =
      maximalPointOpenScalars R κ U := by
  ext k
  exact maximalPoint_map_algebraMap R i (κ k)

/-- Germs preserve the supplied scalar map. -/
lemma maximalPointOpenScalars_germ {K : Type v} [CommRing K] (κ : K →+* R)
    (W : Opens (maximalPointSpace R)) (x : maximalPointSpace R) (hx : x ∈ W) :
    ((maximalPointSpace R).presheaf.germ W x hx).hom.comp (maximalPointOpenScalars R κ W) =
      maximalPointStalkScalars R κ x := by
  ext k
  exact maximalPoint_germ_algebraMap R W x hx (κ k)

/-- The principal-open localization comparison preserves every supplied scalar. -/
lemma maximalPointBasicOpenIso_scalar {K : Type v} [CommRing K]
    (κ : K →+* R) (f : R) (k : K) :
    maximalPointBasicOpenIso R f (algebraMap R _ (κ k)) =
      maximalPointOpenScalars R κ (maximalPointBasicOpen R f) k :=
  (maximalPointBasicOpenIso R f).commutes (κ k)

/-- The full-stalk localization comparison preserves every supplied scalar. -/
lemma maximalPointStalkIso_scalar {K : Type v} [CommRing K]
    (κ : K →+* R) (x : maximalPointSpace R) (k : K) :
    maximalPointStalkIso R x (algebraMap R _ (κ k)) = maximalPointStalkScalars R κ x k :=
  (maximalPointStalkIso R x).commutes (κ k)

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion is the canonical affine comparison after identifying global coordinates. -/
lemma maximalPointInclusion_eq_toΓSpec :
    maximalPointInclusion R = (maximalPointSpace R).toΓSpec ≫
      locallyRingedSpaceMap (CommRingCat.ofHom (maximalPointCoordinates R).toRingHom) := by
  have h : (ΓSpec.locallyRingedSpaceAdjunction.homEquiv (maximalPointSpace R)
      (op (CommRingCat.of R))).symm (maximalPointInclusion R) =
        (CommRingCat.ofHom (maximalPointCoordinates R).toRingHom).op := by
    apply Quiver.Hom.unop_inj
    simp only [Adjunction.homEquiv_counit, unop_comp, Functor.rightOp_map_unop,
      ΓSpec.unop_locallyRingedSpaceAdjunction_counit_app', Γ_map_op,
      Quiver.Hom.unop_op, maximalPointCoordinates_hom, ΓSpec.toSpecΓ_of]
  calc
    maximalPointInclusion R =
        (ΓSpec.locallyRingedSpaceAdjunction.homEquiv (maximalPointSpace R)
          (op (CommRingCat.of R)))
            (CommRingCat.ofHom (maximalPointCoordinates R).toRingHom).op := by
      rw [← h, Equiv.apply_symm_apply]
    _ = _ := ΓSpec.locallyRingedSpaceAdjunction_homEquiv_apply' _

end AlgebraicGeometry.Spec
