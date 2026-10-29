/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.MaximalPointMorphisms
public import SchemeProperties.Topology.LocalizationSheafMaps

/-!
# Uniqueness of affine and maximal-point sheaf components

Over a fixed continuous map to an affine spectrum, a full presheaf
component with values in a sheaf is determined by its map on global
coordinates. The same holds for the maximal-point space of a Jacobson
ring. The supplied component is not required to be a morphism of locally
ringed spaces, and the target sheaf needs no coordinate algebra or
local-ring structure.

In particular, a supplied component over the continuous map induced by a
ring homomorphism preserving maximal ideals equals the constructed
component as soon as it has the prescribed global coordinate homomorphism.
All section rings are the full rings, with their nilpotents retained.
-/

@[expose] public section

universe u

open CategoryTheory TopCat TopologicalSpace Opposite

namespace AlgebraicGeometry.Spec

variable (R : Type u) [CommRing R]

set_option backward.isDefEq.respectTransparency.types false in
/-- Two full presheaf components over the same continuous map to an affine
spectrum are equal if they agree on global coordinates. No locality
condition is imposed on either component. This is the global-coordinate
form of the fixed-base uniqueness used in `Spec.basicOpen_hom_ext`. -/
theorem structureSheaf_component_ext {Y : TopCat.{u}} (G : Sheaf CommRingCat.{u} Y)
    (f : Y ⟶ PrimeSpectrum.Top R)
    {α β : (structureSheaf R).obj ⟶ f _* G.obj}
    (h : CommRingCat.ofHom (algebraMap R _) ≫ α.app (op ⊤) =
      CommRingCat.ofHom (algebraMap R _) ≫ β.app (op ⊤)) : α = β := by
  apply TopCat.Presheaf.hom_ext_of_isLocalizationAway R
    (structureSheaf R).obj ((TopCat.Sheaf.pushforward CommRingCat f).obj G)
    PrimeSpectrum.basicOpen PrimeSpectrum.isBasis_basic_opens
    (fun i r => congrArg (fun g => g r) (StructureSheaf.algebraMap_self_map R _ _ i.op))
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom,
    TopCat.Sheaf.pushforward_obj_val] using! congrArg CommRingCat.Hom.hom h

variable [IsJacobsonRing R]

set_option backward.isDefEq.respectTransparency false in
/-- Two full presheaf components over the same continuous map to the
maximal-point space are equal if they agree on global coordinates.
Neither component is assumed to satisfy a locality condition. -/
theorem maximalPoint_component_ext {Y : TopCat.{u}} (G : Sheaf CommRingCat.{u} Y)
    (f : Y ⟶ (maximalPointSpace R).toTopCat)
    {α β : (maximalPointSpace R).presheaf ⟶ f _* G.obj}
    (h : CommRingCat.ofHom (maximalPointCoordinates R).toRingHom ≫ α.app (op ⊤) =
      CommRingCat.ofHom (maximalPointCoordinates R).toRingHom ≫ β.app (op ⊤)) :
    α = β := by
  apply TopCat.Presheaf.hom_ext_of_isLocalizationAway R
    (maximalPointSpace R).presheaf ((TopCat.Sheaf.pushforward CommRingCat f).obj G)
    (maximalPointBasicOpen R) (maximalPointBasicOpen_isBasis R)
    (fun i r => maximalPoint_map_algebraMap R i r)
  have hhom := congrArg CommRingCat.Hom.hom h
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hhom
  ext r
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    maximalPointCoordinates_apply, TopCat.Sheaf.pushforward_obj_val] using
    RingHom.congr_fun hhom r

variable {R}
variable {S : Type u} [CommRing S] [IsJacobsonRing S]

/-- A supplied full component over the continuous map induced by a
homomorphism preserving maximal ideals is the constructed component if
its global coordinate homomorphism is the given ring homomorphism.
This conclusion does not require locality of the supplied component. -/
theorem maximalPointMap_component_eq_of_coordinates (φ : R →+* S)
    (hφ : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap φ).IsMaximal)
    (α : (maximalPointSpace R).presheaf ⟶
      (maximalPointMap φ hφ).base _* (maximalPointSpace S).presheaf)
    (hα : CommRingCat.ofHom (maximalPointCoordinates R).toRingHom ≫ α.app (op ⊤) =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (maximalPointCoordinates S).toRingHom) :
    α = (maximalPointMap φ hφ).c := by
  apply maximalPoint_component_ext R (maximalPointSpace S).sheaf
    (maximalPointMap φ hφ).base
  exact hα.trans (maximalPointMap_coordinates φ hφ).symm

end AlgebraicGeometry.Spec
