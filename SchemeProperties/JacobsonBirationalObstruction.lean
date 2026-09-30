/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Birational obstruction for Jacobson schemes

A dense open of a Jacobson space cannot contain at most one point unless the entire
space contains at most one point. Applied to the open subschemes in a partial
isomorphism, this rules out birationality between a one-point scheme and a
nontrivial Jacobson scheme. The empty case is included.
-/

@[expose] public section

set_option warningAsError true

open CategoryTheory
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme

/-- A partial isomorphism from a scheme with at most one point to a Jacobson scheme
forces the target to have at most one point, including when the source is empty. -/
theorem PartialIso.subsingleton_target {X Y : Scheme.{u}} [Subsingleton X]
    [JacobsonSpace Y] (p : X.PartialIso Y) : Subsingleton Y := by
  have sourceSetSubsingleton : (p.source : Set X).Subsingleton :=
    Set.subsingleton_of_subsingleton
  have sourceSubsingleton : Subsingleton p.source.toScheme :=
    sourceSetSubsingleton.coe_sort
  have targetSubsingleton : Subsingleton p.target.toScheme :=
    p.iso.hom.homeomorph.subsingleton_congr.mp sourceSubsingleton
  have targetSetSubsingleton : (p.target : Set Y).Subsingleton :=
    (Set.subsingleton_coe _).mp targetSubsingleton
  have closureSubsingleton :
      (closure (p.target : Set Y)).Subsingleton := by
    simpa only [Set.image_id] using
      (subsingleton_image_closure_of_finite_of_isPreirreducible (f := id)
        p.target.isOpen.isLocallyClosed targetSetSubsingleton.isPreirreducible
        continuous_id IsClosedMap.id (by simpa only [Set.image_id] using
          targetSetSubsingleton.finite))
  exact Set.subsingleton_univ_iff.mp (p.dense_target.closure_eq ▸ closureSubsingleton)

/-- A scheme with at most one point is not birational to a nontrivial Jacobson scheme. -/
theorem not_birational_of_subsingleton_of_jacobson {X Y : Scheme.{u}}
    [Subsingleton X] [JacobsonSpace Y] [Nontrivial Y] : ¬Birational X Y := by
  rintro ⟨p⟩
  exact not_subsingleton_iff_nontrivial.mpr inferInstance p.subsingleton_target

/-- The spectrum of a polynomial ring over a field has at least two points. -/
theorem nontrivial_spec_polynomial (k : Type u) [Field k] :
    Nontrivial (Spec (CommRingCat.of k[X])) := by
  change Nontrivial (PrimeSpectrum k[X])
  apply not_subsingleton_iff_nontrivial.mp
  intro h
  exact Polynomial.not_isField k
    (PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp h)

/-- The spectrum of a field is not birational to the polynomial spectrum of any
field (with both fields living in the same universe). -/
theorem not_birational_spec_field_spec_polynomial (K k : Type u) [Field K] [Field k] :
    ¬Birational (Spec (CommRingCat.of K)) (Spec (CommRingCat.of k[X])) := by
  have hNontrivial : Nontrivial (Spec (CommRingCat.of k[X])) := nontrivial_spec_polynomial k
  exact @not_birational_of_subsingleton_of_jacobson _ _ _ _ hNontrivial

end AlgebraicGeometry.Scheme
