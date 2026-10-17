/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.NormalMorphisms
import SchemeProperties.NormalLocalization
import SchemeProperties.NormalPolynomial
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

@[expose] public section

/-!
# Normal affine schemes over the integers

The affine-line projection `Spec ℤ[X] → Spec ℤ` is smooth, flat and surjective
on points. Both schemes are normal independently of the scheme-morphism
normality theorems: use integral closedness of `ℤ`, polynomial local normality,
and the affine-spectrum criterion. Surjectivity is on spectra, not on the
coefficient inclusion `ℤ → ℤ[X]`.

The canonical localization morphism `Spec ℤ[1/2] → Spec ℤ` is étale, hence
smooth. Its source normality uses localization, not smooth or étale ascent.
The empty open subscheme of `Spec ℤ` supplies an empty normal scheme.

## References

Mathlib supplies smooth polynomial algebras, free polynomial modules, faithful
flatness, localization étaleness, and the corresponding spectrum dictionaries.
The independent normality proofs use `SchemeProperties.Normal`,
`SchemeProperties.NormalPolynomial`, and `SchemeProperties.NormalLocalization`.
The localization and polynomial algebra models also occur at ring level in
`SchemePropertiesTest.NormalEtaleAscent` and
`SchemePropertiesTest.NormalFaithfullyFlat`.
-/

open AlgebraicGeometry CategoryTheory
open scoped Polynomial

noncomputable section

namespace SchemePropertiesTest.NormalMorphisms

private theorem int_isDomain : IsDomain ℤ := inferInstance

private theorem int_isIntegrallyClosed : IsIntegrallyClosed ℤ := inferInstance

private theorem int_locallyNormal : IsLocallyNormalRing ℤ := by
  let _ := int_isDomain
  let _ := int_isIntegrallyClosed
  exact isLocallyNormalRing_of_isDomain ℤ

private theorem polynomial_locallyNormal : IsLocallyNormalRing ℤ[X] := by
  let _ := int_locallyNormal
  exact Polynomial.isLocallyNormalRing_of_isLocallyNormalRing

private theorem integerSpectrum_normal : IsNormal (Spec (.of ℤ)) := by
  let _ := int_locallyNormal
  exact normalSpec

private theorem affineLine_normal : IsNormal (Spec (.of ℤ[X])) := by
  let _ := polynomial_locallyNormal
  exact normalSpec

private def affineLineProjection : Spec (.of ℤ[X]) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ ℤ[X]))

private theorem polynomial_smooth : Algebra.Smooth ℤ ℤ[X] where

private theorem affineLineProjection_smooth : Smooth affineLineProjection := by
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr polynomial_smooth)

private theorem affineLine_normal_of_smooth : IsNormal (Spec (.of ℤ[X])) := by
  let _ := integerSpectrum_normal
  let _ := affineLineProjection_smooth
  exact isNormal_of_smooth affineLineProjection

private theorem polynomial_free : Module.Free ℤ ℤ[X] := inferInstance

private theorem polynomial_faithfullyFlat : Module.FaithfullyFlat ℤ ℤ[X] := by
  let _ := polynomial_free
  infer_instance

private theorem affineLineProjection_flat_surjective :
    Flat affineLineProjection ∧ Surjective affineLineProjection := by
  exact (flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr polynomial_faithfullyFlat)

private theorem affineLineProjection_flat : Flat affineLineProjection :=
  affineLineProjection_flat_surjective.1

private theorem affineLineProjection_surjective : Surjective affineLineProjection :=
  affineLineProjection_flat_surjective.2

private theorem coefficientMap_not_surjective :
    ¬ Function.Surjective (algebraMap ℤ ℤ[X]) := by
  intro h
  obtain ⟨a, ha⟩ := h Polynomial.X
  exact Polynomial.X_ne_C a ha.symm

private theorem integerSpectrum_nonempty : Nonempty (Spec (.of ℤ)) := inferInstance

private theorem affineLine_nonempty : Nonempty (Spec (.of ℤ[X])) := inferInstance

private def awayTwoMorphism : Spec (.of (Localization.Away (2 : ℤ))) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (2 : ℤ))))

private theorem awayTwo_etale : Algebra.Etale ℤ (Localization.Away (2 : ℤ)) :=
  Algebra.Etale.of_isLocalizationAway (2 : ℤ)

private theorem awayTwoMorphism_etale : Etale awayTwoMorphism := by
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr awayTwo_etale)

private theorem awayTwoMorphism_smooth : Smooth awayTwoMorphism := by
  let _ := awayTwoMorphism_etale
  infer_instance

private theorem awayTwo_locallyNormal : IsLocallyNormalRing (Localization.Away (2 : ℤ)) := by
  let _ := int_locallyNormal
  exact IsLocallyNormalRing.of_isLocalization (Submonoid.powers (2 : ℤ))
    (Localization.Away (2 : ℤ))

private theorem awayTwoSpectrum_normal : IsNormal (Spec (.of (Localization.Away (2 : ℤ)))) := by
  let _ := awayTwo_locallyNormal
  exact normalSpec

private theorem emptyOpen_normal : IsNormal ((⊥ : (Spec (.of ℤ)).Opens) : Scheme) := by
  let _ := integerSpectrum_normal
  infer_instance

private theorem integerSpectrum_normal_of_affineLineProjection :
    IsNormal (Spec (.of ℤ)) := by
  let _ := affineLineProjection_surjective
  let _ := affineLineProjection_flat
  let _ := affineLine_normal
  exact isNormal_of_surjective_of_flat affineLineProjection

end SchemePropertiesTest.NormalMorphisms
