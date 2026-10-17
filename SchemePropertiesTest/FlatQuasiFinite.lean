/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.RingTheory.KrullDimension.QuasiFinite
import SchemeProperties.FlatQuasiFinite
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Ideal

/-!
# A double cover of the affine line

The diagonal map `Spec (R × R) ⟶ Spec R`, for `R = (ZMod 2)[T]`, is finite
free of rank two, flat and locally quasi-finite. At the closed origin of its
first component, both full stalk dimensions are independently calculated to
be one. The final theorem applies pointwise dimension preservation to this
specified map and point, using the flat and quasi-finite stalk witnesses.
-/

open CategoryTheory AlgebraicGeometry

namespace SchemePropertiesTest.FlatQuasiFinite

noncomputable section

/-- The affine line over the two-element field, with polynomial variable denoted by `T`. -/
private abbrev doubleCoverBaseRing := Polynomial (ZMod 2)

private abbrev doubleCoverBase : Scheme := Spec (CommRingCat.of doubleCoverBaseRing)

private abbrev doubleCoverSource : Scheme :=
  Spec (CommRingCat.of (doubleCoverBaseRing × doubleCoverBaseRing))

/-- The canonical double cover, induced by `r ↦ (r, r)`. -/
private abbrev diagonalDoubleCover : doubleCoverSource ⟶ doubleCoverBase :=
  Spec.map (CommRingCat.ofHom
    (algebraMap doubleCoverBaseRing (doubleCoverBaseRing × doubleCoverBaseRing)))

/-- Inclusion of the first component of the double cover. -/
private abbrev firstComponent : doubleCoverBase ⟶ doubleCoverSource :=
  Spec.map (CommRingCat.ofHom (RingHom.fst doubleCoverBaseRing doubleCoverBaseRing))

/-- The origin `T = 0`, given by its evaluation-kernel prime ideal. -/
private def origin : PrimeSpectrum doubleCoverBaseRing :=
  ⟨RingHom.ker (Polynomial.evalRingHom (0 : ZMod 2)), RingHom.ker_isPrime _⟩

/-- The origin in the first component of the double cover. -/
private abbrev chosenPoint : doubleCoverSource := firstComponent origin

private instance origin_isMaximal : origin.asIdeal.IsMaximal := by
  exact RingHom.ker_isMaximal_of_surjective (Polynomial.evalRingHom (0 : ZMod 2))
    (fun a ↦ ⟨Polynomial.C a, by simp⟩)

private theorem origin_ideal :
    origin.asIdeal = Ideal.span {(Polynomial.X : doubleCoverBaseRing)} := by
  change RingHom.ker (Polynomial.evalRingHom (0 : ZMod 2)) = _
  simpa using Polynomial.ker_evalRingHom (0 : ZMod 2)

private instance diagonalDoubleCover_isFinite : IsFinite diagonalDoubleCover := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

private instance diagonalDoubleCover_flat : Flat diagonalDoubleCover := by
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

private instance diagonalDoubleCover_locallyQuasiFinite :
    LocallyQuasiFinite diagonalDoubleCover := inferInstance

/-- The first projection is localization at the idempotent `(1, 0)`.
This is the stock component-open-immersion construction. -/
private instance firstComponent_isOpenImmersion : IsOpenImmersion firstComponent := by
  let := (RingHom.fst doubleCoverBaseRing doubleCoverBaseRing).toAlgebra
  exact IsOpenImmersion.of_isLocalization (1, 0)

private theorem chosenPoint_closed : IsClosed ({chosenPoint} : Set doubleCoverSource) := by
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
  change (origin.asIdeal.comap (RingHom.fst doubleCoverBaseRing doubleCoverBaseRing)).IsMaximal
  exact Ideal.comap_isMaximal_of_surjective _ Prod.fst_surjective

private theorem chosenPoint_image : diagonalDoubleCover chosenPoint = origin := by
  apply PrimeSpectrum.ext
  ext p
  change Polynomial.eval 0
    ((algebraMap doubleCoverBaseRing (doubleCoverBaseRing × doubleCoverBaseRing) p).1) = 0 ↔
      Polynomial.eval 0 p = 0
  simp

/-- Dimension one at the origin, using only its polynomial PID and localization description. -/
private theorem origin_stalk_dimension :
    ringKrullDim (doubleCoverBase.presheaf.stalk origin) = 1 := by
  calc
    _ = ringKrullDim (Localization.AtPrime origin.asIdeal) :=
      ringKrullDim_eq_of_ringEquiv
        (Spec.stalkIso (CommRingCat.of doubleCoverBaseRing) origin).commRingCatIsoToRingEquiv
    _ = origin.asIdeal.height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height origin.asIdeal
        (Localization.AtPrime origin.asIdeal)
    _ = 1 := by
      simp only [IsPrincipalIdealRing.height_eq_one_of_isMaximal origin.asIdeal
        (Polynomial.not_isField (ZMod 2)), WithBot.coe_one]

/-- The chosen full source stalk is a component stalk of the affine line.
This calculation is independent of dimension preservation. -/
private theorem chosenPoint_stalk_dimension :
    ringKrullDim (doubleCoverSource.presheaf.stalk chosenPoint) = 1 := by
  let : IsIso (firstComponent.stalkMap origin) :=
    ((IsOpenImmersion.iff_isIso_stalkMap (f := firstComponent)).mp
      firstComponent_isOpenImmersion).2 origin
  calc
    _ = ringKrullDim (doubleCoverBase.presheaf.stalk origin) :=
      ringKrullDim_eq_of_ringEquiv
        (asIso (firstComponent.stalkMap origin)).commRingCatIsoToRingEquiv
    _ = 1 := origin_stalk_dimension

/-- The diagonal double cover is finite flat, finite free of rank two and locally
quasi-finite, with a specified closed point over `T = 0`. Both full stalks at that point
have dimension one, not zero. The calculation is independent of dimension preservation. -/
private theorem diagonalDoubleCover_model :
    Module.Finite doubleCoverBaseRing (doubleCoverBaseRing × doubleCoverBaseRing) ∧
    Module.Free doubleCoverBaseRing (doubleCoverBaseRing × doubleCoverBaseRing) ∧
    Module.finrank doubleCoverBaseRing (doubleCoverBaseRing × doubleCoverBaseRing) = 2 ∧
    _root_.IsReduced (doubleCoverBaseRing × doubleCoverBaseRing) ∧
    IsFinite diagonalDoubleCover ∧ Flat diagonalDoubleCover ∧
    LocallyQuasiFinite diagonalDoubleCover ∧
    IsClosed ({chosenPoint} : Set doubleCoverSource) ∧
    diagonalDoubleCover chosenPoint = origin ∧
    origin.asIdeal = Ideal.span {(Polynomial.X : doubleCoverBaseRing)} ∧
    (diagonalDoubleCover.stalkMap chosenPoint).hom.Flat ∧
    diagonalDoubleCover.QuasiFiniteAt chosenPoint ∧
    ringKrullDim (doubleCoverSource.presheaf.stalk chosenPoint) = 1 ∧
    ringKrullDim (doubleCoverBase.presheaf.stalk (diagonalDoubleCover chosenPoint)) = 1 := by
  refine ⟨inferInstance, inferInstance, ?_, inferInstance, inferInstance, inferInstance,
    inferInstance, chosenPoint_closed, chosenPoint_image, origin_ideal,
    Flat.stalkMap diagonalDoubleCover chosenPoint,
    diagonalDoubleCover.quasiFiniteAt chosenPoint, chosenPoint_stalk_dimension, ?_⟩
  · simp
  · rw [chosenPoint_image]
    exact origin_stalk_dimension

/-- The specified closed-origin double-cover stalks have equal dimension by
pointwise flat quasi-finite dimension preservation. -/
theorem diagonalDoubleCover_stalk_dimension_eq :
    ringKrullDim (doubleCoverSource.presheaf.stalk chosenPoint) =
      ringKrullDim (doubleCoverBase.presheaf.stalk (diagonalDoubleCover chosenPoint)) := by
  exact diagonalDoubleCover.ringKrullDim_stalk_eq_of_flat_of_quasiFiniteAt chosenPoint
    (Flat.stalkMap diagonalDoubleCover chosenPoint)
    (diagonalDoubleCover.quasiFiniteAt chosenPoint)

end

end SchemePropertiesTest.FlatQuasiFinite
