/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RationalFunctionFieldReconstruction
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

public section

/-!
# The generic-point inclusion and its function-field map

The canonical morphism from the spectrum of an integral scheme's function field
is dominant and induces an isomorphism on function fields, although it need not
be locally of finite type. The latter obstruction persists after composition
with any independently chosen structure morphism.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{u}) [IsIntegral Y]

/-- The generic-point morphism is dominant, without any finite-type hypothesis. -/
instance fromSpecStalk_genericPoint_isDominant :
    IsDominant (Y.fromSpecStalk (genericPoint Y)) := by
  rw [isDominant_iff, denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← genericPoint_closure (α := Y)]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨closedPoint Y.functionField,
    Y.fromSpecStalk_closedPoint⟩)

/-- The native rational quotient of the generic-point morphism is dominant. -/
instance fromSpecStalk_genericPoint_toRationalMap_isDominant :
    (Y.fromSpecStalk (genericPoint Y)).toRationalMap.IsDominant := by
  infer_instance

/-- The actual reversed field map of the generic-point rational quotient,
read back on spectra, is the canonical stalk map of the field spectrum. -/
theorem genericPoint_functionFieldMap_specMap :
    Spec.map (Y.fromSpecStalk (genericPoint Y)).toRationalMap.functionFieldMap =
      (Spec Y.functionField).fromSpecStalk (genericPoint (Spec Y.functionField)) := by
  have h := RationalMap.functionFieldMap_compatible
    (Y.fromSpecStalk (genericPoint Y)) (𝟙 Y)
    (Y.fromSpecStalk (genericPoint Y)).toRationalMap (by
      change ((Y.fromSpecStalk (genericPoint Y)).toPartialMap.compHom (𝟙 Y)).toRationalMap = _
      rw [PartialMap.compHom_id])
  have hcompat :
      Spec.map (Y.fromSpecStalk (genericPoint Y)).toRationalMap.functionFieldMap ≫
        Y.fromSpecStalk (genericPoint Y) =
      (Spec Y.functionField).fromSpecStalk (genericPoint (Spec Y.functionField)) ≫
        Y.fromSpecStalk (genericPoint Y) := by
    simpa only [Category.comp_id, Category.id_comp] using h
  rw [← cancel_mono (Y.fromSpecStalk (genericPoint Y))]
  exact hcompat

/-- The actual native reversed function-field map is an isomorphism. -/
instance genericPoint_functionFieldMap_isIso :
    IsIso (Y.fromSpecStalk (genericPoint Y)).toRationalMap.functionFieldMap := by
  have hspec : IsIso
      (Spec.map (Y.fromSpecStalk (genericPoint Y)).toRationalMap.functionFieldMap) := by
    rw [genericPoint_functionFieldMap_specMap]
    have hpoint : genericPoint (Spec Y.functionField) = closedPoint Y.functionField := by
      have : Subsingleton (Spec Y.functionField) := by
        change Subsingleton (PrimeSpectrum Y.functionField)
        infer_instance
      exact Subsingleton.elim _ _
    have hstalkClosed : IsIso
        ((Spec Y.functionField).fromSpecStalk (closedPoint Y.functionField)) := by
      rw [← Spec_stalkClosedPointIso]
      infer_instance
    rw [← hpoint] at hstalkClosed
    exact hstalkClosed
  have hopp : IsIso
      (Y.fromSpecStalk (genericPoint Y)).toRationalMap.functionFieldMap.op := by
    exact @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
      Spec.fullyFaithful _ _ _ hspec
  exact (isIso_op_iff _).mp hopp

/-- A nontrivial integral Jacobson scheme cannot receive its generic-point
field spectrum by a locally finite-type morphism. -/
theorem not_locallyOfFiniteType_fromSpecStalk_genericPoint
    [JacobsonSpace Y] [Nontrivial Y] :
    ¬ LocallyOfFiniteType (Y.fromSpecStalk (genericPoint Y)) := by
  intro hfinite
  have hclosed : IsClosed ({genericPoint Y} : Set Y) := by
    have hsource : closedPoint Y.functionField ∈ closedPoints (Spec Y.functionField) :=
      IsLocalRing.isClosed_singleton_closedPoint Y.functionField
    have himage := (Y.fromSpecStalk (genericPoint Y)).closePoints_subset_preimage_closedPoints
      hsource
    change IsClosed
      {(Y.fromSpecStalk (genericPoint Y)) (closedPoint Y.functionField)} at himage
    simpa only [fromSpecStalk_closedPoint] using himage
  have hsingleton : ({genericPoint Y} : Set Y) = Set.univ := by
    simpa only [hclosed.closure_eq] using (genericPoint_closure (α := Y))
  have hsub : Subsingleton Y := ⟨fun a b => by
    have ha : a = genericPoint Y := (Set.mem_singleton_iff.mp (hsingleton.symm ▸ Set.mem_univ a))
    have hb : b = genericPoint Y := (Set.mem_singleton_iff.mp (hsingleton.symm ▸ Set.mem_univ b))
    exact ha.trans hb.symm⟩
  exact not_subsingleton Y hsub

/-- The obstruction holds relative to every choice of a target structure map. -/
theorem not_locallyOfFiniteType_fromSpecStalk_genericPoint_comp
    [JacobsonSpace Y] [Nontrivial Y] {S : Scheme.{u}} (sY : Y ⟶ S) :
    ¬ LocallyOfFiniteType (Y.fromSpecStalk (genericPoint Y) ≫ sY) := by
  intro hfinite
  exact (not_locallyOfFiniteType_fromSpecStalk_genericPoint Y)
    (locallyOfFiniteType_of_comp _ sY)

end AlgebraicGeometry.Scheme
