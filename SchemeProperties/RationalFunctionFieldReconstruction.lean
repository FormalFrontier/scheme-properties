/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RationalFunctionFieldFaithfulness

public section

/-!
# Reconstructing dominant rational maps from function-field homomorphisms

For integral schemes over chosen maps to a common base, a compatible homomorphism
of function fields determines a dominant rational map when the target structure
map is locally of finite type. The readback and uniqueness are statements about
native quotient rational maps, not particular representatives.
-/

set_option warningAsError true

open CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.RationalMap

variable {X Y S : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- A compatible reversed function-field homomorphism spreads out to a native
quotient rational map. Local finite type is required only of the target map. -/
noncomputable def ofFunctionFieldMap (sX : X ⟶ S) (sY : Y ⟶ S)
    [LocallyOfFiniteType sY] (φ : Y.functionField ⟶ X.functionField)
    (hφ : (Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y)) ≫ sY =
      X.fromSpecStalk (genericPoint X) ≫ sX) : X ⤏ Y :=
  ofFunctionField sX sY (Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y)) hφ

/-- The reconstructed quotient respects the independently chosen base arrows. -/
theorem ofFunctionFieldMap_compHom (sX : X ⟶ S) (sY : Y ⟶ S)
    [LocallyOfFiniteType sY] (φ : Y.functionField ⟶ X.functionField)
    (hφ : (Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y)) ≫ sY =
      X.fromSpecStalk (genericPoint X) ≫ sX) :
    (ofFunctionFieldMap sX sY φ hφ).compHom sY = sX.toRationalMap :=
  (equivFunctionField sX sY ⟨_, hφ⟩).property

private theorem fromFunctionField_total {T : Scheme.{u}} (f : Y ⟶ T) :
    f.toRationalMap.fromFunctionField = Y.fromSpecStalk (genericPoint Y) ≫ f := by
  change f.toPartialMap.fromSpecStalkOfMem _ = _
  exact PartialMap.fromSpecStalkOfMem_toPartialMap f _

private theorem fromFunctionField_id :
    (RationalMap.id Y).fromFunctionField = Y.fromSpecStalk (genericPoint Y) := by
  change ((𝟙 Y : Y ⟶ Y).toPartialMap).fromSpecStalkOfMem _ = _
  rw [PartialMap.fromSpecStalkOfMem_toPartialMap, Category.comp_id]

private theorem fromFunctionField_specMap (r : X ⤏ Y) [r.IsDominant] :
    r.fromFunctionField =
      Spec.map r.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y) := by
  calc
    r.fromFunctionField = (r.comp (RationalMap.id Y)).fromFunctionField := by
      rw [RationalMap.comp_id]
    _ = Spec.map r.functionFieldMap ≫ (RationalMap.id Y).fromFunctionField :=
      fromFunctionField_comp r (RationalMap.id Y)
    _ = Spec.map r.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y) := by
      rw [fromFunctionField_id]

/-- The spread-out quotient is dominant: its generic geometric image is the
target's generic point, before any dominant-only factorization is used. -/
theorem isDominant_ofFunctionFieldMap (sX : X ⟶ S) (sY : Y ⟶ S)
    [LocallyOfFiniteType sY] (φ : Y.functionField ⟶ X.functionField)
    (hφ : (Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y)) ≫ sY =
      X.fromSpecStalk (genericPoint X) ≫ sX) :
    (ofFunctionFieldMap sX sY φ hφ).IsDominant := by
  let p := PartialMap.ofFromSpecStalk sX sY
    (Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y)) hφ
  have hx : genericPoint X ∈ p.domain :=
    PartialMap.mem_domain_ofFromSpecStalk sX sY _ hφ
  have hsource : p.domain.fromSpecStalkOfMem (genericPoint X) hx
      (closedPoint X.functionField) = (⟨genericPoint X, hx⟩ : p.domain) := by
    apply Subtype.ext
    have heq := congrArg (fun f : Spec X.functionField ⟶ X =>
      f (closedPoint X.functionField))
      (p.domain.fromSpecStalkOfMem_ι (genericPoint X) hx)
    change p.domain.ι (p.domain.fromSpecStalkOfMem (genericPoint X) hx
      (closedPoint X.functionField)) =
        X.fromSpecStalk (genericPoint X) (closedPoint X.functionField) at heq
    rw [fromSpecStalk_closedPoint] at heq
    change p.domain.ι (p.domain.fromSpecStalkOfMem (genericPoint X) hx
      (closedPoint X.functionField)) = genericPoint X
    exact heq
  have htarget : (Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y))
      (closedPoint X.functionField) = genericPoint Y := by
    have hsub : Subsingleton (Spec Y.functionField) := by
      change Subsingleton (PrimeSpectrum Y.functionField)
      infer_instance
    have hpoint : Spec.map φ (closedPoint X.functionField) = closedPoint Y.functionField :=
      @Subsingleton.elim _ hsub _ _
    change Y.fromSpecStalk (genericPoint Y) (Spec.map φ (closedPoint X.functionField)) = _
    rw [hpoint, fromSpecStalk_closedPoint]
  have himage : p.hom (⟨genericPoint X, hx⟩ : p.domain) = genericPoint Y := by
    have heq := congrArg (fun f : Spec X.functionField ⟶ Y =>
      f (closedPoint X.functionField))
      (PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY _ hφ)
    change (p.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ p.hom)
      (closedPoint X.functionField) = _ at heq
    change p.hom (p.domain.fromSpecStalkOfMem (genericPoint X) hx
      (closedPoint X.functionField)) =
        (Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y))
          (closedPoint X.functionField) at heq
    rw [hsource, htarget] at heq
    exact heq
  have hdense : DenseRange p.hom := by
    apply (denseRange_iff_closure_range).2
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← (genericPoint_spec Y).def]
    apply closure_mono
    exact Set.singleton_subset_iff.mpr ⟨⟨genericPoint X, hx⟩, himage⟩
  exact (p.isDominant_toRationalMap_iff).2 ⟨hdense⟩

/-- Dominance can be inferred for the reconstructed quotient. -/
noncomputable instance ofFunctionFieldMap_isDominant (sX : X ⟶ S) (sY : Y ⟶ S)
    [LocallyOfFiniteType sY] (φ : Y.functionField ⟶ X.functionField)
    (hφ : (Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y)) ≫ sY =
      X.fromSpecStalk (genericPoint X) ≫ sX) :
    (ofFunctionFieldMap sX sY φ hφ).IsDominant :=
  isDominant_ofFunctionFieldMap sX sY φ hφ

/-- Pulling back along the constructed quotient recovers the original field homomorphism. -/
theorem functionFieldMap_ofFunctionFieldMap (sX : X ⟶ S) (sY : Y ⟶ S)
    [LocallyOfFiniteType sY] (φ : Y.functionField ⟶ X.functionField)
    (hφ : (Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y)) ≫ sY =
      X.fromSpecStalk (genericPoint X) ≫ sX) :
    (ofFunctionFieldMap sX sY φ hφ).functionFieldMap = φ := by
  apply Spec.map_injective
  rw [← cancel_mono (Y.fromSpecStalk (genericPoint Y))]
  calc
    Spec.map (ofFunctionFieldMap sX sY φ hφ).functionFieldMap ≫
        Y.fromSpecStalk (genericPoint Y) =
      (ofFunctionFieldMap sX sY φ hφ).fromFunctionField :=
        (fromFunctionField_specMap _).symm
    _ = Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y) :=
      fromFunctionField_ofFunctionField sX sY _ hφ

/-- A dominant quotient over chosen base arrows induces a compatible reversed
homomorphism on function fields; no local finite type hypothesis is needed. -/
theorem functionFieldMap_compatible (sX : X ⟶ S) (sY : Y ⟶ S)
    (r : X ⤏ Y) [r.IsDominant]
    (h : r.compHom sY = sX.toRationalMap) :
    (Spec.map r.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y)) ≫ sY =
      X.fromSpecStalk (genericPoint X) ≫ sX := by
  calc
    (Spec.map r.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y)) ≫ sY =
        Spec.map r.functionFieldMap ≫ sY.toRationalMap.fromFunctionField := by
          rw [fromFunctionField_total]
          simp only [Category.assoc]
    _ = (r.comp sY.toRationalMap).fromFunctionField :=
      (fromFunctionField_comp r sY.toRationalMap).symm
    _ = (r.compHom sY).fromFunctionField := by rw [comp_toRationalMap]
    _ = sX.toRationalMap.fromFunctionField := by rw [h]
    _ = X.fromSpecStalk (genericPoint X) ≫ sX := fromFunctionField_total sX

/-- Reconstruction is inverse on independently dominant quotients over the
chosen base arrows. -/
theorem ofFunctionFieldMap_functionFieldMap (sX : X ⟶ S) (sY : Y ⟶ S)
    [LocallyOfFiniteType sY] (r : X ⤏ Y) [r.IsDominant]
    (h : r.compHom sY = sX.toRationalMap) :
    ofFunctionFieldMap sX sY r.functionFieldMap (functionFieldMap_compatible sX sY r h) = r := by
  apply eq_of_fromFunctionField_eq
  rw [ofFunctionFieldMap, fromFunctionField_ofFunctionField]
  exact (fromFunctionField_specMap r).symm

end AlgebraicGeometry.Scheme.RationalMap
