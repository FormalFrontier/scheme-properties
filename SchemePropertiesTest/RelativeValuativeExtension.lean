/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RelativeValuativeExtension
public import SchemePropertiesTest.DisconnectedNormalCurve
public import SchemePropertiesTest.ProjectiveLineCoordinates

/-!
# Relative extension on a disconnected arithmetic curve

The partial morphism `[1:(2,3)]` from `Spec (ℤ × ℤ)` to the whole projective line
has strict dense domain `D((2,3))`. Relative extension includes the omitted point
`(2)` on the first component, retains the original morphism on its whole domain,
and preserves its rational map. On the whole normal curve the unique extension
is the independently constructed morphism `[1:(2,3)]`.

The source geometry and the projective-line morphism are supplied by
`SchemePropertiesTest.DisconnectedNormalCurve` and
`SchemePropertiesTest.ProjectiveLineCoordinates`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace SchemePropertiesTest.DisconnectedNormalCurve

private theorem valuation_extension_at_omittedPoint :
    ∃ q : source.PartialMap ProjectiveLineCoordinates.target, omittedPoint ∈ q.domain ∧
      ∃ hD : partialMap.domain < q.domain,
        q.hom ≫ ProjectiveLineCoordinates.structureMap = q.domain.ι ≫ structureMap ∧
        source.homOfLE hD.le ≫ q.hom = partialMap.hom ∧
        q.toRationalMap = globalMap.toRationalMap ∧
        source.homOfLE (inf_le_left : partialMap.domain ⊓ q.domain ≤ partialMap.domain) ≫
            partialMap.hom =
          source.homOfLE (inf_le_right : partialMap.domain ⊓ q.domain ≤ q.domain) ≫ q.hom := by
  obtain ⟨q, hx, hD, hover, hread, hrat, hinter⟩ :=
    Scheme.PartialMap.exists_le_extension_of_valuationRing_stalk
      structureMap ProjectiveLineCoordinates.structureMap partialMap partialMap_over omittedPoint
  have hstrict : partialMap.domain < q.domain := by
    refine lt_iff_le_and_ne.mpr ⟨hD, ?_⟩
    intro heq
    exact omittedPoint_not_mem_restricted_domain globalMap (heq.symm ▸ hx)
  exact ⟨q, hx, hstrict, hover, hread,
    hrat.trans (restrictedMap_toRationalMap globalMap), hinter⟩

private theorem normal_extension_at_omittedPoint :
    ∃ q : source.PartialMap ProjectiveLineCoordinates.target, omittedPoint ∈ q.domain ∧
      ∃ hD : partialMap.domain ≤ q.domain,
        q.hom ≫ ProjectiveLineCoordinates.structureMap = q.domain.ι ≫ structureMap ∧
        source.homOfLE hD ≫ q.hom = partialMap.hom ∧
        q.toRationalMap = globalMap.toRationalMap ∧
        source.homOfLE (inf_le_left : partialMap.domain ⊓ q.domain ≤ partialMap.domain) ≫
            partialMap.hom =
          source.homOfLE (inf_le_right : partialMap.domain ⊓ q.domain ≤ q.domain) ≫ q.hom := by
  obtain ⟨q, hx, hD, hover, hread, hrat, hinter⟩ :=
    Scheme.PartialMap.exists_le_extension_of_coheight_le_one
      structureMap ProjectiveLineCoordinates.structureMap partialMap partialMap_over
      omittedPoint omittedPoint_coheight.le
  exact ⟨q, hx, hD, hover, hread,
    hrat.trans (restrictedMap_toRationalMap globalMap), hinter⟩

private theorem omittedPoint_mem_rational_domain :
    omittedPoint ∈ partialMap.toRationalMap.domain ∧ omittedPoint ∉ partialMap.domain := by
  exact ⟨Scheme.PartialMap.mem_domain_toRationalMap_of_coheight_le_one
    structureMap ProjectiveLineCoordinates.structureMap partialMap partialMap_over
    omittedPoint omittedPoint_coheight.le, omittedPoint_not_mem_restricted_domain globalMap⟩

private theorem globalMap_extension_iff (h : source ⟶ ProjectiveLineCoordinates.target) :
    (h ≫ ProjectiveLineCoordinates.structureMap = structureMap ∧
      partialMap.domain.ι ≫ h = partialMap.hom) ↔ h = globalMap := by
  obtain ⟨g, _, huniq⟩ := Scheme.PartialMap.existsUnique_extension_of_krullDimLE_one
    structureMap ProjectiveLineCoordinates.structureMap partialMap partialMap_over
  have hglobal : globalMap ≫ ProjectiveLineCoordinates.structureMap = structureMap ∧
      partialMap.domain.ι ≫ globalMap = partialMap.hom :=
    ⟨globalMap_over, (restrictedMap_hom globalMap).symm⟩
  constructor
  · intro hh
    exact (huniq h hh).trans (huniq globalMap hglobal).symm
  · rintro rfl
    exact hglobal

private theorem rational_domain_eq_top : partialMap.toRationalMap.domain = ⊤ := by
  letI : source.Over base := .ofHom structureMap
  letI : ProjectiveLineCoordinates.target.Over base :=
    .ofHom ProjectiveLineCoordinates.structureMap
  letI : IsProper (ProjectiveLineCoordinates.target ↘ base) := by
    change IsProper ProjectiveLineCoordinates.structureMap
    infer_instance
  letI : partialMap.IsOver base := Scheme.PartialMap.isOver_iff.mpr partialMap_over
  letI : partialMap.toRationalMap.IsOver base := ⟨partialMap, inferInstance, rfl⟩
  apply top_unique
  intro x _
  exact Scheme.RationalMap.mem_domain_of_coheight_le_one
    (S := base) partialMap.toRationalMap x (coheight_le_one x)

end SchemePropertiesTest.DisconnectedNormalCurve
