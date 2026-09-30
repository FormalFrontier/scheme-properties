/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.RationalFunctionFieldInverse

set_option warningAsError true

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace SchemePropertiesTest.RationalFunctionFieldInverse

private theorem chosen_base_inverse_laws {X Y S : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (sX : X ⟶ S) (sY : Y ⟶ S)
    [LocallyOfFiniteType sX]
    (f : IntegralDominantRationalSchemeOver.of sX ⟶
      IntegralDominantRationalSchemeOver.of sY)
    [IsIso f.toRationalMap.functionFieldMap] :
    ∃ g : IntegralDominantRationalSchemeOver.of sY ⟶
      IntegralDominantRationalSchemeOver.of sX,
      f ≫ g = 𝟙 _ ∧ g ≫ f = 𝟙 _ := by
  have hsource : LocallyOfFiniteType
      (IntegralDominantRationalSchemeOver.of sX).toBase := by
    change LocallyOfFiniteType sX
    infer_instance
  exact ((@IntegralDominantRationalSchemeOver.isIso_iff_isIso_functionFieldMap
    _ _ _ f hsource).2 inferInstance).out

private theorem chosen_base_converse_without_finiteness {X Y S : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (sX : X ⟶ S) (sY : Y ⟶ S)
    (f : IntegralDominantRationalSchemeOver.of sX ⟶
      IntegralDominantRationalSchemeOver.of sY) [IsIso f] :
    IsIso f.toRationalMap.functionFieldMap :=
  IntegralDominantRationalSchemeOver.isIso_functionFieldMap f

private theorem chosen_base_native_quotient {X Y S : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (sX : X ⟶ S) (sY : Y ⟶ S)
    [LocallyOfFiniteType sX]
    (r : X ⤏ Y) [hrdominant : r.IsDominant]
    (hr : r.compHom sY = sX.toRationalMap)
    [IsIso r.functionFieldMap] :
    ∃ g : IntegralDominantRationalSchemeOver.of sY ⟶
      IntegralDominantRationalSchemeOver.of sX,
      g.toRationalMap.compHom sX = sY.toRationalMap ∧
      r.comp g.toRationalMap = Scheme.RationalMap.id X ∧
      g.toRationalMap.comp r = Scheme.RationalMap.id Y := by
  have hbase : r.compHom (IntegralDominantRationalSchemeOver.of sY).toBase =
      (IntegralDominantRationalSchemeOver.of sX).toBase.toRationalMap := by
    change r.compHom sY = sX.toRationalMap
    exact hr
  let f : IntegralDominantRationalSchemeOver.of sX ⟶
      IntegralDominantRationalSchemeOver.of sY :=
    IntegralDominantRationalSchemeOver.hom r hrdominant
      ((IntegralDominantRationalSchemeOver.isOver_iff_compHom
        (X := .of sX) (Y := .of sY) (r := r)).mpr hbase)
  have hfield : IsIso f.toRationalMap.functionFieldMap := by
    change IsIso r.functionFieldMap
    infer_instance
  obtain ⟨g, hfg, hgf⟩ := chosen_base_inverse_laws sX sY f
  refine ⟨g, ?_, ?_, ?_⟩
  · exact IntegralDominantRationalSchemeOver.isOver_iff_compHom.mp g.isOver
  · have h := congrArg (fun h : IntegralDominantRationalSchemeOver.of sX ⟶
        IntegralDominantRationalSchemeOver.of sX => h.toRationalMap) hfg
    simp only [IntegralDominantRationalSchemeOver.toRationalMap_comp,
      IntegralDominantRationalSchemeOver.toRationalMap_id] at h
    change r.comp g.toRationalMap = Scheme.RationalMap.id X at h
    exact h
  · have h := congrArg (fun h : IntegralDominantRationalSchemeOver.of sY ⟶
        IntegralDominantRationalSchemeOver.of sY => h.toRationalMap) hgf
    simp only [IntegralDominantRationalSchemeOver.toRationalMap_comp,
      IntegralDominantRationalSchemeOver.toRationalMap_id] at h
    change g.toRationalMap.comp r = Scheme.RationalMap.id Y at h
    exact h

end SchemePropertiesTest.RationalFunctionFieldInverse
