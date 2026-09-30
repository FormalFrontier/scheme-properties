/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RationalMapPartialIso

public section

set_option warningAsError true

universe u

open CategoryTheory AlgebraicGeometry

namespace SchemePropertiesTest.RationalMapPartialIso

private theorem exact_inverse_client {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (forward : X ⤏ Y) (reverse : Y ⤏ X)
    [forward.IsDominant] [reverse.IsDominant]
    (hforward : forward.comp reverse = Scheme.RationalMap.id X)
    (hreverse : reverse.comp forward = Scheme.RationalMap.id Y) :
    ∃ partialIso : X.PartialIso Y,
      partialIso.toRationalMap = forward ∧ partialIso.symm.toRationalMap = reverse :=
  Scheme.RationalMap.exists_partialIso_of_inverse forward reverse hforward hreverse

private theorem chosen_base_client {X Y S : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (sourceMap : X ⟶ S) (targetMap : Y ⟶ S)
    (forward : X ⤏ Y) (reverse : Y ⤏ X)
    [forward.IsDominant] [reverse.IsDominant]
    (hforward : forward.comp reverse = Scheme.RationalMap.id X)
    (hreverse : reverse.comp forward = Scheme.RationalMap.id Y)
    (hbase : forward.compHom targetMap = sourceMap.toRationalMap) :
    ∃ partialIso : X.PartialIso Y,
      partialIso.toRationalMap = forward ∧
      partialIso.symm.toRationalMap = reverse ∧
      partialIso.IsOver sourceMap targetMap :=
  Scheme.RationalMap.exists_partialIso_of_inverse_over
    sourceMap targetMap forward reverse hforward hreverse hbase

private theorem same_carrier_client {X S : Scheme.{u}} [IsIntegral X]
    (sourceMap targetMap : X ⟶ S)
    (hbase : (Scheme.RationalMap.id X).compHom targetMap = sourceMap.toRationalMap) :
    ∃ partialIso : X.PartialIso X,
      partialIso.toRationalMap = Scheme.RationalMap.id X ∧
      partialIso.symm.toRationalMap = Scheme.RationalMap.id X ∧
      partialIso.IsOver sourceMap targetMap := by
  apply Scheme.RationalMap.exists_partialIso_of_inverse_over
    sourceMap targetMap (Scheme.RationalMap.id X) (Scheme.RationalMap.id X)
  · simp
  · simp
  · exact hbase

private theorem converse_client {X Y S : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (sourceMap : X ⟶ S) (targetMap : Y ⟶ S)
    (partialIso : X.PartialIso Y) (hover : partialIso.IsOver sourceMap targetMap) :
    partialIso.toRationalMap.IsDominant ∧
      partialIso.symm.toRationalMap.IsDominant ∧
      partialIso.toRationalMap.comp partialIso.symm.toRationalMap =
        Scheme.RationalMap.id X ∧
      partialIso.symm.toRationalMap.comp partialIso.toRationalMap =
        Scheme.RationalMap.id Y ∧
      partialIso.toRationalMap.compHom targetMap = sourceMap.toRationalMap ∧
      partialIso.symm.toRationalMap.compHom sourceMap = targetMap.toRationalMap :=
  ⟨inferInstance, inferInstance, partialIso.toRationalMap_comp_symm,
    partialIso.symm_toRationalMap_comp,
    partialIso.toRationalMap_compHom_of_isOver sourceMap targetMap hover,
    partialIso.symm_toRationalMap_compHom_of_isOver sourceMap targetMap hover⟩

end SchemePropertiesTest.RationalMapPartialIso
