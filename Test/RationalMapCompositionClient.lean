/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RationalMapComposition

/-! # Clients of relative partial/rational map composition -/

set_option warningAsError true

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y Z S : Scheme.{u}} [PreirreducibleSpace X] [Nonempty Y]
variable [X.Over S] [Y.Over S] [Z.Over S]

example (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    [f.IsOver S] [g.IsOver S] : (f.comp g).IsOver S :=
  PartialMap.isOver_comp_of_isDominant_first f g

example (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z)
    [f.IsOver S] [g.IsOver S] : (f.comp g).IsOver S :=
  RationalMap.isOver_comp_of_isDominant_first f g

example (f : X.PartialMap Y) [IsDominant f.hom] (h : Y ⟶ Z)
    [f.IsOver S] [h.IsOver S] :
    f.comp h.toPartialMap = f.compHom h ∧ (f.comp h.toPartialMap).IsOver S :=
  ⟨PartialMap.comp_toPartialMap f h, PartialMap.isOver_comp_of_isDominant_first f _⟩

example (f : X ⤏ Y) [f.IsDominant] (h : Y ⟶ Z)
    [f.IsOver S] [h.IsOver S] :
    f.comp h.toRationalMap = f.compHom h ∧ (f.comp h.toRationalMap).IsOver S :=
  ⟨RationalMap.comp_toRationalMap f h, RationalMap.isOver_comp_of_isDominant_first f _⟩

end AlgebraicGeometry.Scheme
