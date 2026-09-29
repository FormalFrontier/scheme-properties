/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents (Hive Task hive-request-5661a06674dafb5829660f4b9a743ffdb93c3d80,
  UID 1d6aee74-dee3-48bc-829f-fb75f94fb841)
-/
module

public import SchemeProperties.DenseOpenCompositionOver

@[expose] public section

set_option warningAsError true

universe u

namespace SchemePropertiesTest.DenseOpenCompositionOver

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {X Y Z S : Scheme.{u}} [X.Over S] [Y.Over S] [Z.Over S]

private theorem partialOver (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) [f.IsOver S] [g.IsOver S] :
    (f.compOfPullsDenseOpens hf g).IsOver S :=
  PartialMap.isOver_compOfPullsDenseOpens f hf g

private theorem rationalOver (f : X ⤏ Y) (hf : f.PullsDenseOpens)
    (g : Y ⤏ Z) [f.IsOver S] [g.IsOver S] :
    (f.compOfPullsDenseOpens hf g).IsOver S :=
  RationalMap.isOver_compOfPullsDenseOpens f hf g

private theorem quotientOver (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) [f.IsOver S] [g.IsOver S] :
    (f.toRationalMap.compOfPullsDenseOpens
      (f.pullsDenseOpens_toRationalMap_iff.mpr hf) g.toRationalMap).IsOver S :=
  RationalMap.isOver_compOfPullsDenseOpens _ _ _

private theorem openFirstOver (f : X.PartialMap Y) (hOpen : IsOpenMap f.hom)
    (g : Y.PartialMap Z) [f.IsOver S] [g.IsOver S] :
    (f.compOfPullsDenseOpens (f.pullsDenseOpens_of_isOpenMap hOpen) g).IsOver S :=
  PartialMap.isOver_compOfPullsDenseOpens _ _ _

private theorem totalSecondOver (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y ⟶ Z) [f.IsOver S] [g.IsOver S] :
    (f.compHom g).IsOver S := by
  rw [← f.compOfPullsDenseOpens_toPartialMap hf g]
  exact PartialMap.isOver_compOfPullsDenseOpens f hf g.toPartialMap

end SchemePropertiesTest.DenseOpenCompositionOver
