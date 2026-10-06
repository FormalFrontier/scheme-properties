/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenComposition

@[expose] public section

set_option warningAsError true

universe u

namespace SchemePropertiesTest.DenseOpenComposition

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

example (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) :
    (f.compOfPullsDenseOpens hf g).domain =
      f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain) :=
  rfl

example {f₁ f₂ : X.PartialMap Y}
    (hf₁ : f₁.PullsDenseOpens) (hf₂ : f₂.PullsDenseOpens)
    (h : f₁.equiv f₂) (g : Y.PartialMap Z) :
    (f₁.compOfPullsDenseOpens hf₁ g).toRationalMap =
      (f₂.compOfPullsDenseOpens hf₂ g).toRationalMap :=
  PartialMap.toRationalMap_eq_iff.mpr
    (PartialMap.compOfPullsDenseOpens_equiv_of_equiv_left hf₁ hf₂ h g)

example (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    {g₁ g₂ : Y.PartialMap Z} (h : g₁.equiv g₂) :
    (f.compOfPullsDenseOpens hf g₁).toRationalMap =
      (f.compOfPullsDenseOpens hf g₂).toRationalMap :=
  PartialMap.toRationalMap_eq_iff.mpr
    (PartialMap.compOfPullsDenseOpens_equiv_of_equiv_right f hf h)

example (f₁ f₂ : X.PartialMap Y)
    (hf₁ : f₁.PullsDenseOpens) (hf₂ : f₂.PullsDenseOpens)
    (h : f₁.equiv f₂) (g₁ g₂ : Y.PartialMap Z) (hg : g₁.equiv g₂) :
    (f₁.compOfPullsDenseOpens hf₁ g₁).toRationalMap =
      (f₂.compOfPullsDenseOpens hf₂ g₂).toRationalMap :=
  PartialMap.toRationalMap_eq_iff.mpr
    (PartialMap.compOfPullsDenseOpens_equiv_of_equiv f₁ f₂ hf₁ hf₂ h g₁ g₂ hg)

example (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) :
    f.toRationalMap.compOfPullsDenseOpens
        (f.pullsDenseOpens_toRationalMap_iff.mpr hf) g.toRationalMap =
      (f.compOfPullsDenseOpens hf g).toRationalMap :=
  RationalMap.toRationalMap_compOfPullsDenseOpens f hf g

example (f : X ⤏ Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) :
    f.compOfPullsDenseOpens hf g.toRationalMap =
      (f.representative.compOfPullsDenseOpens
        (f.pullsDenseOpens_representative_iff.mpr hf) g).toRationalMap :=
  RationalMap.compOfPullsDenseOpens_def f hf g

noncomputable example (f : X.PartialMap Y) (hOpen : IsOpenMap f.hom)
    (g : Y.PartialMap Z) : X.PartialMap Z :=
  f.compOfPullsDenseOpens (f.pullsDenseOpens_of_isOpenMap hOpen) g

example [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) :
    f.compOfPullsDenseOpens f.pullsDenseOpens_of_isDominant g = f.comp g :=
  f.compOfPullsDenseOpens_eq_comp f.pullsDenseOpens_of_isDominant g

example [PreirreducibleSpace X] [Nonempty Y]
    (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) :
    f.compOfPullsDenseOpens
        (f.pullsDenseOpens_representative_iff.mp
          f.representative.pullsDenseOpens_of_isDominant) g = f.comp g :=
  f.compOfPullsDenseOpens_eq_comp _ g

example (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y ⟶ Z) : f.compOfPullsDenseOpens hf g.toPartialMap = f.compHom g :=
  f.compOfPullsDenseOpens_toPartialMap hf g

example (f : X ⤏ Y) (hf : f.PullsDenseOpens)
    (g : Y ⟶ Z) : f.compOfPullsDenseOpens hf g.toRationalMap = f.compHom g :=
  f.compOfPullsDenseOpens_toRationalMap hf g

end SchemePropertiesTest.DenseOpenComposition
