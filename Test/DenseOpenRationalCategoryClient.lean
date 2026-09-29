/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenRationalCategory

@[expose] public section

set_option warningAsError true

universe u

namespace SchemePropertiesTest.DenseOpenRationalCategory

open AlgebraicGeometry AlgebraicGeometry.DenseOpenRationalScheme CategoryTheory

private theorem objectConstructor (X : Scheme.{u}) :
    (DenseOpenRationalScheme.of X).toScheme = X := rfl

variable {X Y Z T : DenseOpenRationalScheme.{u}}

private theorem arrowConstructor (r : X.toScheme ⤏ Y.toScheme)
    (hr : r.PullsDenseOpens) : (hom r hr).toRationalMap = r :=
  toRationalMap_hom r hr

private theorem arrowExtensionality (f g : X ⟶ Y)
    (h : f.toRationalMap = g.toRationalMap) : f = g := hom_ext h

private theorem leftIdentity (f : X ⟶ Y) : 𝟙 X ≫ f = f := CategoryTheory.Category.id_comp f
private theorem rightIdentity (f : X ⟶ Y) : f ≫ 𝟙 Y = f := CategoryTheory.Category.comp_id f

private theorem associativity (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := CategoryTheory.Category.assoc f g h

private theorem identityProjection (X : DenseOpenRationalScheme.{u}) :
    (𝟙 X : X ⟶ X).toRationalMap = Scheme.RationalMap.id X.toScheme :=
  toRationalMap_id X

private theorem compositionProjection (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRationalMap =
      f.toRationalMap.compOfPullsDenseOpens f.pullsDenseOpens g.toRationalMap :=
  toRationalMap_comp f g

private theorem boundedDominance [PreirreducibleSpace X.toScheme] [Nonempty X.toScheme]
    [PreirreducibleSpace Y.toScheme] [Nonempty Y.toScheme]
    (r : X.toScheme ⤏ Y.toScheme) (hr : r.IsDominant) :
    ((homEquivDominant X Y).symm ⟨r, hr⟩).toRationalMap = r := rfl

private theorem dominanceProjection [PreirreducibleSpace X.toScheme]
    [Nonempty X.toScheme] [PreirreducibleSpace Y.toScheme] [Nonempty Y.toScheme]
    (f : X ⟶ Y) : (homEquivDominant X Y f).1 = f.toRationalMap :=
  homEquivDominant_apply_val X Y f

end SchemePropertiesTest.DenseOpenRationalCategory
