/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.PowerImage
public import Mathlib.Data.ZMod.Basic

/-!
# The one-root cover over the zero ring

The single-cover construction remains faithfully flat and makes every unit a
positive power when the base ring is trivial.
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry

example :
    (powerImage (ZMod 1) 2).IsOneCoverDense (faithfullyFlatTestMorphisms (ZMod 1)) :=
  powerImage_isOneCoverDense (ZMod 1) 2 (by decide)

example :
    faithfullyFlatTestMorphisms (ZMod 1)
      (powerRootMap (ZMod 1) 2 (laurentTest (ZMod 1)) (laurentUnit (ZMod 1))).op :=
  powerRootMap_faithfullyFlat (ZMod 1) 2 (laurentTest (ZMod 1))
    (laurentUnit (ZMod 1)) (by decide)

end AlgebraicGeometry
