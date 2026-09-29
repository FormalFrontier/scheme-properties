/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenPullbackDominance

@[expose] public section

set_option warningAsError true

universe u

namespace SchemePropertiesTest.DenseOpenPullbackDominance

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

private example [Nonempty X] [PreirreducibleSpace Y] (f : X.PartialMap Y)
    (hf : f.PullsDenseOpens) : IsDominant f.hom :=
  f.isDominant_of_pullsDenseOpens hf

private example [Nonempty X] [PreirreducibleSpace Y] (r : X ⤏ Y)
    (hr : r.PullsDenseOpens) : r.IsDominant :=
  r.isDominant_of_pullsDenseOpens hr

private example [PreirreducibleSpace X] [Nonempty X]
    [PreirreducibleSpace Y] [Nonempty Y] (f : X.PartialMap Y) :
    f.PullsDenseOpens ↔ IsDominant f.hom :=
  f.pullsDenseOpens_iff_isDominant

private example [PreirreducibleSpace X] [Nonempty X]
    [PreirreducibleSpace Y] [Nonempty Y] (r : X ⤏ Y) :
    r.PullsDenseOpens ↔ r.IsDominant :=
  r.pullsDenseOpens_iff_isDominant

end SchemePropertiesTest.DenseOpenPullbackDominance
