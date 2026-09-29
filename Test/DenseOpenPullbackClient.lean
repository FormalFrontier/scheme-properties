/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenPullback

@[expose] public section

set_option warningAsError true

universe u

namespace SchemePropertiesTest.DenseOpenPullback

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

example (f g : X.PartialMap Y) (h : f.equiv g) :
    f.PullsDenseOpens ↔ g.PullsDenseOpens :=
  PartialMap.pullsDenseOpens_iff_of_equiv f g h

example (f : X.PartialMap Y) (W : X.Opens)
    (hW : Dense (W : Set X)) (hWf : W ≤ f.domain) :
    (f.restrict W hW hWf).PullsDenseOpens ↔ f.PullsDenseOpens :=
  f.pullsDenseOpens_restrict_iff W hW hWf

example (f : X.PartialMap Y) (W : X.Opens)
    (hW : Dense (W : Set X)) (hWf : W ≤ f.domain) :
    (f.restrict W hW hWf).toRationalMap.PullsDenseOpens ↔ f.PullsDenseOpens := by
  rw [f.restrict_toRationalMap W hW hWf, f.pullsDenseOpens_toRationalMap_iff]

example (f : X.PartialMap Y) :
    f.toRationalMap.PullsDenseOpens ↔ f.PullsDenseOpens :=
  f.pullsDenseOpens_toRationalMap_iff

example (r : X ⤏ Y) :
    r.PullsDenseOpens ↔ r.representative.PullsDenseOpens :=
  r.pullsDenseOpens_representative_iff.symm

example (f : X.PartialMap Y) (hf : IsOpenMap f.hom) :
    f.toRationalMap.PullsDenseOpens :=
  f.pullsDenseOpens_toRationalMap_iff.mpr (f.pullsDenseOpens_of_isOpenMap hf)

example [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] :
    f.toRationalMap.PullsDenseOpens :=
  f.pullsDenseOpens_toRationalMap_iff.mpr f.pullsDenseOpens_of_isDominant

end SchemePropertiesTest.DenseOpenPullback
