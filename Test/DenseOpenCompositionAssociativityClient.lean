/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenCompositionAssociativity

@[expose] public section

set_option warningAsError true

universe u

namespace SchemePropertiesTest.DenseOpenCompositionAssociativity

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {X Y Z T : Scheme.{u}}

private theorem arbitraryPartial (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) (hg : g.PullsDenseOpens) (h : Z.PartialMap T) :
    (f.compOfPullsDenseOpens hf g).compOfPullsDenseOpens
      (f.pullsDenseOpens_compOfPullsDenseOpens hf g hg) h =
      f.compOfPullsDenseOpens hf (g.compOfPullsDenseOpens hg h) :=
  f.compOfPullsDenseOpens_assoc hf g hg h

private theorem arbitraryRational (r : X ⤏ Y) (hr : r.PullsDenseOpens)
    (s : Y ⤏ Z) (hs : s.PullsDenseOpens) (t : Z ⤏ T) :
    (r.compOfPullsDenseOpens hr s).compOfPullsDenseOpens
      (r.pullsDenseOpens_compOfPullsDenseOpens hr s hs) t =
      r.compOfPullsDenseOpens hr (s.compOfPullsDenseOpens hs t) :=
  r.compOfPullsDenseOpens_assoc hr s hs t

private theorem representativeInstance (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) (hg : g.PullsDenseOpens) (h : Z.PartialMap T) :
    (f.toRationalMap.compOfPullsDenseOpens
      (f.pullsDenseOpens_toRationalMap_iff.mpr hf) g.toRationalMap).compOfPullsDenseOpens
        (f.toRationalMap.pullsDenseOpens_compOfPullsDenseOpens
          (f.pullsDenseOpens_toRationalMap_iff.mpr hf) g.toRationalMap
          (g.pullsDenseOpens_toRationalMap_iff.mpr hg)) h.toRationalMap =
      f.toRationalMap.compOfPullsDenseOpens
        (f.pullsDenseOpens_toRationalMap_iff.mpr hf)
        (g.toRationalMap.compOfPullsDenseOpens
          (g.pullsDenseOpens_toRationalMap_iff.mpr hg) h.toRationalMap) :=
  f.toRationalMap.compOfPullsDenseOpens_assoc
    (f.pullsDenseOpens_toRationalMap_iff.mpr hf) g.toRationalMap
    (g.pullsDenseOpens_toRationalMap_iff.mpr hg) h.toRationalMap

private noncomputable def iteratedPartial (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) (hg : g.PullsDenseOpens) (h : Z.PartialMap T) : X.PartialMap T :=
  (f.compOfPullsDenseOpens hf g).compOfPullsDenseOpens
    (f.pullsDenseOpens_compOfPullsDenseOpens hf g hg) h

private theorem iteratedPartial_right (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) (hg : g.PullsDenseOpens) (h : Z.PartialMap T) :
    iteratedPartial f hf g hg h =
      f.compOfPullsDenseOpens hf (g.compOfPullsDenseOpens hg h) :=
  f.compOfPullsDenseOpens_assoc hf g hg h

end SchemePropertiesTest.DenseOpenCompositionAssociativity
