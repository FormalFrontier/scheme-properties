/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenCompositionClosure

@[expose] public section

set_option warningAsError true

universe u

namespace SchemePropertiesTest.DenseOpenCompositionClosure

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {X Y Z T : Scheme.{u}}

private theorem arbitraryPartial (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) (hg : g.PullsDenseOpens) :
    (f.compOfPullsDenseOpens hf g).PullsDenseOpens :=
  f.pullsDenseOpens_compOfPullsDenseOpens hf g hg

private theorem arbitraryRational (f : X ⤏ Y) (hf : f.PullsDenseOpens)
    (g : Y ⤏ Z) (hg : g.PullsDenseOpens) :
    (f.compOfPullsDenseOpens hf g).PullsDenseOpens :=
  f.pullsDenseOpens_compOfPullsDenseOpens hf g hg

private theorem representativeTransfer (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) (hg : g.PullsDenseOpens) :
    ((f.compOfPullsDenseOpens hf g).toRationalMap).PullsDenseOpens :=
  (f.compOfPullsDenseOpens hf g).pullsDenseOpens_toRationalMap_iff.mpr
    (f.pullsDenseOpens_compOfPullsDenseOpens hf g hg)

private theorem chosenRepresentatives (f : X ⤏ Y) (hf : f.PullsDenseOpens)
    (g : Y ⤏ Z) (hg : g.PullsDenseOpens) :
    ((f.representative.compOfPullsDenseOpens
      (f.pullsDenseOpens_representative_iff.mpr hf) g.representative).toRationalMap).PullsDenseOpens :=
  representativeTransfer f.representative
    (f.pullsDenseOpens_representative_iff.mpr hf) g.representative
    (g.pullsDenseOpens_representative_iff.mpr hg)

private theorem openMaps (f : X.PartialMap Y) (hf : IsOpenMap f.hom)
    (g : Y.PartialMap Z) (hg : IsOpenMap g.hom) :
    (f.compOfPullsDenseOpens (f.pullsDenseOpens_of_isOpenMap hf) g).PullsDenseOpens :=
  f.pullsDenseOpens_compOfPullsDenseOpens (f.pullsDenseOpens_of_isOpenMap hf) g
    (g.pullsDenseOpens_of_isOpenMap hg)

private noncomputable def reuseFirstPremise (f : X.PartialMap Y) (hf : f.PullsDenseOpens)
    (g : Y.PartialMap Z) (hg : g.PullsDenseOpens)
    (h : Z.PartialMap T) : X.PartialMap T :=
  (f.compOfPullsDenseOpens hf g).compOfPullsDenseOpens
    (f.pullsDenseOpens_compOfPullsDenseOpens hf g hg) h

end SchemePropertiesTest.DenseOpenCompositionClosure
