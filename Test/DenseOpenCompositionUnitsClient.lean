/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.DenseOpenCompositionUnits

@[expose] public section

set_option warningAsError true

universe u

namespace SchemePropertiesTest.DenseOpenCompositionUnits

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

private theorem partialIdentity (X : Scheme.{u}) :
    (PartialMap.id X).PullsDenseOpens := PartialMap.pullsDenseOpens_id X

private theorem rationalIdentity (X : Scheme.{u}) :
    (RationalMap.id X).PullsDenseOpens := RationalMap.pullsDenseOpens_id X

private theorem partialLeft (f : X.PartialMap Y) :
    (PartialMap.id X).compOfPullsDenseOpens (PartialMap.pullsDenseOpens_id X) f = f :=
  PartialMap.id_compOfPullsDenseOpens f

private theorem rationalLeft (r : X ⤏ Y) :
    (RationalMap.id X).compOfPullsDenseOpens (RationalMap.pullsDenseOpens_id X) r = r :=
  RationalMap.id_compOfPullsDenseOpens r

private theorem partialRight (f : X.PartialMap Y) (hf : f.PullsDenseOpens) :
    f.compOfPullsDenseOpens hf (PartialMap.id Y) = f :=
  PartialMap.compOfPullsDenseOpens_id f hf

private theorem rationalRight (r : X ⤏ Y) (hr : r.PullsDenseOpens) :
    r.compOfPullsDenseOpens hr (RationalMap.id Y) = r :=
  RationalMap.compOfPullsDenseOpens_id r hr

private theorem rationalLeftRepresentative (f : X.PartialMap Y) :
    (RationalMap.id X).compOfPullsDenseOpens (RationalMap.pullsDenseOpens_id X)
      f.toRationalMap = f.toRationalMap :=
  RationalMap.id_compOfPullsDenseOpens f.toRationalMap

private theorem rationalRightRepresentative (f : X.PartialMap Y) (hf : f.PullsDenseOpens) :
    f.toRationalMap.compOfPullsDenseOpens
      (f.pullsDenseOpens_toRationalMap_iff.mpr hf) (RationalMap.id Y) = f.toRationalMap :=
  RationalMap.compOfPullsDenseOpens_id _ _

end SchemePropertiesTest.DenseOpenCompositionUnits
