/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.PullbackOpenImmersion

set_option warningAsError true

open AlgebraicGeometry
open AlgebraicGeometry.PullbackOpenImmersion

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

example (f : R →+* T) (g : S →+* T) :
    IsOpenImmersion (fstOpenMap f g) ∧ IsOpenImmersion (sndOpenMap f g) :=
  ⟨isOpenImmersion_fstOpenMap f g, isOpenImmersion_sndOpenMap f g⟩

example (f : R →+* T) (g : S →+* T) :
    Set.range (fstOpenMap f g) =
      (kernelComplement (f.pullbackSnd g) : Set (Spec (.of (f.pullback g)))) :=
  range_fstOpenMap f g

example (f : R →+* T) (g : S →+* T) :
    Disjoint (Set.range (fstOpenMap f g)) (Set.range (sndOpenMap f g)) ∧
    Set.range (fstOpenMap f g) ∪ Set.range (sndOpenMap f g) =
      (kernelComplement (toBase f g) : Set (Spec (.of (f.pullback g)))) :=
  ⟨disjoint_ranges f g, union_ranges f g⟩
