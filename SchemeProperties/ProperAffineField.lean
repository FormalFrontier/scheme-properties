/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Points of proper affine schemes over a field

A preconnected scheme admitting a locally quasi-finite morphism to a totally disconnected scheme
has at most one point. In particular, a proper affine preconnected scheme over a field has at most
one point. Preconnectedness weakens the preirreducibility hypothesis: neither nonemptiness nor
reducedness is required.

These are statements about underlying topological points, not isomorphisms of schemes or
identifications of their rings of global sections. For example, the spectrum of the dual numbers
over a field is connected, finite and nonreduced. Preconnectedness cannot be omitted, as the
spectrum of a product of two copies of the field shows.

## References

The route uses Mathlib's finite/proper/affine morphism results of Christian Merten and Andrew
Yang, Andrew Yang's locally quasi-finite discrete-preimage API, and the connected-space topology
of Johannes Hölzl, Mario Carneiro, Kenny Lau, Patrick Massot and Yury Kudryashov. In particular,
`Scheme.Hom.isDiscrete_preimage_singleton`, `TotallyDisconnectedSpace.eq_of_continuous` and
`IsPreconnected.isDiscrete_iff_subsingleton` supply the geometric and topological ingredients.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

namespace Scheme.Hom

/-- A preconnected scheme locally quasi-finite over a totally disconnected scheme has at most
one point. This uses Mathlib's constancy of continuous maps to totally disconnected spaces and
its discrete-fibre and preconnected discrete-set results. The source may be empty. -/
theorem subsingleton_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [PreconnectedSpace X] [TotallyDisconnectedSpace Y] :
    Subsingleton X := by
  refine ⟨fun x y ↦ ?_⟩
  have hfiber : f ⁻¹' {f x} = Set.univ :=
    Set.eq_univ_of_forall fun z ↦
      TotallyDisconnectedSpace.eq_of_continuous f f.continuous z x
  have hdiscrete := f.isDiscrete_preimage_singleton (f x)
  rw [hfiber] at hdiscrete
  exact (isPreconnected_univ.isDiscrete_iff_subsingleton.mp hdiscrete)
    (Set.mem_univ x) (Set.mem_univ y)

/-- A proper affine preconnected scheme over a field has at most one underlying point.
Preconnectedness suffices in place of preirreducibility, and neither nonemptiness nor reducedness
is required. This follows through Mathlib's proper-affine finiteness and locally quasi-finite
fibre topology; it does not assert that the morphism is an isomorphism. -/
theorem subsingleton_of_isProper_of_isAffine {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [IsAffine X] [PreconnectedSpace X] :
    Subsingleton X := by
  haveI : IsFinite f :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  exact subsingleton_of_locallyQuasiFinite f

end Scheme.Hom

end AlgebraicGeometry
