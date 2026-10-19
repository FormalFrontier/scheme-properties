/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.Topology.Irreducible

/-!
# Irreducibility of projective spectra of domains

A nonempty projective spectrum of a naturally graded domain is irreducible. Its
zero homogeneous ideal is a relevant prime ideal and defines a generic point.

Nonemptiness is essential: a domain concentrated in degree zero has empty
projective spectrum.

The proof uses Mathlib's projective spectrum, constructed by Jujian Zhang and
Johan Commelin, and its specialization-order API.

## References

- Stacks Project, [Tag 004W(1)](https://stacks.math.columbia.edu/tag/004W).
- Mathlib's topological irreducibility formalization by Johannes Hölzl, Mario Carneiro
  and Yury Kudryashov.
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry.Proj

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The projective spectrum of a naturally graded domain is irreducible whenever
it is nonempty. The proof uses its zero-ideal generic point and irreducible closure
as in [Stacks Project, Tag 004W(1)](https://stacks.math.columbia.edu/tag/004W). -/
instance irreducibleSpace [IsDomain A] [Nonempty (Proj 𝒜)] :
    IrreducibleSpace (Proj 𝒜) := by
  classical
  change IrreducibleSpace (ProjectiveSpectrum 𝒜)
  let p : Proj 𝒜 := Classical.choice inferInstance
  let η : ProjectiveSpectrum 𝒜 :=
    { asHomogeneousIdeal := ⊥
      isPrime := by
        simpa only [HomogeneousIdeal.toIdeal_bot] using
          (inferInstance : (⊥ : Ideal A).IsPrime)
      not_irrelevant_le := fun h ↦ p.not_irrelevant_le (h.trans bot_le) }
  have hη : closure ({η} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    have hle : η.asHomogeneousIdeal ≤ x.asHomogeneousIdeal := bot_le
    exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 η x).mp
      ((ProjectiveSpectrum.as_ideal_le_as_ideal 𝒜 η x).mp hle)
  refine (irreducibleSpace_def (ProjectiveSpectrum 𝒜)).mpr ?_
  simpa only [Set.top_eq_univ, hη] using (isIrreducible_singleton (x := η)).closure

end AlgebraicGeometry.Proj
