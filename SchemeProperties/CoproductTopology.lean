/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.Constructible

public section

/-!
# Topology of coproducts of schemes

This file packages two elementary topological properties of arbitrary
same-universe indexed coproducts of schemes. Quasiseparatedness is inherited
componentwise, while an infinite coproduct of nonempty schemes is not compact.

Both results use Mathlib's homeomorphism from the underlying space of a
scheme coproduct to the corresponding Sigma type. No finiteness, compactness,
nonemptiness, or separation assumption is needed for quasiseparatedness.

## References

- Mathlib's `AlgebraicGeometry.Limits` (`sigmaMk`) and Sigma-type topology,
  open-embedding, compactness and quasiseparatedness results used in the proofs.
-/

set_option warningAsError true

open CategoryTheory Limits Set TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

variable {ι : Type u} (X : ι → Scheme.{u})

/-- An indexed coproduct of quasiseparated schemes is quasiseparated.

The empty family and families with empty components are included. -/
noncomputable instance quasiSeparatedSpace_sigma
    [∀ i, QuasiSeparatedSpace (X i)] :
    QuasiSeparatedSpace (∐ X : Scheme.{u}) := by
  rw [← quasiSeparatedSpace_congr (sigmaMk X)]
  let Y : ι → Type u := fun i ↦ X i
  change QuasiSeparatedSpace (Σ i, Y i)
  refine .of_isOpenCover (U := fun i ↦
    ⟨Set.range (@Sigma.mk ι Y i), isOpen_range_sigmaMk⟩) ?_ ?_ ?_
  · apply IsOpenCover.of_sets (fun _ ↦ isOpen_range_sigmaMk)
    ext x
    constructor
    · exact fun _ ↦ Set.mem_univ x
    · intro _
      exact Set.mem_iUnion.mpr ⟨x.1, ⟨x.2, rfl⟩⟩
  · intro i U hU _
    simpa [Set.inter_comm] using hU.inter_right
      (isClosed_range_sigmaMk (i := i))
  · intro i
    change IsQuasiSeparated (Set.range (@Sigma.mk ι Y i))
    simpa only [Set.image_univ] using
      Topology.IsOpenEmbedding.sigmaMk.isQuasiSeparated_iff.mp
        (isQuasiSeparated_univ (α := Y i))

/-- An infinite indexed coproduct of nonempty schemes is not compact. -/
theorem not_compactSpace_sigma [Infinite ι] [∀ i, Nonempty (X i)] :
    ¬ CompactSpace (∐ X : Scheme.{u}) := by
  intro h
  let _ : CompactSpace (∐ X : Scheme.{u}) := h
  let _ : CompactSpace (Σ i, X i) := (sigmaMk X).symm.compactSpace
  obtain ⟨s, t, hs, _, hst⟩ :=
    @IsCompact.sigma_exists_finite_sigma_eq ι (fun i ↦ X i) _
      Set.univ CompactSpace.isCompact_univ
  have hsu : s = Set.univ := Set.eq_univ_of_forall fun i ↦ by
    obtain ⟨x⟩ := (inferInstance : Nonempty (X i))
    exact (Set.mem_sigma_iff.mp (hst.symm ▸ Set.mem_univ (Sigma.mk i x))).1
  exact Set.infinite_univ.not_finite (hsu ▸ hs)

end AlgebraicGeometry
