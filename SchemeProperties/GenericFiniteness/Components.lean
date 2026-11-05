/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.GenericFiniteness
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober

/-!
# Finiteness near a discrete space of generic points

A locally finite type, quasi-compact morphism whose target has a discrete subspace
of component generic points is finite over a dense open containing every such
point, provided its ordinary point fibres at those points are finite. The topology
on the generic points is the canonical topology inherited from the target.

For a target with finitely many irreducible components this discreteness is
automatic, giving the finite-component criterion. Both restrictions have the whole
preimage of the open as their source and retain the original structure sheaves.
Empty targets and empty generic fibres are allowed. Neither criterion assumes
separatedness, reducedness, or Noetherianity.

## References

* The generic-point criterion in `SchemeProperties.GenericFiniteness`,
  `Scheme.Hom.exists_isFinite_morphismRestrict_of_isGenericPoint`.
* Mathlib's irreducible-component, generic-point, scheme-restriction, and
  target-local finite-morphism APIs.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

private theorem genericPoints_t1Space {α : Type*} [TopologicalSpace α] [T0Space α] :
    T1Space (genericPoints α) := by
  refine t1Space_iff_specializes_imp_eq.mpr fun x y hxy ↦ ?_
  apply genericPoints.component_injective
  apply Subtype.ext
  exact (Maximal.eq_of_subset y.property x.property.1
    ((subtype_specializes_iff x y).mp hxy).closure_subset).symm

private lemma exists_isGenericPoint_opens_of_discreteTopology_genericPoints
    {T : Type*} [TopologicalSpace T] [QuasiSober T]
    [DiscreteTopology (genericPoints T)] (η : genericPoints T) :
    ∃ (U : Opens T) (hηU : η.1 ∈ U),
      IsGenericPoint (⟨η.1, hηU⟩ : U) (Set.univ : Set U) := by
  obtain ⟨O, hO, hOη⟩ := discreteTopology_subtype_iff'.mp
    (inferInstance : DiscreteTopology (genericPoints T)) η.1 η.2
  have hηO : η.1 ∈ O := by
    have hη : η.1 ∈ O ∩ genericPoints T := by rw [hOη]; rfl
    exact hη.1
  let U : Opens T := ⟨O, hO⟩
  refine ⟨U, hηO, ?_⟩
  apply isGenericPoint_iff_specializes.mpr
  intro x
  constructor
  · intro _; trivial
  · intro _
    -- A component through x has its generic point in O, so isolation identifies it with η.
    let C : irreducibleComponents T :=
      ⟨irreducibleComponent x.1, irreducibleComponent_mem_irreducibleComponents x.1⟩
    let ξ : genericPoints T := genericPoints.ofComponent C
    have hξx : ξ.1 ⤳ x.1 :=
      (genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent
    have hξη : ξ.1 = η.1 := by
      have hξO : ξ.1 ∈ O := hξx.mem_open hO x.2
      have hξ : ξ.1 ∈ ({η.1} : Set T) := hOη ▸ ⟨hξO, ξ.2⟩
      exact hξ
    apply U.isOpenEmbedding'.isInducing.specializes_iff.mp
    change η.1 ⤳ x.1
    rwa [hξη] at hξx

namespace AlgebraicGeometry

universe u

/-- A locally finite type, quasi-compact morphism with finite ordinary point fibres
at all component generic points is finite on the whole preimage of a dense open
containing all those points when their canonical inherited topology is discrete.
No separatedness, reducedness, or Noetherianity assumption is required. -/
theorem Scheme.Hom.exists_isFinite_morphismRestrict_of_discreteTopology_genericPoints
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [DiscreteTopology (genericPoints Y)]
    (hf : ∀ η ∈ genericPoints Y, (f ⁻¹' {η}).Finite) :
    ∃ U : Y.Opens, genericPoints Y ⊆ (U : Set Y) ∧
      Dense (U : Set Y) ∧ IsFinite (f ∣_ U) := by
  classical
  have hlocal (η : genericPoints Y) :
      ∃ W : Y.Opens, η.1 ∈ W ∧ IsFinite (f ∣_ W) := by
    obtain ⟨(O : Y.Opens), hηO, hη⟩ :=
      exists_isGenericPoint_opens_of_discreteTopology_genericPoints η
    let ηO : O.toScheme := ⟨η.1, hηO⟩
    have hfO : ((f ∣_ O) ⁻¹' {ηO}).Finite := by
      refine Set.Finite.of_injOn (f := fun x : (f ⁻¹ᵁ O).toScheme ↦ x.1)
        ?_ Subtype.val_injective.injOn (hf η.1 η.2)
      intro x hx
      change f x.1 = η.1
      have hx' : (f ∣_ O) x = ηO := hx
      exact (morphismRestrict_base_coe f O x).symm.trans
        (congrArg (fun y : O.toScheme ↦ y.1) hx')
    obtain ⟨V, hηV, _, hfinite⟩ :=
      (f ∣_ O).exists_isFinite_morphismRestrict_of_isGenericPoint ηO hη hfO
    refine ⟨O.ι ''ᵁ V, ⟨ηO, hηV, rfl⟩, ?_⟩
    let : IsFinite ((f ∣_ O) ∣_ V) := hfinite
    rw [Arrow.iso_w' (morphismRestrictRestrict f O V)]
    infer_instance
  choose W hηW hfinite using hlocal
  let U : Y.Opens := iSup W
  have hGP : genericPoints Y ⊆ (U : Set Y) := by
    intro η hη
    exact Opens.mem_iSup.mpr ⟨⟨η, hη⟩, hηW ⟨η, hη⟩⟩
  refine ⟨U, hGP, ?_, ?_⟩
  · apply dense_iff_closure_eq.mpr
    apply le_antisymm (Set.subset_univ _)
    rw [← genericPoints.closure (α := Y)]
    exact closure_mono hGP
  · -- Finiteness is assembled on the target, over the whole preimage of U.
    let : IsZariskiLocalAtTarget (@IsFinite.{u} : MorphismProperty Scheme.{u}) := by
      let : IsZariskiLocalAtTarget (@IsIntegralHom.{u} : MorphismProperty Scheme.{u}) :=
        (HasAffineProperty.iff.mp IsIntegralHom.hasAffineProperty).1
      let : IsZariskiLocalAtTarget
          (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
        (HasAffineProperty.iff.mp
          (HasRingHomProperty.HasAffineProperty
            (Q := RingHom.FiniteType)
            (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}))).1
      exact IsFinite.eq_inf.symm ▸
        CategoryTheory.MorphismProperty.IsLocalAtTarget.inf
          (K := Scheme.zariskiPrecoverage)
          (@IsIntegralHom.{u} : MorphismProperty Scheme.{u})
          (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    let C (η : genericPoints Y) : U.toScheme.Opens := U.ι ⁻¹ᵁ W η
    have hcover : iSup C = ⊤ := by
      apply le_antisymm le_top
      intro x _
      obtain ⟨η, hη⟩ := Opens.mem_iSup.mp x.2
      exact Opens.mem_iSup.mpr ⟨η, hη⟩
    apply IsZariskiLocalAtTarget.of_iSup_eq_top
      (P := (@IsFinite : MorphismProperty Scheme.{u})) (f := f ∣_ U) C hcover
    intro η
    have himage : U.ι ''ᵁ C η = W η := by
      change U.ι ''ᵁ (U.ι ⁻¹ᵁ W η) = W η
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr (le_iSup W η)
    let : IsFinite (f ∣_ U.ι ''ᵁ C η) := by
      rw [himage]
      exact hfinite η
    rw [Arrow.iso_w' (morphismRestrictRestrict f U (C η)).symm]
    infer_instance

/-- A locally finite type, quasi-compact morphism to a scheme with finitely many
irreducible components and finite ordinary point fibres at all component generic
points is finite on the whole preimage of a dense open containing all those points.
No separatedness, reducedness, or Noetherianity assumption is required. This extends
`Scheme.Hom.exists_isFinite_morphismRestrict_of_isGenericPoint` to finitely many
irreducible components. -/
theorem Scheme.Hom.exists_isFinite_morphismRestrict_of_finite_irreducibleComponents
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hY : (irreducibleComponents Y).Finite)
    (hf : ∀ η ∈ genericPoints Y, (f ⁻¹' {η}).Finite) :
    ∃ U : Y.Opens, genericPoints Y ⊆ (U : Set Y) ∧
      Dense (U : Set Y) ∧ IsFinite (f ∣_ U) := by
  let : T1Space (genericPoints Y) := genericPoints_t1Space
  let : Finite (genericPoints Y) := (genericPoints.finite hY).to_subtype
  let : DiscreteTopology (genericPoints Y) := inferInstance
  exact f.exists_isFinite_morphismRestrict_of_discreteTopology_genericPoints hf

end AlgebraicGeometry
