/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.PullbackSpectrumPushout
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.NormNum

/-!
# Boundary examples for the spectrum of a ring pullback

Polynomial coefficient reduction and constant inclusion give an asymmetric
nontrivial gluing square. Zero target rings recover disjoint unions; a zero
component gives the identity boundary. The examples also exercise transported
maps between distinct ring-carrier universes.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open Polynomial

namespace PrimeSpectrum

private def coeffReduction : ℤ[X] →+* (ZMod 2)[X] :=
  Polynomial.mapRingHom (Int.castRingHom (ZMod 2))

private def constantInclusion : ZMod 2 →+* (ZMod 2)[X] :=
  Polynomial.C

private theorem coeffReduction_surjective : Function.Surjective coeffReduction := by
  simpa only [coeffReduction, Polynomial.coe_mapRingHom] using
    (Polynomial.map_surjective (f := Int.castRingHom (ZMod 2)) ZMod.intCast_surjective)

private theorem coeffReduction_not_injective : ¬ Function.Injective coeffReduction := by
  intro hinj
  have htwo : (Polynomial.C (2 : ℤ) : ℤ[X]) ≠ 0 := by norm_num
  have hcast : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  have hpoly : (2 : (ZMod 2)[X]) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (fun coeff : ZMod 2 => (Polynomial.C coeff : (ZMod 2)[X])) hcast
  have hker : coeffReduction (Polynomial.C (2 : ℤ)) = coeffReduction 0 := by
    simpa [coeffReduction] using hpoly
  exact htwo (hinj hker)

private theorem constantInclusion_not_surjective :
    ¬ Function.Surjective constantInclusion := by
  intro hsurj
  obtain ⟨b, hb⟩ := hsurj (Polynomial.X : (ZMod 2)[X])
  exact Polynomial.X_ne_C b hb.symm

/-- Polynomial reduction is surjective but not injective, whereas constant
polynomial inclusion is not surjective. Nevertheless their whole spectral
square is a pushout. -/
example :
    ¬ Function.Injective coeffReduction ∧
    ¬ Function.Surjective constantInclusion ∧
    IsPushout (comapULift.{0, 0, 1} coeffReduction)
      (comapULift.{0, 0, 1} constantInclusion)
      (comapULift.{0, 0, 1} (coeffReduction.pullbackFst constantInclusion))
      (comapULift.{0, 0, 1} (coeffReduction.pullbackSnd constantInclusion)) :=
  ⟨coeffReduction_not_injective, constantInclusion_not_surjective,
    isPushout_pullback coeffReduction constantInclusion coeffReduction_surjective⟩

/-- The Zariski topology in this asymmetric polynomial example is exactly
the topology coinduced by the two spectral projections. -/
example :
    (inferInstance : TopologicalSpace
      (PrimeSpectrum (coeffReduction.pullback constantInclusion))) =
      (inferInstance : TopologicalSpace (PrimeSpectrum ℤ[X])).coinduced
        (comap (coeffReduction.pullbackFst constantInclusion)) ⊔
      (inferInstance : TopologicalSpace (PrimeSpectrum (ZMod 2))).coinduced
        (comap (coeffReduction.pullbackSnd constantInclusion)) := by
  apply TopologicalSpace.ext
  funext V
  apply propext
  change IsOpen V ↔
    IsOpen ((comap (coeffReduction.pullbackFst constantInclusion)) ⁻¹' V) ∧
    IsOpen ((comap (coeffReduction.pullbackSnd constantInclusion)) ⁻¹' V)
  exact isOpen_pullback_iff coeffReduction constantInclusion coeffReduction_surjective V

/-- A surjective `A → C` and a non-surjective diagonal `B → C` can
identify distinct points of `Spec A` in the pushout. -/
theorem exists_not_injective_comap_pullbackFst :
    ∃ (α : (ZMod 2 × ZMod 2) →+* (ZMod 2 × ZMod 2))
    (β : ZMod 2 →+* (ZMod 2 × ZMod 2)),
    Function.Surjective α ∧ ¬ Function.Surjective β ∧
      ¬ Function.Injective (comap (α.pullbackFst β)) := by
  let α : (ZMod 2 × ZMod 2) →+* (ZMod 2 × ZMod 2) := RingHom.id _
  let β : ZMod 2 →+* (ZMod 2 × ZMod 2) :=
    (RingHom.id (ZMod 2)).prod (RingHom.id (ZMod 2))
  let p : PrimeSpectrum (ZMod 2 × ZMod 2) :=
    primeSpectrumProdHomeo.symm (.inl default)
  let q : PrimeSpectrum (ZMod 2 × ZMod 2) :=
    primeSpectrumProdHomeo.symm (.inr default)
  have hpq : p ≠ q := by
    intro h
    have := congrArg (primeSpectrumProdHomeo (R := ZMod 2) (S := ZMod 2)) h
    simp [p, q] at this
  have hcomm (r : PrimeSpectrum (ZMod 2 × ZMod 2)) :
      comap (α.pullbackFst β) (comap α r) =
        comap (α.pullbackSnd β) (comap β r) := by
    rw [← comap_comp_apply, ← comap_comp_apply, RingHom.pullback_comm_sq]
  have himage : comap (α.pullbackFst β) p = comap (α.pullbackFst β) q := by
    calc
      comap (α.pullbackFst β) p =
          comap (α.pullbackSnd β) (comap β p) := by simpa [α, comap_id] using hcomm p
      _ = comap (α.pullbackSnd β) (comap β q) := by
            rw [Subsingleton.elim (comap β p) (comap β q)]
      _ = comap (α.pullbackFst β) q := by simpa [α, comap_id] using (hcomm q).symm
  refine ⟨α, β, fun x => ⟨x, rfl⟩, ?_, ?_⟩
  · intro hsurj
    obtain ⟨b, hb⟩ := hsurj ((0 : ZMod 2), (1 : ZMod 2))
    have hleft : b = 0 := by simpa [β] using congrArg Prod.fst hb
    have hright : b = 1 := by simpa [β] using congrArg Prod.snd hb
    exact zero_ne_one (hleft.symm.trans hright)
  · intro hinj
    exact hpq (hinj himage)

private def pullbackZeroEquivProd {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Subsingleton C]
    (α : A →+* C) (β : B →+* C) : α.pullback β ≃+* A × B :=
  RingEquiv.ofBijective ((α.pullbackFst β).prod (α.pullbackSnd β))
    ⟨by
      intro x y h
      exact Subtype.ext h,
    by
      intro x
      exact ⟨⟨x, Subsingleton.elim _ _⟩, rfl⟩⟩

/-- When the common target is the zero ring, the pullback ring is a product
and its spectrum is a disjoint union. The categorical pushout still applies. -/
example (α : ℤ →+* ZMod 1) (β : ZMod 2 →+* ZMod 1) :
    (∃ _ : PrimeSpectrum (α.pullback β) ≃ₜ PrimeSpectrum ℤ ⊕ PrimeSpectrum (ZMod 2),
      IsPushout (comapULift.{0, 0, 1} α) (comapULift.{0, 0, 1} β)
        (comapULift.{0, 0, 1} (α.pullbackFst β))
        (comapULift.{0, 0, 1} (α.pullbackSnd β))) := by
  refine ⟨(homeomorphOfRingEquiv (pullbackZeroEquivProd α β)).trans
    primeSpectrumProdHomeo, isPushout_pullback α β ?_⟩
  intro c
  exact ⟨0, Subsingleton.elim _ _⟩

/-- If `A = C = 0`, the pullback is `B`; hence the `B`-leg on spectra
is a homeomorphism even though the other two spectra are empty. -/
example (α : ZMod 1 →+* ZMod 1) (β : ℤ →+* ZMod 1) :
    IsHomeomorph (comap (α.pullbackSnd β)) ∧
      IsEmpty (PrimeSpectrum (ZMod 1)) := by
  have hbij : Function.Bijective (α.pullbackSnd β) := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · exact h
    · intro b
      exact ⟨⟨(0, b), Subsingleton.elim _ _⟩, rfl⟩
  exact ⟨isHomeomorph_comap_of_bijective hbij, inferInstance⟩

/-- For a zero left component, restriction to the integral right component
uniquely determines a continuous map from the whole pullback spectrum. -/
example (α : ZMod 1 →+* ZMod 1) (β : ℤ →+* ZMod 1) :
    ∃! fD : C(PrimeSpectrum (α.pullback β), PrimeSpectrum ℤ),
      ∀ b, fD (comap (α.pullbackSnd β) b) = b := by
  let fA : C(PrimeSpectrum (ZMod 1), PrimeSpectrum ℤ) :=
    ⟨fun _ => Classical.choice inferInstance, continuous_const⟩
  obtain ⟨fD, hfD, hunique⟩ :=
    existsUnique_continuousMap_pullback α β
      (fun _ => ⟨0, Subsingleton.elim _ _⟩) fA (ContinuousMap.id _)
      (by intro c; exact isEmptyElim c)
  refine ⟨fD, hfD.2, ?_⟩
  intro g hg
  apply hunique g
  constructor
  · intro a
    exact isEmptyElim a
  · exact hg

/-- The entirely zero diagram has no points on any of its four spectra,
but remains covered by the same universal property. -/
example (α β : ZMod 1 →+* ZMod 1) :
    IsEmpty (PrimeSpectrum (α.pullback β)) ∧
      IsPushout (comapULift.{0, 0, 1} α) (comapULift.{0, 0, 1} β)
        (comapULift.{0, 0, 1} (α.pullbackFst β))
        (comapULift.{0, 0, 1} (α.pullbackSnd β)) := by
  have hzero : Subsingleton (α.pullback β) :=
    (pullbackZeroEquivProd α β).injective.subsingleton
  exact ⟨isEmpty_iff_subsingleton.mpr hzero,
    isPushout_pullback α β (fun _ => ⟨0, Subsingleton.elim _ _⟩)⟩

private def liftedReduction : ULift.{u} ℤ →+* ULift.{v} (ZMod 1) :=
  RingHom.ulift (Int.castRingHom (ZMod 1))

private def liftedConstant : ℤ →+* ULift.{v} (ZMod 1) :=
  (ULift.ringEquiv (R := ZMod 1)).symm.toRingHom.comp (Int.castRingHom (ZMod 1))

/-- Distinct carrier universes and a further target universe still permit
descent to the nontrivial spectrum of the integers. -/
example : ∃ d :
    (TopCat.uliftFunctor.{max u v 1}).obj
        (TopCat.of (PrimeSpectrum (liftedReduction.{u, v}.pullback liftedConstant.{v}))) ⟶
      (TopCat.uliftFunctor.{max u v 1}).obj (TopCat.of (PrimeSpectrum ℤ)),
    ∀ p : PrimeSpectrum (ULift.{u} ℤ),
      d (⟨comap (liftedReduction.{u, v}.pullbackFst liftedConstant.{v}) p⟩) =
        ⟨comap ((ULift.ringEquiv (R := ℤ)).symm.toRingHom) p⟩ := by
  let α := liftedReduction.{u, v}
  let β := liftedConstant.{v}
  have hα : Function.Surjective α := fun _ => ⟨0, Subsingleton.elim _ _⟩
  let h : IsPushout (comapULift.{u, v, max u v 1} α)
      (comapULift.{0, v, max u v 1} β)
      (comapULift.{u, u, max u v 1} (α.pullbackFst β))
      (comapULift.{u, 0, max u v 1} (α.pullbackSnd β)) :=
    isPushout_pullback.{1, u, 0, v} α β hα
  let fA := comapULift.{0, u, max u v 1} (ULift.ringEquiv (R := ℤ)).symm.toRingHom
  let fB := comapULift.{0, 0, max u v 1} (RingHom.id ℤ)
  have hagree : comapULift.{u, v, max u v 1} α ≫ fA =
      comapULift.{0, v, max u v 1} β ≫ fB := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro c
    exact isEmptyElim c.down
  refine ⟨h.desc fA fB hagree, ?_⟩
  intro p
  have hfac := h.inl_desc fA fB hagree
  change (comapULift.{u, u, max u v 1} (α.pullbackFst β) ≫
    h.desc fA fB hagree) ⟨p⟩ = fA ⟨p⟩
  exact congrArg (fun (morphism : (TopCat.uliftFunctor.{max u v 1}).obj
    (TopCat.of (PrimeSpectrum (ULift.{u} ℤ))) ⟶
      (TopCat.uliftFunctor.{max u v 1}).obj (TopCat.of (PrimeSpectrum ℤ))) =>
        morphism ⟨p⟩) hfac

end PrimeSpectrum
