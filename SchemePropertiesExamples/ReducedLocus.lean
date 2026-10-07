/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ReducedLocus
public import Mathlib.RingTheory.ZMod
import Mathlib.Data.Nat.Squarefree

@[expose] public section

set_option warningAsError true

/-!
# Boundary cases for reduced prime localizations

The zero ring has no primes, a field has reduced prime localizations, and
`ZMod 4` has a nonreduced prime localization. For a product of a field and
`ZMod 4`, the nilradical module support contains one component but not the
other.
-/

open AlgebraicGeometry

private instance : Nontrivial (ZMod 4) := ⟨0, 1, by decide⟩

private instance : _root_.IsReduced (ZMod 2) :=
  isReduced_zmod.mpr (Or.inl Nat.squarefree_two)

private instance : Algebra (ZMod 2 × ZMod 4) (ZMod 2) :=
  (RingHom.fst (ZMod 2) (ZMod 4)).toAlgebra

example : IsEmpty (PrimeSpectrum (ZMod 1)) := inferInstance

example : IsEmpty (Spec (.of (ZMod 1))) := by
  change IsEmpty (PrimeSpectrum (ZMod 1))
  infer_instance

example : IsOpen {p : PrimeSpectrum (ZMod 1) |
    _root_.IsReduced (Localization.AtPrime p.asIdeal)} := by
  have hset : {p : PrimeSpectrum (ZMod 1) |
      _root_.IsReduced (Localization.AtPrime p.asIdeal)} = ∅ := by
    ext p
    exact isEmptyElim p
  rw [hset]
  exact isOpen_empty

example : ∃ p : PrimeSpectrum (ZMod 2),
    _root_.IsReduced (Localization.AtPrime p.asIdeal) ∧
      p ∉ Module.support (ZMod 2) (nilradical (ZMod 2)) := by
  classical
  refine ⟨Classical.choice (inferInstance : Nonempty (PrimeSpectrum (ZMod 2))), ?_, ?_⟩
  · infer_instance
  · have : Subsingleton (nilradical (ZMod 2)) := by
      rw [nilradical_eq_bot_iff.mpr (inferInstance : _root_.IsReduced (ZMod 2))]
      infer_instance
    rw [Module.support_eq_empty]
    simp

private theorem zmod_four_notReduced : ¬ _root_.IsReduced (ZMod 4) := by
  intro h
  have hnil : IsNilpotent (2 : ZMod 4) := ⟨2, by decide⟩
  exact (by decide : (2 : ZMod 4) ≠ 0) (h.eq_zero 2 hnil)

private theorem nonreduced_at_zmod_four : ∃ p : PrimeSpectrum (ZMod 4),
    ¬ _root_.IsReduced (Localization.AtPrime p.asIdeal) := by
  by_contra h
  apply zmod_four_notReduced
  apply isReduced_ofLocalizationMaximal (ZMod 4)
  intro J hJ
  have hall : ∀ p : PrimeSpectrum (ZMod 4),
      _root_.IsReduced (Localization.AtPrime p.asIdeal) := by
    simpa only [not_exists, not_not] using h
  exact hall ⟨J, hJ.isPrime⟩

example : ∃ x : (Spec (.of (ZMod 2)) : Scheme),
    _root_.IsReduced ((Spec (.of (ZMod 2)) : Scheme).presheaf.stalk x) := by
  classical
  exact ⟨Classical.choice (inferInstance : Nonempty (PrimeSpectrum (ZMod 2))),
    inferInstance⟩

example : ∃ x : (Spec (.of (ZMod 4)) : Scheme),
    ¬ _root_.IsReduced ((Spec (.of (ZMod 4)) : Scheme).presheaf.stalk x) := by
  by_contra h
  have hall : ∀ x : (Spec (.of (ZMod 4)) : Scheme),
      _root_.IsReduced ((Spec (.of (ZMod 4)) : Scheme).presheaf.stalk x) := by
    simpa only [not_exists, not_not] using h
  have hX : AlgebraicGeometry.IsReduced (Spec (.of (ZMod 4))) :=
    @isReduced_of_isReduced_stalk (Spec (.of (ZMod 4))) hall
  exact zmod_four_notReduced ((affine_isReduced_iff (.of (ZMod 4))).mp hX)

private instance (p₂ : PrimeSpectrum (ZMod 2)) :
    IsLocalization.AtPrime (ZMod 2)
      (PrimeSpectrum.comap (RingHom.fst (ZMod 2) (ZMod 4)) p₂).asIdeal := by
  let fstHom := RingHom.fst (ZMod 2) (ZMod 4)
  let p := PrimeSpectrum.comap fstHom p₂
  apply (isLocalization_iff p.asIdeal.primeCompl (ZMod 2)).mpr
  constructor
  · intro y
    have hy : fstHom (y : ZMod 2 × ZMod 4) ≠ 0 := by
      intro hy
      have hp : (y : ZMod 2 × ZMod 4) ∈ p.asIdeal := by
        change fstHom y ∈ p₂.asIdeal
        exact hy ▸ p₂.asIdeal.zero_mem
      exact (Ideal.mem_primeCompl_iff.mp y.property) hp
    have hone : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
    change IsUnit (fstHom (y : ZMod 2 × ZMod 4))
    rw [hone _ hy]
    exact isUnit_one
  constructor
  · intro z
    refine ⟨((z, 0), ⟨1, by simp⟩), ?_⟩
    change z * fstHom (1 : ZMod 2 × ZMod 4) = fstHom (z, 0)
    simp [fstHom]
  · intro x y hxy
    refine ⟨⟨(1, 0), ?_⟩, ?_⟩
    · apply Ideal.mem_primeCompl_iff.mpr
      intro hp
      have hone : (1 : ZMod 2) ∈ p₂.asIdeal := by
        simpa [p, fstHom, PrimeSpectrum.comap_asIdeal] using hp
      exact p₂.asIdeal.one_notMem hone
    · apply Prod.ext
      · change fstHom x = fstHom y at hxy
        simpa [fstHom] using hxy
      · simp

private theorem reduced_at_left_prod :
    ∃ p : PrimeSpectrum (ZMod 2 × ZMod 4),
      _root_.IsReduced (Localization.AtPrime p.asIdeal) := by
  classical
  let p₂ : PrimeSpectrum (ZMod 2) := Classical.choice inferInstance
  let p := PrimeSpectrum.comap (RingHom.fst (ZMod 2) (ZMod 4)) p₂
  let equiv := IsLocalization.algEquiv p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) (ZMod 2)
  exact ⟨p, isReduced_of_injective equiv.toRingHom equiv.injective⟩

example : ∃ p q : PrimeSpectrum (ZMod 2 × ZMod 4),
    _root_.IsReduced (Localization.AtPrime p.asIdeal) ∧
      ¬ _root_.IsReduced (Localization.AtPrime q.asIdeal) := by
  obtain ⟨p, hp⟩ := reduced_at_left_prod
  have hnon : ¬ _root_.IsReduced (ZMod 2 × ZMod 4) := by
    intro h
    have hnil : IsNilpotent (((0 : ZMod 2), (2 : ZMod 4)) : ZMod 2 × ZMod 4) :=
      ⟨2, by decide⟩
    have hz := congrArg Prod.snd (h.eq_zero _ hnil)
    exact (by decide : (2 : ZMod 4) ≠ 0) hz
  have hpoint : ∃ q : PrimeSpectrum (ZMod 2 × ZMod 4),
      ¬ _root_.IsReduced (Localization.AtPrime q.asIdeal) := by
    by_contra h
    apply hnon
    apply isReduced_ofLocalizationMaximal (ZMod 2 × ZMod 4)
    intro J hJ
    have hall : ∀ q : PrimeSpectrum (ZMod 2 × ZMod 4),
        _root_.IsReduced (Localization.AtPrime q.asIdeal) := by
      simpa only [not_exists, not_not] using h
    exact hall ⟨J, hJ.isPrime⟩
  obtain ⟨q, hq⟩ := hpoint
  exact ⟨p, q, hp, hq⟩

/-- In the spectrum of a field times `ZMod 4`, the nilradical module support
contains a prime from the second component and omits one from the first. -/
theorem support_nilradical_zmod_prod_nontrivial :
    ∃ p q : PrimeSpectrum (ZMod 2 × ZMod 4),
      p ∉ Module.support (ZMod 2 × ZMod 4) (nilradical (ZMod 2 × ZMod 4)) ∧
      q ∈ Module.support (ZMod 2 × ZMod 4) (nilradical (ZMod 2 × ZMod 4)) := by
  classical
  let p₂ : PrimeSpectrum (ZMod 2) := Classical.choice inferInstance
  let p₄ : PrimeSpectrum (ZMod 4) := Classical.choice inferInstance
  let p := PrimeSpectrum.comap (RingHom.fst (ZMod 2) (ZMod 4)) p₂
  let q := PrimeSpectrum.comap (RingHom.snd (ZMod 2) (ZMod 4)) p₄
  refine ⟨p, q, (Module.notMem_support_iff').mpr ?_, (Module.mem_support_iff').mpr ?_⟩
  · intro m
    refine ⟨((1 : ZMod 2), (0 : ZMod 4)), ?_, ?_⟩
    · intro h
      have : (1 : ZMod 2) ∈ p₂.asIdeal := by
        simpa [p, PrimeSpectrum.comap_asIdeal] using h
      exact p₂.asIdeal.one_notMem this
    · have hnil : IsNilpotent (m : ZMod 2 × ZMod 4) := mem_nilradical.mp m.property
      have hm : (m : ZMod 2 × ZMod 4).1 = 0 :=
        IsReduced.eq_zero _ (hnil.map (RingHom.fst (ZMod 2) (ZMod 4)))
      apply Subtype.ext
      apply Prod.ext
      · simpa using hm
      · simp
  · let m : nilradical (ZMod 2 × ZMod 4) :=
      ⟨((0 : ZMod 2), (2 : ZMod 4)), mem_nilradical.mpr ⟨2, by decide⟩⟩
    refine ⟨m, ?_⟩
    intro r hr hzero
    have hnot : r.2 ∉ p₄.asIdeal := by
      simpa [q, PrimeSpectrum.comap_asIdeal] using hr
    have htwo : (2 : ZMod 4) ∈ p₄.asIdeal := by
      apply p₄.isPrime.mem_of_pow_mem 2
      have hnil : (2 : ZMod 4) ^ 2 = 0 := by decide
      rw [hnil]
      exact p₄.asIdeal.zero_mem
    have hmul : r.2 * (2 : ZMod 4) = 0 := by
      simpa [m] using
        congrArg (fun a : nilradical (ZMod 2 × ZMod 4) => a.val.2) hzero
    have hdiv : ∀ a : ZMod 4, a * 2 = 0 → a = 0 ∨ a = 2 := by decide
    rcases hdiv r.2 hmul with hzero | htwo'
    · exact hnot (hzero ▸ p₄.asIdeal.zero_mem)
    · exact hnot (htwo' ▸ htwo)

example : ∃ p q : PrimeSpectrum (ZMod 2 × ZMod 4),
    _root_.IsReduced (Localization.AtPrime p.asIdeal) ∧
      ¬ _root_.IsReduced (Localization.AtPrime q.asIdeal) := by
  obtain ⟨p, q, hp, hq⟩ := support_nilradical_zmod_prod_nontrivial
  refine ⟨p, q, (IsLocalization.AtPrime.isReduced_iff_not_mem_support_nilradical
    p (Localization.AtPrime p.asIdeal)).2 hp, ?_⟩
  intro h
  exact ((IsLocalization.AtPrime.isReduced_iff_not_mem_support_nilradical
    q (Localization.AtPrime q.asIdeal)).1 h) hq

example : (Module.support (ZMod 4) (nilradical (ZMod 4))).Nonempty := by
  rw [← PrimeSpectrum.nonreduced_atPrime_eq_support_nilradical]
  exact nonreduced_at_zmod_four

example : IsOpen {p : PrimeSpectrum (ZMod 2) |
    _root_.IsReduced (Localization.AtPrime p.asIdeal)} := by
  have hFinite : Module.Finite (ZMod 2) (nilradical (ZMod 2)) := by
    rw [nilradical_eq_bot_iff.mpr (inferInstance : _root_.IsReduced (ZMod 2))]
    infer_instance
  exact @PrimeSpectrum.isOpen_isReduced_atPrime (ZMod 2) _ hFinite

example : IsOpen {x : (Spec (.of (ZMod 2 × ZMod 4)) : Scheme) |
    _root_.IsReduced ((Spec (.of (ZMod 2 × ZMod 4)) : Scheme).presheaf.stalk x)} := by
  exact isOpen_setOf_isReduced_stalk _
