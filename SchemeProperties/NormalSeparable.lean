/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.NormalEtale
public import SchemeProperties.NormalLocalization
public import SchemeProperties.NormalPolynomial
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.FieldTheory.TranscendentalSeparable
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Finite

public section

set_option warningAsError true

/-!
# Local normality under separable field base change

This file proves that flat directed unions of locally normal subrings are
locally normal. It applies this to tensor products with separably generated and
transcendental-separable field extensions.
-/

noncomputable section

open Polynomial
open scoped TensorProduct nonZeroDivisors

private theorem isDomain_iSup_of_directed
    {A : Type*} [CommRing A] {ι : Type*} [Nonempty ι]
    (S : ι → Subring A) [∀ i, IsDomain (S i)]
    (hS : Directed (· ≤ ·) S) (hTop : ⨆ i, S i = ⊤) :
    IsDomain A := by
  classical
  have hmem (a : A) : ∃ i, a ∈ S i := by
    apply (Subring.mem_iSup_of_directed hS).mp
    rw [hTop]
    exact Set.mem_univ a
  let i0 : ι := Classical.choice ‹Nonempty ι›
  let _ : Nontrivial A := (S i0).subtype_injective.nontrivial
  let _ : NoZeroDivisors A := ⟨by
    intro a b hab
    obtain ⟨i, hai⟩ := hmem a
    obtain ⟨j, hbj⟩ := hmem b
    obtain ⟨k, hik, hjk⟩ := hS i j
    let ak : S k := ⟨a, hik hai⟩
    let bk : S k := ⟨b, hjk hbj⟩
    have hakbk : ak * bk = 0 := by
      apply Subtype.ext
      exact hab
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hakbk with ha | hb
    · left
      simpa only [ak, Subring.coe_zero] using congr_arg Subtype.val ha
    · right
      simpa only [bk, Subring.coe_zero] using congr_arg Subtype.val hb⟩
  exact NoZeroDivisors.to_isDomain A
private theorem isIntegrallyClosed_iSup_of_directed
    {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} [Nonempty ι]
    (S : ι → Subring R) (hS : Directed (· ≤ ·) S)
    (hTop : ⨆ i, S i = ⊤) (hIC : ∀ i, IsIntegrallyClosed (S i)) :
    IsIntegrallyClosed R := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro x hx
  rcases hx with ⟨p, hp, hpx⟩
  rcases IsFractionRing.div_surjective R x with ⟨a, b, hb, hab⟩
  let s : Finset R := insert a (insert b p.coeffs)
  have hs : (s : Set R) ⊆ ⋃ i, (S i : Set R) := by
    rw [← Subring.coe_iSup_of_directed hS, hTop]
    exact Set.subset_univ _
  obtain ⟨i, hi⟩ :=
    (show Directed (· ⊆ ·) fun i ↦ (S i : Set R) from hS).exists_mem_subset_of_finset_subset_biUnion hs
  let T := S i
  have haT : a ∈ T := hi (by simp [s])
  have hbT : b ∈ T := hi (by simp [s])
  have hpT : (p.coeffs : Set R) ⊆ T := by
    intro c hc
    exact hi (by simp [s, hc])
  let aT : T := ⟨a, haT⟩
  let bT : T := ⟨b, hbT⟩
  have hbT0 : bT ≠ 0 := by
    intro h
    apply nonZeroDivisors.ne_zero hb
    exact congr_arg Subtype.val h
  let bT' : nonZeroDivisors T := ⟨bT, mem_nonZeroDivisors_of_ne_zero hbT0⟩
  let y : FractionRing T := IsLocalization.mk' (FractionRing T) aT bT'
  let g : T →+* FractionRing R :=
    (algebraMap R (FractionRing R)).comp T.subtype
  have hg : Function.Injective g :=
    (IsFractionRing.injective R (FractionRing R)).comp T.subtype_injective
  let hgu : ∀ z : nonZeroDivisors T, IsUnit (g z) :=
    fun z ↦ IsFractionRing.isUnit_map_of_injective hg z
  let φ : FractionRing T →+* FractionRing R :=
    IsLocalization.lift hgu
  have hφ : Function.Injective φ := by
    exact φ.injective
  have hφcomp : φ.comp (algebraMap T (FractionRing T)) = g := by
    exact IsLocalization.lift_comp hgu
  have hφy : φ y = x := by
    rw [show φ y = x ↔ g aT = g bT * x by
      exact IsLocalization.lift_mk'_spec hgu aT x bT']
    have hbmap : g bT ≠ 0 := by
      intro h
      apply hbT0
      apply hg
      simpa using h
    have habg : g aT / g bT = x := by
      simpa only [g, RingHom.comp_apply, T, Subring.subtype_apply, aT, bT] using hab
    simpa only [mul_comm] using (div_eq_iff hbmap).mp habg
  let pT : T[X] := p.toSubring T hpT
  have hpTmonic : pT.Monic := (p.monic_toSubring T hpT).mpr hp
  have hpTy : pT.eval₂ (algebraMap T (FractionRing T)) y = 0 := by
    apply hφ
    rw [map_zero, hom_eval₂]
    rw [hφcomp]
    change pT.eval₂ ((algebraMap R (FractionRing R)).comp T.subtype) (φ y) = 0
    rw [hφy, ← eval₂_map, p.map_toSubring T hpT, hpx]
  have hy : IsIntegral T y := ⟨pT, hpTmonic, hpTy⟩
  obtain ⟨t, ht⟩ :=
    (isIntegrallyClosed_iff (FractionRing T)).mp (hIC i) hy
  refine ⟨t.1, ?_⟩
  calc
    algebraMap R (FractionRing R) t.1 = g t := rfl
    _ = φ (algebraMap T (FractionRing T) t) := (RingHom.congr_fun hφcomp t).symm
    _ = φ y := congr_arg φ ht
    _ = x := hφy
private theorem localizedRanges_directed_iSup
    {R : Type*} [CommRing R] {ι : Type*} [Nonempty ι]
    (S : ι → Subring R) (hS : Directed (· ≤ ·) S)
    (hTop : ⨆ i, S i = ⊤) (q : Ideal R) [q.IsPrime]
    (hflat : ∀ i, RingHom.Flat (Subring.subtype (S i))) :
    let p : (i : ι) → Ideal (S i) := fun i ↦ q.comap (Subring.subtype (S i))
    let f : (i : ι) → Localization.AtPrime (p i) →+* Localization.AtPrime q :=
      fun i ↦ Localization.localRingHom (p i) q (Subring.subtype (S i)) rfl
    Directed (· ≤ ·) (fun i ↦ RingHom.range (f i)) ∧
      ⨆ i, RingHom.range (f i) = ⊤ ∧
      ∀ i, Function.Injective (f i) := by
  classical
  let p : (i : ι) → Ideal (S i) := fun i ↦ q.comap (Subring.subtype (S i))
  let f : (i : ι) → Localization.AtPrime (p i) →+* Localization.AtPrime q :=
    fun i ↦ Localization.localRingHom (p i) q (Subring.subtype (S i)) rfl
  have hf (i : ι) : Function.Injective (f i) := by
    have hfl : (f i).Flat := (hflat i).localRingHom q (p i) rfl
    rw [RingHom.Flat] at hfl
    let _ : Algebra (Localization.AtPrime (p i)) (Localization.AtPrime q) := (f i).toAlgebra
    let _ : Module.Flat (Localization.AtPrime (p i)) (Localization.AtPrime q) := hfl
    have _ : IsLocalHom (algebraMap (Localization.AtPrime (p i)) (Localization.AtPrime q)) := by
      change IsLocalHom (f i)
      infer_instance
    have hff : Module.FaithfullyFlat (Localization.AtPrime (p i)) (Localization.AtPrime q) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact (RingHom.faithfullyFlat_algebraMap_iff.mpr hff).injective
  have hdir : Directed (· ≤ ·) (fun i ↦ (f i).range) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hS i j
    refine ⟨k, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      let e : S i →+* S k := Subring.inclusion hik
      have hp : p i = (p k).comap e := by
        ext x
        rfl
      let g : Localization.AtPrime (p i) →+* Localization.AtPrime (p k) :=
        Localization.localRingHom (p i) (p k) e hp
      refine ⟨g x, ?_⟩
      change f k (g x) = f i x
      rw [← RingHom.comp_apply]
      have hcomp := Localization.localRingHom_comp (p i) (p k) q e hp (S k).subtype rfl
      exact congr_arg (fun h : Localization.AtPrime (p i) →+* Localization.AtPrime q ↦ h x)
        hcomp.symm
    · rintro _ ⟨x, rfl⟩
      let e : S j →+* S k := Subring.inclusion hjk
      have hp : p j = (p k).comap e := by
        ext x
        rfl
      let g : Localization.AtPrime (p j) →+* Localization.AtPrime (p k) :=
        Localization.localRingHom (p j) (p k) e hp
      refine ⟨g x, ?_⟩
      change f k (g x) = f j x
      rw [← RingHom.comp_apply]
      have hcomp := Localization.localRingHom_comp (p j) (p k) q e hp (S k).subtype rfl
      exact congr_arg (fun h : Localization.AtPrime (p j) →+* Localization.AtPrime q ↦ h x)
        hcomp.symm
  refine ⟨hdir, ?_, hf⟩
  apply top_unique
  intro x _
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  have ha : ∃ i, a ∈ S i := by
    apply (Subring.mem_iSup_of_directed hS).mp
    rw [hTop]
    trivial
  have hs : ∃ i, (s : R) ∈ S i := by
    apply (Subring.mem_iSup_of_directed hS).mp
    rw [hTop]
    trivial
  obtain ⟨i, hai⟩ := ha
  obtain ⟨j, hsj⟩ := hs
  obtain ⟨k, hik, hjk⟩ := hS i j
  let ak : S k := ⟨a, hik hai⟩
  have hsk : (s : R) ∈ S k := hjk hsj
  have hskp : (⟨s, hsk⟩ : S k) ∈ (p k).primeCompl := by
    exact s.property
  let sk : (p k).primeCompl := ⟨⟨s, hsk⟩, hskp⟩
  apply (Subring.mem_iSup_of_directed hdir).mpr
  refine ⟨k, ?_⟩
  refine ⟨IsLocalization.mk' (Localization.AtPrime (p k)) ak sk, ?_⟩
  simp [f, ak, sk]
private theorem isLocallyNormal_atPrime_of_directed_flat_iSup
    {R : Type*} [CommRing R] {ι : Type*} [Nonempty ι]
    (S : ι → Subring R) (hS : Directed (· ≤ ·) S)
    (hTop : ⨆ i, S i = ⊤) (q : Ideal R) [q.IsPrime]
    (hflat : ∀ i, RingHom.Flat (Subring.subtype (S i)))
    (hNormal : ∀ i, IsLocallyNormalRing (S i)) :
    IsDomain (Localization.AtPrime q) ∧
      IsIntegrallyClosed (Localization.AtPrime q) := by
  classical
  let p : (i : ι) → Ideal (S i) := fun i ↦ q.comap (Subring.subtype (S i))
  let f : (i : ι) → Localization.AtPrime (p i) →+* Localization.AtPrime q :=
    fun i ↦ Localization.localRingHom (p i) q (Subring.subtype (S i)) rfl
  let T : ι → Subring (Localization.AtPrime q) := fun i ↦ (f i).range
  obtain ⟨hT, hTopT, hf⟩ := localizedRanges_directed_iSup S hS hTop q hflat
  have hDom (i : ι) : IsDomain (T i) := by
    let _ : IsLocallyNormalRing (S i) := hNormal i
    let _ : IsDomain (Localization.AtPrime (p i)) :=
      IsLocallyNormalRing.isDomain_atPrime ⟨p i, inferInstance⟩
    let e : Localization.AtPrime (p i) ≃+* T i :=
      RingEquiv.ofBijective (f i).rangeRestrict
        ⟨fun _ _ h ↦ hf i (congr_arg Subtype.val h), (f i).rangeRestrict_surjective⟩
    exact e.symm.toMulEquiv.isDomain _
  have hIC (i : ι) : IsIntegrallyClosed (T i) := by
    let _ : IsLocallyNormalRing (S i) := hNormal i
    let _ : IsIntegrallyClosed (Localization.AtPrime (p i)) :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime ⟨p i, inferInstance⟩
    let e : Localization.AtPrime (p i) ≃+* T i :=
      RingEquiv.ofBijective (f i).rangeRestrict
        ⟨fun _ _ h ↦ hf i (congr_arg Subtype.val h), (f i).rangeRestrict_surjective⟩
    exact IsIntegrallyClosed.of_equiv e
  let _ (i : ι) : IsDomain (T i) := hDom i
  have hR : IsDomain (Localization.AtPrime q) :=
    isDomain_iSup_of_directed T hT hTopT
  let _ : IsDomain (Localization.AtPrime q) := hR
  exact ⟨hR, isIntegrallyClosed_iSup_of_directed T hT hTopT hIC⟩

/-- A nonempty directed supremum of flat locally normal subrings is locally normal. -/
theorem IsLocallyNormalRing.of_directed_iSup
    {R : Type*} [CommRing R] {ι : Type*} [Nonempty ι]
    (S : ι → Subring R) (hS : Directed (· ≤ ·) S)
    (hTop : ⨆ i, S i = ⊤)
    (hflat : ∀ i, RingHom.Flat (Subring.subtype (S i)))
    (hNormal : ∀ i, IsLocallyNormalRing (S i)) :
    IsLocallyNormalRing R := by
  constructor
  · intro q
    exact (isLocallyNormal_atPrime_of_directed_flat_iSup
      S hS hTop q.asIdeal hflat hNormal).1
  · intro q
    exact (isLocallyNormal_atPrime_of_directed_flat_iSup
      S hS hTop q.asIdeal hflat hNormal).2

private theorem tensorProductRanges_directed_iSup_flat
    {k A K : Type*} [Field k] [CommRing A] [Field K]
    [Algebra k A] [Algebra k K]
    {ι : Type*} [Nonempty ι]
    (L : ι → IntermediateField k K) (hL : Directed (· ≤ ·) L)
    (hTop : ⨆ i, L i = ⊤) :
    let f := fun i : ι ↦
      (Algebra.TensorProduct.map (AlgHom.id k A) (L i).val).toRingHom
    let S : ι → Subring (A ⊗[k] K) := fun i ↦ (f i).range
    Directed (· ≤ ·) S ∧ ⨆ i, S i = ⊤ ∧
      ∀ i, RingHom.Flat (Subring.subtype (S i)) := by
  classical
  let f := fun i : ι ↦
    (Algebra.TensorProduct.map (AlgHom.id k A) (L i).val).toRingHom
  let S : ι → Subring (A ⊗[k] K) := fun i ↦ (f i).range
  have hf (i : ι) : Function.Injective (f i) := by
    change Function.Injective
      (TensorProduct.map (LinearMap.id : A →ₗ[k] A) (L i).val.toLinearMap)
    exact TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id (L i).val.injective
  have hdir : Directed (· ≤ ·) S := by
    intro i j
    obtain ⟨m, him, hjm⟩ := hL i j
    refine ⟨m, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      let g :=
        Algebra.TensorProduct.map (AlgHom.id k A) (IntermediateField.inclusion him)
      refine ⟨g x, ?_⟩
      change f m (g x) = f i x
      have hval : (L m).val.comp (IntermediateField.inclusion him) = (L i).val := by
        ext
        rfl
      have hcomp := Algebra.TensorProduct.map_id_comp
        (R := k) (S := k) (A := A) (B := L i) (D := L m) (F := K)
        (L m).val (IntermediateField.inclusion him)
      rw [hval] at hcomp
      exact congr_arg (fun h : AlgHom k (A ⊗[k] (L i)) (A ⊗[k] K) ↦ h x) hcomp.symm
    · rintro _ ⟨x, rfl⟩
      let g :=
        Algebra.TensorProduct.map (AlgHom.id k A) (IntermediateField.inclusion hjm)
      refine ⟨g x, ?_⟩
      change f m (g x) = f j x
      have hval : (L m).val.comp (IntermediateField.inclusion hjm) = (L j).val := by
        ext
        rfl
      have hcomp := Algebra.TensorProduct.map_id_comp
        (R := k) (S := k) (A := A) (B := L j) (D := L m) (F := K)
        (L m).val (IntermediateField.inclusion hjm)
      rw [hval] at hcomp
      exact congr_arg (fun h : AlgHom k (A ⊗[k] (L j)) (A ⊗[k] K) ↦ h x) hcomp.symm
  refine ⟨hdir, ?_, ?_⟩
  · apply top_unique
    intro x hx
    clear hx
    refine TensorProduct.inductionOn x ?_ ?_
    · intro a z
      have hzTop : z ∈ ⋃ i, (L i : Set K) := by
        rw [← IntermediateField.coe_iSup_of_directed hL, hTop]
        trivial
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzTop
      apply (Subring.mem_iSup_of_directed hdir).mpr
      refine ⟨i, ?_⟩
      refine ⟨a ⊗ₜ[k] (⟨z, hzi⟩ : L i), ?_⟩
      rfl
    · intro x y hx hy
      exact (iSup S).add_mem hx hy
  · intro i
    have hflatf : (f i).Flat := by
      apply RingHom.Flat.tensorProductMap
      · exact RingHom.Flat.id A
      · exact RingHom.Flat.of_isField (Field.toIsField (L i)) (L i).val.toRingHom
    apply (RingHom.Flat.comp_iff_of_bijective_right
      (f := Subring.subtype (S i))
      (g := (f i).rangeRestrict)
      ⟨fun _ _ h ↦ hf i (congr_arg Subtype.val h), (f i).rangeRestrict_surjective⟩).mp
    change (f i).Flat
    exact hflatf

private theorem locallyNormal_tensorProduct_of_directed_intermediateFields
    {k A K : Type*} [Field k] [CommRing A] [Field K]
    [Algebra k A] [Algebra k K]
    {ι : Type*} [Nonempty ι]
    (L : ι → IntermediateField k K) (hL : Directed (· ≤ ·) L)
    (hTop : ⨆ i, L i = ⊤)
    (hNormal : ∀ i, IsLocallyNormalRing (A ⊗[k] L i)) :
    IsLocallyNormalRing (A ⊗[k] K) := by
  classical
  let f := fun i : ι ↦
    (Algebra.TensorProduct.map (AlgHom.id k A) (L i).val).toRingHom
  let S : ι → Subring (A ⊗[k] K) := fun i ↦ (f i).range
  obtain ⟨hS, hSup, hflat⟩ :=
    tensorProductRanges_directed_iSup_flat (A := A) (K := K) L hL hTop
  have hf (i : ι) : Function.Injective (f i) := by
    change Function.Injective
      (TensorProduct.map (LinearMap.id : A →ₗ[k] A) (L i).val.toLinearMap)
    exact TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id (L i).val.injective
  have hNormalS (i : ι) : IsLocallyNormalRing (S i) := by
    let _ : IsLocallyNormalRing (A ⊗[k] L i) := hNormal i
    let e : (A ⊗[k] L i) ≃+* S i :=
      RingEquiv.ofBijective (f i).rangeRestrict
        ⟨fun _ _ h ↦ hf i (congr_arg Subtype.val h), (f i).rangeRestrict_surjective⟩
    exact IsLocallyNormalRing.of_ringEquiv
      (R := A ⊗[k] L i) (S := S i) e
  exact IsLocallyNormalRing.of_directed_iSup S hS hSup hflat hNormalS

/-- Tensoring a locally normal algebra with an essentially finite-type,
separably generated field extension preserves local normality. -/
theorem IsLocallyNormalRing.tensorProduct_of_isSeparablyGenerated
    {k A L : Type*} [Field k] [CommRing A] [Field L]
    [Algebra k A] [Algebra k L]
    [IsLocallyNormalRing A] [Algebra.EssFiniteType k L]
    [Algebra.IsSeparablyGenerated k L] :
    IsLocallyNormalRing (A ⊗[k] L) := by
  classical
  obtain ⟨s, hs, hsep⟩ := (inferInstance : Algebra.IsSeparablyGenerated k L)
  let F := IntermediateField.adjoin k s
  let P := MvPolynomial s k
  let _ : FinTrdeg k L := inferInstance
  let _ : Finite s := finite_of_isTranscendenceBasis hs
  let _ : IsLocallyNormalRing (MvPolynomial s A) := inferInstance
  let ePoly : A ⊗[k] P ≃ₐ[A] MvPolynomial s A :=
    MvPolynomial.algebraTensorAlgEquiv k A
  let _ : IsLocallyNormalRing (A ⊗[k] P) :=
    IsLocallyNormalRing.of_ringEquiv ePoly.symm.toRingEquiv
  let ePF : FractionRing P ≃ₐ[k] F := by
    exact hs.1.aevalEquivField.trans
      (IntermediateField.equivOfEq (by rw [Subtype.range_val]))
  let eTensor : A ⊗[k] FractionRing P ≃ₐ[k] A ⊗[k] F :=
    AlgEquiv.ofBijective
      (Algebra.TensorProduct.map (AlgHom.id k A) ePF.toAlgHom)
      (Algebra.TensorProduct.map_bijective Function.bijective_id ePF.bijective)
  let _ : Algebra (A ⊗[k] P) (A ⊗[k] FractionRing P) :=
    (Algebra.TensorProduct.map (AlgHom.id k A)
      (IsScalarTower.toAlgHom k P (FractionRing P))).toAlgebra
  let _ : SMul A (A ⊗[k] P) := Algebra.toSMul
  let _ : SMul A (A ⊗[k] FractionRing P) := Algebra.toSMul
  let _ : IsScalarTower A (A ⊗[k] P) (A ⊗[k] FractionRing P) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext
      simp [RingHom.algebraMap_toAlgebra])
  have hloc : IsLocalization
      ((nonZeroDivisors P).map
        (Algebra.TensorProduct.includeRight (R := k) (A := A)))
      (A ⊗[k] FractionRing P) := by
    apply IsLocalization.tensorProduct_tensorProduct_right k A
    rfl
  let _ : IsLocalization
      ((nonZeroDivisors P).map
        (Algebra.TensorProduct.includeRight (R := k) (A := A)))
      (A ⊗[k] FractionRing P) := hloc
  let _ : IsLocallyNormalRing (A ⊗[k] FractionRing P) :=
    IsLocallyNormalRing.of_isLocalization
      (R := A ⊗[k] P)
      ((nonZeroDivisors P).map
        (Algebra.TensorProduct.includeRight (R := k) (A := A)))
      (A ⊗[k] FractionRing P)
  let _ : IsLocallyNormalRing (A ⊗[k] F) :=
    IsLocallyNormalRing.of_ringEquiv eTensor.toRingEquiv
  let _ : Algebra.EssFiniteType F L :=
    Algebra.EssFiniteType.of_comp k F L
  let _ : Algebra.IsSeparable F L := hsep
  let _ : Algebra.IsAlgebraic F L := inferInstance
  let _ : Module.Finite F L :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  let _ : Algebra.FormallyEtale F L :=
    Algebra.FormallyEtale.of_isSeparable F L
  let _ : Module.FinitePresentation F L :=
    Module.finitePresentation_of_finite F L
  let _ : Algebra.Etale F L := ⟨inferInstance, inferInstance⟩
  let B := A ⊗[k] F
  let rightAlg : Algebra F B := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra F B := rightAlg
  let _ : Module F B := @Algebra.toModule F B _ _ rightAlg
  let C := B ⊗[F] L
  let _ : CommRing C :=
    @Algebra.TensorProduct.instCommRing F B L
      (inferInstance) (inferInstance) rightAlg (inferInstance) (inferInstance)
  let leftAlg : Algebra B C :=
    Algebra.TensorProduct.leftAlgebra (R := F) (S := B) (A := B) (B := L)
  let _ : Algebra B C := leftAlg
  let _ : Module B C := @Algebra.toModule B C _ _ leftAlg
  let _ : Algebra.Etale B C := Algebra.Etale.baseChange F L B
  let hFiniteBC : Module.Finite B C := Module.Finite.base_change F B L
  let _ : Module.Finite B C := hFiniteBC
  let _ : IsLocallyNormalRing C :=
    IsLocallyNormalRing.of_finiteEtale (R := B) (S := C)
  let aAlg : Algebra A C :=
    Algebra.TensorProduct.leftAlgebra (R := F) (S := A) (A := B) (B := L)
  let _ : Algebra A C := aAlg
  let _ : IsScalarTower A B C := by
    constructor
    intro a b x
    refine TensorProduct.inductionOn x ?_ ?_
    · intro l y
      simp [smul_assoc]
    · intro x y hx hy
      simp
  let e : C ≃ₐ[A] A ⊗[k] L :=
    Algebra.IsPushout.cancelBaseChangeAlg k A F B L
  exact IsLocallyNormalRing.of_ringEquiv e.toRingEquiv

/-- Tensoring a locally normal algebra with a transcendental-separable field
extension preserves local normality. -/
theorem IsLocallyNormalRing.tensorProduct_of_isTranscendentalSeparable
    {k A K : Type*} [Field k] [CommRing A] [Field K]
    [Algebra k A] [Algebra k K] [IsLocallyNormalRing A]
    [Algebra.IsTranscendentalSeparable k K] :
    IsLocallyNormalRing (A ⊗[k] K) := by
  classical
  let I := {L : IntermediateField k K // Algebra.EssFiniteType k L}
  let _ : Nonempty I := by
    refine ⟨⟨⊥, IntermediateField.essFiniteType_iff.mpr ?_⟩⟩
    exact IntermediateField.fg_bot
  have hDirected : Directed (· ≤ ·) (fun i : I ↦ i.1) := by
    intro i j
    let M : IntermediateField k K := i.1 ⊔ j.1
    have hM : Algebra.EssFiniteType k M :=
      IntermediateField.essFiniteType_iff.mpr <|
        IntermediateField.fg_sup
          (IntermediateField.essFiniteType_iff.mp i.2)
          (IntermediateField.essFiniteType_iff.mp j.2)
    exact ⟨⟨M, hM⟩, le_sup_left, le_sup_right⟩
  have hTop : ⨆ i : I, i.1 = (⊤ : IntermediateField k K) := by
    apply top_unique
    intro x _
    let M : IntermediateField k K := IntermediateField.adjoin k {x}
    have hM : Algebra.EssFiniteType k M :=
      IntermediateField.essFiniteType_iff.mpr <|
        IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x)
    exact SetLike.le_def.mp (le_iSup (fun i : I ↦ i.1) ⟨M, hM⟩)
      (IntermediateField.subset_adjoin k {x} (by simp))
  have hNormal (i : I) : IsLocallyNormalRing (A ⊗[k] i.1) := by
    let _ : Algebra.EssFiniteType k i.1 := i.2
    let _ : Algebra.IsSeparablyGenerated k i.1 :=
      (inferInstance : Algebra.IsTranscendentalSeparable k K).forall_isSeparablyGenerated i.1 i.2
    exact IsLocallyNormalRing.tensorProduct_of_isSeparablyGenerated
  exact locallyNormal_tensorProduct_of_directed_intermediateFields
    (A := A) (K := K) (fun i : I ↦ i.1) hDirected hTop hNormal
