/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Geometric connectedness over separably closed fields

This file proves that every connected scheme over a separably closed field is geometrically
connected. The key algebraic theorem says that the tensor product of any two extension fields
of the base has connected prime spectrum.

No finite-type, reducedness, irreducibility, separation, properness, algebraicity or
algebraic-closedness hypothesis is imposed on the final theorem. Finite type is used only
internally: an idempotent in a tensor product is captured in tensor products of finitely
generated subalgebras. Passing from a separably closed field to its algebraic closure is purely
inseparable, so the relevant prime spectra are homeomorphic even over an imperfect base.

The scheme-facing declarations use one universe, matching Mathlib's geometric API.

## References

- The Stacks Project, tag 037U for geometric connectedness of field extensions
  over separably closed fields; tags 0386, 0385 and 0363 for the scheme-level
  passage via connected fibers and open projections.
- Mathlib's `LocallyOfFiniteType.jacobsonSpace` and `residueFieldIsoBase` for
  closed-point fibers, `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`
  for purely inseparable scalar extension, and `GeometricallyConnected` for
  the geometric-connectedness pullback API.
-/

public section

set_option warningAsError true

open Set Function Topology TopologicalSpace
open CategoryTheory Limits
open scoped TensorProduct

/-- An open surjection onto a connected Jacobson space is connected when its
closed-point fibers are connected. -/
lemma connectedSpace_of_isOpenMap_of_closedPoint_fibers
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ConnectedSpace Y]
    [JacobsonSpace Y] (f : X → Y) (hopen : IsOpenMap f)
    (hsurj : Surjective f)
    (hfib : ∀ y, IsClosed ({y} : Set Y) → IsConnected (f ⁻¹' {y})) : ConnectedSpace X := by
  rw [connectedSpace_iff_clopen]
  refine ⟨hsurj.nonempty, fun s hs ↦ ?_⟩
  by_cases hsempty : s = ∅
  · exact Or.inl hsempty
  right
  apply eq_univ_iff_forall.mpr
  intro x
  by_contra hx
  have hsne : s.Nonempty := nonempty_iff_ne_empty.mpr hsempty
  have hscne : sᶜ.Nonempty := ⟨x, hx⟩
  let U := f '' s
  let V := f '' sᶜ
  have hUopen : IsOpen U := hopen _ hs.isOpen
  have hVopen : IsOpen V := hopen _ hs.compl.isOpen
  have hUne : U.Nonempty := hsne.image f
  have hVne : V.Nonempty := hscne.image f
  have hcover : (Set.univ : Set Y) ⊆ U ∪ V := by
    intro y _
    obtain ⟨z, rfl⟩ := hsurj y
    by_cases hz : z ∈ s
    · exact Or.inl ⟨z, hz, rfl⟩
    · exact Or.inr ⟨z, hz, rfl⟩
  obtain ⟨y, _, hyU, hyV⟩ :=
    isConnected_univ.isPreconnected U V hUopen hVopen hcover
      (hUne.mono (by simp)) (hVne.mono (by simp))
  obtain ⟨z, ⟨hzU, hzV⟩, hzclosed⟩ :=
    nonempty_inter_closedPoints (Z := U ∩ V) ⟨y, hyU, hyV⟩
      (hUopen.inter hVopen).isLocallyClosed
  obtain ⟨a, ha, haf⟩ := hzU
  obtain ⟨b, hb, hbf⟩ := hzV
  have hsubset : f ⁻¹' {z} ⊆ s :=
    (hfib z hzclosed).isPreconnected.subset_isClopen hs
      ⟨a, by simpa using haf, ha⟩
  exact hb (hsubset (by simpa using hbf))

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {X Y : Scheme.{u}} (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))

private noncomputable def pullbackFstFiberIsoOfIsClosed [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    (pullback.fst f g).fiber x ≅ Y := by
  change pullback (pullback.fst f g) (X.fromSpecResidueField x) ≅ Y
  let e := residueFieldIsoBase f x hx
  let E := Scheme.Spec.mapIso e.symm.op
  have hE : E.hom = X.fromSpecResidueField x ≫ f := by
    exact SpecMap_residueFieldIsoBase_inv f x hx
  let p : Spec (.of K) ⟶ X := E.inv ≫ X.fromSpecResidueField x
  have hp0 : p ≫ f = 𝟙 _ := by
    simp only [p, Category.assoc, ← hE, E, Iso.inv_hom_id]
  let h : Y ⟶ Spec (X.residueField x) := g ≫ E.inv
  let j : Y ⟶ pullback f g := pullback.lift (g ≫ p) (𝟙 Y) (by
    simp only [Category.assoc, hp0, Category.comp_id, Category.id_comp])
  let inv : Y ⟶ pullback (pullback.fst f g) (X.fromSpecResidueField x) := pullback.lift j h (by
    simp only [j, h, pullback.lift_fst, Category.assoc, p])
  let hom : pullback (pullback.fst f g) (X.fromSpecResidueField x) ⟶ Y :=
    pullback.fst _ _ ≫ pullback.snd f g
  have hq : X.fromSpecResidueField x ≫ f ≫ E.inv = 𝟙 _ := by
    rw [← Category.assoc, ← hE, Iso.hom_inv_id]
  have hp : X.fromSpecResidueField x ≫ f ≫ p = X.fromSpecResidueField x := by
    dsimp only [p]
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun q ↦ q ≫ X.fromSpecResidueField x) hq
  refine Iso.mk hom inv ?_ ?_
  · apply pullback.hom_ext
    · simp only [Category.assoc, hom, inv, pullback.lift_fst, j, pullback.lift_fst,
        Category.id_comp]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
        rw [← pullback.condition_assoc (f := f) (g := g) p,
          pullback.condition_assoc (f := pullback.fst f g)
            (g := X.fromSpecResidueField x) (f ≫ p), hp]
        exact pullback.condition.symm
      · change pullback.fst _ _ ≫ pullback.snd f g ≫
          (pullback.lift (g ≫ p) (𝟙 Y) _) ≫ pullback.snd f g = _
        rw [pullback.lift_snd, Category.comp_id]
    · simp only [Category.assoc, hom, inv, pullback.lift_snd, h, Category.id_comp]
      rw [← pullback.condition_assoc (f := f) (g := g) E.inv,
        pullback.condition_assoc (f := pullback.fst f g)
          (g := X.fromSpecResidueField x) (f ≫ E.inv), hq,
        Category.comp_id]
  · change (pullback.lift j h _) ≫ pullback.fst _ _ ≫ pullback.snd f g = 𝟙 Y
    simp only [pullback.lift_fst_assoc, j, pullback.lift_snd]

/-- The fiber product of a connected scheme locally of finite type over an algebraically
closed field with any connected scheme over that field is connected. -/
lemma connectedSpace_pullback_of_isAlgClosed [LocallyOfFiniteType f]
    [ConnectedSpace X] [ConnectedSpace Y] : ConnectedSpace ↥(pullback f g) := by
  let _ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let q := pullback.fst f g
  apply connectedSpace_of_isOpenMap_of_closedPoint_fibers q q.isOpenMap q.surjective
  intro x hx
  rw [isConnected_iff_connectedSpace]
  rw [← (q.fiberHomeo x).connectedSpace_iff]
  rw [(Scheme.homeoOfIso (pullbackFstFiberIsoOfIsClosed f g x hx)).connectedSpace_iff]
  infer_instance

end AlgebraicGeometry

namespace Algebra.TensorProduct

universe u

/-- Base change commutes with tensor products. -/
noncomputable def baseChangeTensorProductEquiv (k K A B : Type u)
    [Field k] [Field K] [Algebra k K] [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] :
    (K ⊗[k] A) ⊗[K] (K ⊗[k] B) ≃ₐ[K] K ⊗[k] (A ⊗[k] B) :=
  (tensorTensorTensorComm k k K K K A K B).trans
    (congr (Algebra.TensorProduct.lid K K)
      (AlgEquiv.refl : (A ⊗[k] B) ≃ₐ[k] (A ⊗[k] B)))

end Algebra.TensorProduct

namespace PrimeSpectrum

universe u

open AlgebraicGeometry

private noncomputable def specPrimeSpectrumHomeomorph (R : Type u) [CommRing R] :
    ↥(Spec (.of R)) ≃ₜ PrimeSpectrum R := Homeomorph.refl _

variable (k A B : Type u) [Field k] [CommRing A] [Algebra k A]
  [CommRing B] [Algebra k B]

/-- Idempotents are trivial when the prime spectrum is connected. -/
lemma eq_zero_or_eq_one_of_isIdempotentElem {R : Type u} [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {e : R} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  let c := PrimeSpectrum.isIdempotentElemEquivClopens ⟨e, he⟩
  obtain hc | hc := ((connectedSpace_iff_clopen (α := PrimeSpectrum R)).mp
    (by infer_instance)).2 c c.isClopen
  · left
    have hcbot : c = ⊥ := SetLike.ext' (by simpa using hc)
    have h := congrArg PrimeSpectrum.isIdempotentElemEquivClopens.symm hcbot
    rw [OrderIso.symm_apply_apply, PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot] at h
    exact congrArg Subtype.val h
  · right
    have hctop : c = ⊤ := SetLike.ext' (by simpa using hc)
    have h := congrArg PrimeSpectrum.isIdempotentElemEquivClopens.symm hctop
    rw [OrderIso.symm_apply_apply, PrimeSpectrum.isIdempotentElemEquivClopens_symm_top] at h
    exact congrArg Subtype.val h

/-- Purely inseparable scalar extension does not change connectedness of an affine spectrum. -/
lemma connectedSpace_tensorProduct_left_iff_of_isPurelyInseparable
    (K R : Type u) [Field K] [Algebra k K] [IsPurelyInseparable k K]
    [CommRing R] [Algebra k R] :
    ConnectedSpace (PrimeSpectrum (K ⊗[k] R)) ↔ ConnectedSpace (PrimeSpectrum R) := by
  let e := Algebra.TensorProduct.comm k R K
  let hcomm := PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective
  let hpure := PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k K R
  exact hcomm.homeomorph.connectedSpace_iff.trans hpure.homeomorph.connectedSpace_iff

/-- Tensor products of connected finite-type algebras over an algebraically closed field have
connected spectrum. -/
lemma connectedSpace_tensorProduct_of_isAlgClosed [IsAlgClosed k]
    [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    [ConnectedSpace (PrimeSpectrum A)] [ConnectedSpace (PrimeSpectrum B)] :
    ConnectedSpace (PrimeSpectrum (A ⊗[k] B)) := by
  let _ : ConnectedSpace ↥(Spec (.of A)) :=
    (specPrimeSpectrumHomeomorph A).connectedSpace_iff.mpr inferInstance
  let _ : ConnectedSpace ↥(Spec (.of B)) :=
    (specPrimeSpectrumHomeomorph B).connectedSpace_iff.mpr inferInstance
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let g := Spec.map (CommRingCat.ofHom (algebraMap k B))
  let _ : LocallyOfFiniteType f := by
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  let _ : LocallyOfFiniteType g := by
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  rw [← (specPrimeSpectrumHomeomorph (A ⊗[k] B)).connectedSpace_iff]
  rw [← (Scheme.homeoOfIso (pullbackSpecIso k A B)).connectedSpace_iff]
  exact connectedSpace_pullback_of_isAlgClosed f g

/-- Tensor products of finite-type domains over a separably closed field have connected
spectrum. The scalar extensions may be nonreduced when the base field is imperfect. -/
lemma connectedSpace_tensorProduct_of_isSepClosed_of_finiteType [IsSepClosed k]
    [IsDomain A] [IsDomain B] [Algebra.FiniteType k A] [Algebra.FiniteType k B] :
    ConnectedSpace (PrimeSpectrum (A ⊗[k] B)) := by
  let K := AlgebraicClosure k
  let _ : ConnectedSpace (PrimeSpectrum A) := inferInstance
  let _ : ConnectedSpace (PrimeSpectrum B) := inferInstance
  let _ : ConnectedSpace (PrimeSpectrum (K ⊗[k] A)) :=
    (connectedSpace_tensorProduct_left_iff_of_isPurelyInseparable k K A).mpr inferInstance
  let _ : ConnectedSpace (PrimeSpectrum (K ⊗[k] B)) :=
    (connectedSpace_tensorProduct_left_iff_of_isPurelyInseparable k K B).mpr inferInstance
  let _ : Algebra.FiniteType K (K ⊗[k] A) := Algebra.FiniteType.baseChange K
  let _ : Algebra.FiniteType K (K ⊗[k] B) := Algebra.FiniteType.baseChange K
  have hprod : ConnectedSpace
      (PrimeSpectrum ((K ⊗[k] A) ⊗[K] (K ⊗[k] B))) :=
    connectedSpace_tensorProduct_of_isAlgClosed K (K ⊗[k] A) (K ⊗[k] B)
  let e := Algebra.TensorProduct.baseChangeTensorProductEquiv k K A B
  have he := PrimeSpectrum.isHomeomorph_comap_of_bijective
    (f := e.toRingEquiv.toRingHom) e.bijective
  have hbase : ConnectedSpace (PrimeSpectrum (K ⊗[k] (A ⊗[k] B))) :=
    he.homeomorph.connectedSpace_iff.mpr hprod
  exact (connectedSpace_tensorProduct_left_iff_of_isPurelyInseparable
    k K (A ⊗[k] B)).mp hbase

/-- Every idempotent in the tensor product of two extension fields of a separably closed field is
trivial. The extension fields may be arbitrary, including transcendental extensions. -/
lemma eq_zero_or_eq_one_of_isIdempotentElem_tensorProduct_fields [IsSepClosed k]
    (K L : Type u) [Field K] [Field L] [Algebra k K] [Algebra k L]
    {x : K ⊗[k] L} (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  classical
  obtain ⟨n, a, b, hab⟩ := TensorProduct.exists_sum_tmul_eq x
  let A := Algebra.adjoin k (Set.range a)
  let B := Algebra.adjoin k (Set.range b)
  let a' : Fin n → A := fun i ↦ ⟨a i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  let b' : Fin n → B := fun i ↦ ⟨b i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  let y : A ⊗[k] B := ∑ i, a' i ⊗ₜ[k] b' i
  let F : A ⊗[k] B →ₐ[k] K ⊗[k] L := Algebra.TensorProduct.map A.val B.val
  let _ : Module.Free k K := Module.Free.of_divisionRing k K
  let _ : Module.Free k B := Module.Free.of_divisionRing k B
  let _ : Module.Flat k K := Module.Flat.of_free
  let _ : Module.Flat k B := Module.Flat.of_free
  have hF : Function.Injective F := by
    change Function.Injective
      (TensorProduct.map A.val.toLinearMap B.val.toLinearMap)
    exact TensorProduct.map_injective_of_flat_flat _ _
      Subtype.val_injective Subtype.val_injective
  have hFy : F y = x := by
    rw [hab]
    simp only [F, y, map_sum, Algebra.TensorProduct.map_tmul]
    rfl
  have hy : IsIdempotentElem y := by
    rw [isIdempotentElem_iff]
    apply hF
    simpa only [map_mul, hFy] using (isIdempotentElem_iff.mp hx)
  let _ : Algebra.FiniteType k A :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range a)
  let _ : Algebra.FiniteType k B :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range b)
  let _ : ConnectedSpace (PrimeSpectrum (A ⊗[k] B)) :=
    connectedSpace_tensorProduct_of_isSepClosed_of_finiteType k A B
  obtain hy0 | hy1 := eq_zero_or_eq_one_of_isIdempotentElem hy
  · left
    exact hFy.symm.trans (by simpa only [map_zero] using congrArg F hy0)
  · right
    exact hFy.symm.trans (by simpa only [map_one] using congrArg F hy1)

/-- The tensor product of any two extension fields of a separably closed field has connected
prime spectrum. No algebraicity or finite-generation hypothesis is required. This is the
field-extension case underlying the Stacks Project's tag 037U; it does not assert the
corresponding result for arbitrary connected algebras. -/
lemma connectedSpace_tensorProduct_fields [IsSepClosed k]
    (K L : Type u) [Field K] [Field L] [Algebra k K] [Algebra k L] :
    ConnectedSpace (PrimeSpectrum (K ⊗[k] L)) := by
  rw [connectedSpace_iff_clopen]
  refine ⟨by infer_instance, fun s hs ↦ ?_⟩
  let c : TopologicalSpace.Clopens (PrimeSpectrum (K ⊗[k] L)) := ⟨s, hs⟩
  let e := PrimeSpectrum.isIdempotentElemEquivClopens.symm c
  obtain he0 | he1 := eq_zero_or_eq_one_of_isIdempotentElem_tensorProduct_fields
    k K L e.2
  · left
    have heq : e = PrimeSpectrum.isIdempotentElemEquivClopens.symm ⊥ := by
      rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot]
      exact Subtype.ext he0
    have hc : c = ⊥ := (PrimeSpectrum.isIdempotentElemEquivClopens.apply_symm_apply c).symm.trans
      (congrArg PrimeSpectrum.isIdempotentElemEquivClopens heq |>.trans
        (PrimeSpectrum.isIdempotentElemEquivClopens.apply_symm_apply ⊥))
    exact congrArg (fun d : TopologicalSpace.Clopens (PrimeSpectrum (K ⊗[k] L)) ↦
      (d : Set (PrimeSpectrum (K ⊗[k] L)))) hc
  · right
    have heq : e = PrimeSpectrum.isIdempotentElemEquivClopens.symm ⊤ := by
      rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_top]
      exact Subtype.ext he1
    have hc : c = ⊤ := (PrimeSpectrum.isIdempotentElemEquivClopens.apply_symm_apply c).symm.trans
      (congrArg PrimeSpectrum.isIdempotentElemEquivClopens heq |>.trans
        (PrimeSpectrum.isIdempotentElemEquivClopens.apply_symm_apply ⊤))
    exact congrArg (fun d : TopologicalSpace.Clopens (PrimeSpectrum (K ⊗[k] L)) ↦
      (d : Set (PrimeSpectrum (K ⊗[k] L)))) hc

end PrimeSpectrum

namespace AlgebraicGeometry

universe u

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The spectrum of an arbitrary extension field of a separably closed field is geometrically
connected over the base, as in the Stacks Project, tag 037U. -/
lemma geometricallyConnected_SpecMap_of_isSepClosed [IsSepClosed k] :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  refine ⟨?_⟩
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro L _ _
  rw [(Scheme.homeoOfIso (pullbackSpecIso k K L)).connectedSpace_iff]
  rw [(PrimeSpectrum.specPrimeSpectrumHomeomorph (K ⊗[k] L)).connectedSpace_iff]
  exact PrimeSpectrum.connectedSpace_tensorProduct_fields k K L

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Every connected scheme over a separably closed field is geometrically connected.

No finite-type, reducedness, irreducibility, separation, properness, algebraicity or
rational-point hypothesis is required. The statement uses the same universe for the base field,
its extension fields and the scheme, following Mathlib's geometric API. The scheme-level
argument follows the Stacks Project's connected-fiber and open-projection route (tags 0386,
0385 and 0363), using the field-extension case of tag 037U. -/
lemma geometricallyConnected_of_isSepClosed [IsSepClosed k] [ConnectedSpace X] :
    GeometricallyConnected f := by
  refine ⟨?_⟩
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro L _ _
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let _ : GeometricallyConnected g := geometricallyConnected_SpecMap_of_isSepClosed k L
  infer_instance

end AlgebraicGeometry
