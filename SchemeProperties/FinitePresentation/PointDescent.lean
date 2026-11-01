/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.Adjoin.FG
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Descent of scheme points to finitely generated subalgebras

Let `K → R → S` be a tower of commutative rings with its given `K`-algebra structures.
If `X` is locally of finite type over `Spec K`, every `S`-point of `X` over
`Spec K` comes from a point over a finitely generated `R`-subalgebra of `S`.
The forward map is `algSpec` applied to the subalgebra inclusion, and its
composite with the descended point equals the original point in the over category.
Neither the map `R → S` nor `K → R` is required to be injective or of finite type.
There are no affineness or quasi-compactness assumptions on `X`.

The private construction uses the inclusion preorder of finitely generated subalgebras.
Its ring cocone has vertex the original `S` and legs the subtype inclusions. Singleton
coverage and injectivity of those legs give a type colimit by the filtered-colimit
criterion; reflection by the forgetful functor gives a colimit of the same ring cocone.
The `Γ-Spec` adjunction then gives a limit with vertex the original `Spec S`.
Finite generation in affine charts supplies local factors over localized subalgebras.
Injectivity of the localized inclusions descends every relation. The affine-transition
limit theorem makes the finitely many overlap equations hold at a common stage;
the local factors then glue. No separatedness assumption is imposed on `X`.

This finite-type assertion concerns the subalgebra inclusion diagram. It does not assert
preservation of arbitrary filtered algebra colimits under local finite type. The more
general finite-presentation limit theorem in Mathlib retains its original hypotheses.

## Main result

* `Scheme.exists_algSpec_map_subalgebra_val_comp_eq_of_locallyOfFiniteType`
* `Scheme.exists_algSpec_map_subalgebra_inclusion_comp_eq_of_locallyOfFiniteType`
* `Scheme.exists_algSpec_map_subalgebra_val_comp_eq_of_locallyOfFinitePresentation`

## References

* Mathlib, `Mathlib.AlgebraicGeometry.AffineTransitionLimit`, especially
  `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` and its restricted-open
  limit construction; Mathlib's principal-open localization isomorphisms and
  `Scheme.Cover.glueMorphisms`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

universe k r w

section LocalizedAlgebra

variable (K : Type k) {R : Type r} {S : Type u} {B : Type w}
  [CommRing K] [CommRing R] [CommRing S] [CommRing B]
  [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
  [Algebra K B]

private instance (A : Subalgebra R S) (s : A) :
    IsLocalization.Away ((A.val.restrictScalars K) s) (Localization.Away (s : S)) := by
  change IsLocalization.Away (s : S) (Localization.Away (s : S))
  infer_instance

private instance (A C : Subalgebra R S) (hAC : A ≤ C) (s : A) :
    IsLocalization.Away (((Subalgebra.inclusion hAC).restrictScalars K) s)
      (Localization.Away (⟨s, hAC s.2⟩ : C)) := by
  change IsLocalization.Away (⟨s, hAC s.2⟩ : C) (Localization.Away (⟨s, hAC s.2⟩ : C))
  infer_instance

private instance (A : Subalgebra R S) (s : S) (hs : s ∈ A) :
    IsLocalization.Away ((A.val.restrictScalars K) (⟨s, hs⟩ : A)) (Localization.Away s) := by
  change IsLocalization.Away s (Localization.Away s)
  infer_instance

private instance (A C : Subalgebra R S) (hAC : A ≤ C) (s : S) (hs : s ∈ A) :
    IsLocalization.Away (((Subalgebra.inclusion hAC).restrictScalars K) (⟨s, hs⟩ : A))
      (Localization.Away (⟨s, hAC hs⟩ : C)) := by
  change IsLocalization.Away (⟨s, hAC hs⟩ : C) (Localization.Away (⟨s, hAC hs⟩ : C))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- A finite-type K-algebra map into S[1/s] factors through A[1/s] for
some FG R-subalgebra A of S containing any given FG anchor. -/
private lemma exists_fgSubalgebra_factor_localizationAway
    [Algebra.FiniteType K B] (s : S)
    (φ : B →ₐ[K] Localization.Away s)
    (A0 : Subalgebra R S) (hA0 : A0.FG) :
    ∃ (A : Subalgebra R S), A0 ≤ A ∧ A.FG ∧
      ∃ (hs : s ∈ A) (ψ : B →ₐ[K] Localization.Away (⟨s, hs⟩ : A)),
        ∀ b, IsLocalization.Away.mapₐ
          (Localization.Away (⟨s, hs⟩ : A)) (Localization.Away s)
          (A.val.restrictScalars K) (⟨s, hs⟩ : A) (ψ b) = φ b := by
  classical
  obtain ⟨t, ht⟩ := (inferInstance : Algebra.FiniteType K B).out
  let num : B → S := fun b ↦ (IsLocalization.Away.sec s (φ b)).1
  let q : Finset S := insert s (t.image num)
  let A : Subalgebra R S := A0 ⊔ Algebra.adjoin R (q : Set S)
  have hA : A.FG := hA0.sup (Subalgebra.fg_adjoin_finset q)
  have hs : s ∈ A := by
    apply (show Algebra.adjoin R (q : Set S) ≤ A from le_sup_right)
    apply Algebra.subset_adjoin
    exact Finset.mem_insert_self _ _
  have hnum (b : B) (hb : b ∈ t) : num b ∈ A := by
    apply (show Algebra.adjoin R (q : Set S) ≤ A from le_sup_right)
    apply Algebra.subset_adjoin
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  let sa : A := ⟨s, hs⟩
  let f : Localization.Away sa →ₐ[K] Localization.Away s :=
    IsLocalization.Away.mapₐ (Localization.Away sa) (Localization.Away s)
      (A.val.restrictScalars K) sa
  have hf : Function.Injective f :=
    IsLocalization.Away.mapₐ_injective_of_injective
      (Aₚ := Localization.Away sa) (Bₚ := Localization.Away s)
      (f := A.val.restrictScalars K) sa Subtype.val_injective
  have hgen (b : B) (hb : b ∈ t) : φ b ∈ f.range := by
    let n : ℕ := (IsLocalization.Away.sec s (φ b)).2
    let ab : A := ⟨num b, hnum b hb⟩
    let d : Submonoid.powers sa := ⟨sa ^ n, ⟨n, rfl⟩⟩
    refine f.mem_range.mpr ⟨IsLocalization.mk' (Localization.Away sa) ab d, ?_⟩
    change IsLocalization.Away.mapₐ (Localization.Away sa) (Localization.Away s)
      (A.val.restrictScalars K) sa
      (IsLocalization.mk' (Localization.Away sa) ab d) = φ b
    let : IsLocalization.Away ((A.val.restrictScalars K).toRingHom sa)
        (Localization.Away s) := by
      change IsLocalization.Away s (Localization.Away s)
      infer_instance
    rw [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
      IsLocalization.map_mk']
    apply IsLocalization.mk'_eq_iff_eq_mul.mpr
    change algebraMap S (Localization.Away s) (num b) =
      φ b * algebraMap S (Localization.Away s) (↑(sa ^ n) : S)
    rw [Subalgebra.coe_pow]
    exact (IsLocalization.Away.sec_spec s (φ b)).symm
  have htop : (⊤ : Subalgebra K B) ≤ f.range.comap φ := by
    rw [← ht]
    exact Algebra.adjoin_le_iff.mpr fun b hb ↦ hgen b hb
  have hφ : ∀ b, φ b ∈ f.range := fun b ↦ htop (Algebra.mem_top (x := b))
  let e : Localization.Away sa ≃ₐ[K] f.range := AlgEquiv.ofInjective f hf
  let ψ : B →ₐ[K] Localization.Away sa :=
    e.symm.toAlgHom.comp (φ.codRestrict f.range hφ)
  refine ⟨A, le_sup_left, hA, hs, ψ, ?_⟩
  intro b
  change f (e.symm ((φ.codRestrict f.range hφ) b)) = φ b
  exact congrArg (fun z : f.range ↦ (z : Localization.Away s))
    (e.apply_symm_apply ((φ.codRestrict f.range hφ) b))

set_option backward.isDefEq.respectTransparency false in
/-- Pushing a factorization to a larger subalgebra retains the same original map.
No FG condition on either stage, and no finite-type condition on B, is needed here. -/
private lemma localizationAway_factor_pushup
    (A C : Subalgebra R S) (hAC : A ≤ C) (s : S) (hs : s ∈ A)
    (φ : B →ₐ[K] Localization.Away s)
    (ψ : B →ₐ[K] Localization.Away (⟨s, hs⟩ : A))
    (hψ : ∀ b, IsLocalization.Away.mapₐ
      (Localization.Away (⟨s, hs⟩ : A)) (Localization.Away s)
      (A.val.restrictScalars K) (⟨s, hs⟩ : A) (ψ b) = φ b) :
    ∃ (ψC : B →ₐ[K] Localization.Away (⟨s, hAC hs⟩ : C)),
      ∀ b, IsLocalization.Away.mapₐ
        (Localization.Away (⟨s, hAC hs⟩ : C)) (Localization.Away s)
        (C.val.restrictScalars K) (⟨s, hAC hs⟩ : C) (ψC b) = φ b := by
  let sa : A := ⟨s, hs⟩
  let sc : C := ⟨s, hAC hs⟩
  let fA : Localization.Away sa →ₐ[K] Localization.Away s :=
    IsLocalization.Away.mapₐ (Localization.Away sa) (Localization.Away s)
      (A.val.restrictScalars K) sa
  let fC : Localization.Away sc →ₐ[K] Localization.Away s :=
    IsLocalization.Away.mapₐ (Localization.Away sc) (Localization.Away s)
      (C.val.restrictScalars K) sc
  let u : Localization.Away sa →ₐ[K] Localization.Away sc :=
    IsLocalization.Away.mapₐ (Localization.Away sa) (Localization.Away sc)
      ((Subalgebra.inclusion hAC).restrictScalars K) sa
  have hcomp : fC.comp u = fA := by
    apply IsLocalization.algHom_ext (Submonoid.powers sa)
    apply AlgHom.ext
    intro a
    change fC (u (algebraMap A (Localization.Away sa) a)) =
      fA (algebraMap A (Localization.Away sa) a)
    simp only [fC, u, fA, IsLocalization.Away.mapₐ_apply,
      IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  refine ⟨u.comp ψ, ?_⟩
  intro b
  change fC (u (ψ b)) = φ b
  exact (congrArg (fun q : Localization.Away sa →ₐ[K] Localization.Away s ↦ q (ψ b))
    hcomp).trans (hψ b)

end LocalizedAlgebra

namespace AlgebraicGeometry

section RingDiagram

variable (R : Type v) (S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private abbrev FGSubalgebra := { A : Subalgebra R S // A.FG }

private instance : Nonempty (FGSubalgebra R S) :=
  ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

private instance : IsDirectedOrder (FGSubalgebra R S) where
  directed A B :=
    ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩,
      (show A.1 ≤ A.1 ⊔ B.1 from le_sup_left),
      (show B.1 ≤ A.1 ⊔ B.1 from le_sup_right)⟩

private def fgSubalgebraDiagram : FGSubalgebra R S ⥤ CommRingCat.{u} where
  obj A := CommRingCat.of A.1
  map f := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom
  map_id A := by ext a; rfl
  map_comp f g := by ext a; rfl

private def fgSubalgebraCocone : Cocone (fgSubalgebraDiagram R S) where
  pt := CommRingCat.of S
  ι :=
    { app A := CommRingCat.ofHom A.1.val.toRingHom
      naturality {A B} f := by ext a; rfl }

private noncomputable def fgSubalgebraTypesIsColimit :
    IsColimit ((forget CommRingCat).mapCocone (fgSubalgebraCocone R S)) := by
  classical
  apply Types.FilteredColimit.isColimitOf'
  · intro s
    change S at s
    refine ⟨⟨Algebra.adjoin R (↑({s} : Finset S) : Set S),
      Subalgebra.fg_adjoin_finset _⟩,
      ⟨s, Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_singleton_self s))⟩,
      rfl⟩
  · intro A a b h
    change A.1 at a b
    change (a : S) = (b : S) at h
    have hab : a = b := Subtype.ext h
    refine ⟨A, 𝟙 A, ?_⟩
    change a = b
    exact hab

private noncomputable def fgSubalgebraIsColimit :
    IsColimit (fgSubalgebraCocone R S) := by
  letI : ReflectsColimit (fgSubalgebraDiagram R S) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact isColimitOfReflects (forget CommRingCat) (fgSubalgebraTypesIsColimit R S)

private noncomputable def fgSubalgebraSpecDiagram : (FGSubalgebra R S)ᵒᵖ ⥤ Scheme.{u} :=
  (fgSubalgebraDiagram R S).op ⋙ Scheme.Spec

private noncomputable def fgSubalgebraSpecCone : Cone (fgSubalgebraSpecDiagram R S) :=
  Scheme.Spec.mapCone (fgSubalgebraCocone R S).op

private noncomputable def fgSubalgebraSpecIsLimit :
    IsLimit (fgSubalgebraSpecCone R S) :=
  isLimitOfPreserves Scheme.Spec (fgSubalgebraIsColimit R S).op

private instance (A : (FGSubalgebra R S)ᵒᵖ) :
    IsAffine ((fgSubalgebraSpecDiagram R S).obj A) := by
  dsimp [fgSubalgebraSpecDiagram, fgSubalgebraDiagram]
  infer_instance

private instance {A B : (FGSubalgebra R S)ᵒᵖ} (f : A ⟶ B) :
    IsAffineHom ((fgSubalgebraSpecDiagram R S).map f) := by
  dsimp [fgSubalgebraSpecDiagram]
  infer_instance

end RingDiagram

section ScalarTower

variable (K : Type u) {R : Type v} {S : Type u} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]

private lemma Scheme.specMap_algHom_comp {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (Spec (.of A) ↘ Spec (.of K)) =
      (Spec (.of B) ↘ Spec (.of K)) := by
  simpa only [specOverSpec_over, AlgHom.toRingHom_eq_coe,
    CommRingCat.ofHom_comp, Spec.map_comp] using
    congrArg (fun h : K →+* B ↦ Spec.map (CommRingCat.ofHom h)) f.comp_algebraMap

/-- The spectrum of a subalgebra inclusion respects the given `K`-structure.
The `K`-algebra structure on the stage is the inherited `Subalgebra.algebra'` structure. -/
private lemma Scheme.specMap_subalgebra_val_comp (A : Subalgebra R S) :
    Spec.map (CommRingCat.ofHom A.val.toRingHom) ≫ (Spec (.of A) ↘ Spec (.of K)) =
      (Spec (.of S) ↘ Spec (.of K)) := by
  simpa only [AlgHom.coe_restrictScalars, AlgHom.toRingHom_eq_coe, specOverSpec_over,
    CommRingCat.ofHom_comp, Spec.map_comp] using
    congrArg (fun h : K →+* S ↦ Spec.map (CommRingCat.ofHom h))
      (A.val.restrictScalars K).comp_algebraMap

private noncomputable def fgSubalgebraSpecBase : fgSubalgebraSpecDiagram R S ⟶
    (Functor.const (FGSubalgebra R S)ᵒᵖ).obj (Spec (.of K)) where
  app A := Spec.map (CommRingCat.ofHom (algebraMap K A.unop.1))
  naturality {A B} f := by
    change Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion (leOfHom f.unop)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K B.unop.1)) =
      Spec.map (CommRingCat.ofHom (algebraMap K A.unop.1)) ≫ 𝟙 _
    simpa only [AlgHom.coe_restrictScalars, AlgHom.toRingHom_eq_coe, Category.comp_id,
      CommRingCat.ofHom_comp, Spec.map_comp] using
      congrArg (fun h : K →+* A.unop.1 ↦ Spec.map (CommRingCat.ofHom h))
        ((Subalgebra.inclusion (leOfHom f.unop)).restrictScalars K).comp_algebraMap

/- Equality on a quasi-compact overlap can be made true at an inclusion stage.
The limit here is the restriction of the original spectrum limit. -/
set_option backward.isDefEq.respectTransparency false in
private lemma Scheme.exists_overlap_stage_of_locallyOfFiniteType
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))]
    (A : (FGSubalgebra R S)ᵒᵖ)
    (U : ((fgSubalgebraSpecDiagram R S).obj A).Opens) (hU : IsAffineOpen U)
    (a b : U.toScheme ⟶ X)
    (ha : a ≫ (X ↘ Spec (.of K)) = U.ι ≫ (fgSubalgebraSpecBase K).app A)
    (hb : b ≫ (X ↘ Spec (.of K)) = U.ι ≫ (fgSubalgebraSpecBase K).app A)
    (hab : ((fgSubalgebraSpecCone R S).π.app A ∣_ U) ≫ a =
      ((fgSubalgebraSpecCone R S).π.app A ∣_ U) ≫ b) :
    ∃ (B : (FGSubalgebra R S)ᵒᵖ) (f : B ⟶ A),
      ((fgSubalgebraSpecDiagram R S).map f ∣_ U) ≫ a =
        ((fgSubalgebraSpecDiagram R S).map f ∣_ U) ≫ b := by
  let D := fgSubalgebraSpecDiagram R S
  let c := fgSubalgebraSpecCone R S
  let D' := opensDiagram D A U
  let c' := opensCone D c A U
  let t' : D' ⟶ (Functor.const _).obj (Spec (.of K)) :=
    opensDiagramι D A U ≫ Functor.whiskerLeft (Over.forget A) (fgSubalgebraSpecBase K)
  let e : D'.obj (Over.mk (𝟙 A)) ≅ U := (D.map (𝟙 A)).preimageIso U
  have hc : IsLimit c' := isLimitOpensCone D c (fgSubalgebraSpecIsLimit R S) A U
  let : ∀ j, CompactSpace (D'.obj j) := fun j ↦
    isCompact_iff_compactSpace.mp (hU.preimage (D.map j.hom)).isCompact
  have he : e.hom ≫ U.ι = (D.map (𝟙 A) ⁻¹ᵁ U).ι ≫ D.map (𝟙 A) :=
    Scheme.Hom.preimageIso_hom_ι (D.map (𝟙 A)) U
  have hπ : c'.π.app (Over.mk (𝟙 A)) ≫ e.hom = c.π.app A ∣_ U := by
    rw [← cancel_mono U.ι, Category.assoc, he]
    dsimp only [c', opensCone]
    simp only [Over.mk_left, Over.mk_hom]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, D.map_id, Category.comp_id,
      morphismRestrict_ι]
  obtain ⟨j, f, hf⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    D' t' (X ↘ Spec (.of K)) c' hc (e.hom ≫ a) (e.hom ≫ b)
    (by simp [t', e, Category.assoc, ha])
    (by simp [t', e, Category.assoc, hb])
    (by
      change (c'.π.app (Over.mk (𝟙 A)) ≫ e.hom) ≫ a =
        (c'.π.app (Over.mk (𝟙 A)) ≫ e.hom) ≫ b
      rw [hπ]
      exact hab)
  have hleft : f.left = j.hom := by simpa using f.w
  have hf' : D'.map f ≫ e.hom = D.map j.hom ∣_ U := by
    rw [← cancel_mono U.ι, Category.assoc, he]
    dsimp only [D', opensDiagram]
    simp only [Over.mk_left, Over.mk_hom]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, D.map_id, Category.comp_id,
      hleft, morphismRestrict_ι]
  refine ⟨j.left, j.hom, ?_⟩
  change (D.map j.hom ∣_ U) ≫ a = (D.map j.hom ∣_ U) ≫ b
  rw [← hf']
  exact hf

set_option backward.isDefEq.respectTransparency false in
private lemma Scheme.exists_principal_chart_point
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))]
    (x : (Spec (.of S)).asOver (Spec (.of K)) ⟶ X.asOver (Spec (.of K)))
    (p : Spec (.of S)) :
    ∃ (s : S) (B : CommAlgCat.{u, u} K), Algebra.FiniteType K B ∧
      ∃ (y : (algSpec (.of K)).obj (op B) ⟶ X.asOver (Spec (.of K)))
        (φ : B →ₐ[K] Localization.Away s),
        p ∈ PrimeSpectrum.basicOpen s ∧
          Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ y.left =
            Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s))) ≫ x.left := by
  classical
  let 𝒰 := X.affineOpenCover
  let i := 𝒰.idx (x.left p)
  have hp : p ∈ x.left ⁻¹ᵁ (𝒰.f i).opensRange := 𝒰.covers (x.left p)
  obtain ⟨_, ⟨s, rfl⟩, hps, hs⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) hp
  let ρ := Spec.preimage (𝒰.f i ≫ (X ↘ Spec (.of K)))
  let _ : Algebra K (𝒰.X i) := ρ.hom.toAlgebra
  have hft : Algebra.FiniteType K (𝒰.X i) := by
    rw [← RingHom.finiteType_algebraMap]
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    simpa only [ρ, Spec.map_preimage] using
      (inferInstance : LocallyOfFiniteType (𝒰.f i ≫ (X ↘ Spec (.of K))))
  let B : CommAlgCat.{u, u} K := .of K (𝒰.X i)
  let y : (algSpec (.of K)).obj (op B) ⟶ X.asOver (Spec (.of K)) :=
    Over.homMk (𝒰.f i) (by
      rw [algSpec_obj_hom]
      change 𝒰.f i ≫ (X ↘ Spec (.of K)) = Spec.map ρ
      exact (Spec.map_preimage _).symm)
  let f₀ : Spec (.of (Localization.Away s)) ⟶ Spec (.of B) :=
    (basicOpenIsoSpecAway (R := .of S) s).inv ≫ x.left.resLE _ (PrimeSpectrum.basicOpen s) hs ≫
      (𝒰.f i).isoOpensRange.inv
  have hf₀ : f₀ ≫ y.left =
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s))) ≫ x.left := by
    change f₀ ≫ 𝒰.f i = _
    dsimp only [f₀]
    rw [Category.assoc, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp,
      Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      ← basicOpenIsoSpecAway_hom_SpecMap (R := .of S) s]
    simp
  let φ₀ := Spec.preimage f₀
  have hbase : f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away s))) := by
    have hybase : Spec.map (CommRingCat.ofHom (algebraMap K B)) =
        𝒰.f i ≫ (X ↘ Spec (.of K)) := Spec.map_preimage _
    rw [hybase, ← Category.assoc]
    change (f₀ ≫ y.left) ≫ (X ↘ Spec (.of K)) = _
    rw [hf₀, Category.assoc]
    have hx : x.left ≫ (X ↘ Spec (.of K)) = (Spec (.of S) ↘ Spec (.of K)) := x.w
    rw [hx]
    exact Scheme.specMap_algHom_comp K (IsScalarTower.toAlgHom K S (Localization.Away s))
  have hcomm : CommRingCat.ofHom (algebraMap K B) ≫ φ₀ =
      CommRingCat.ofHom (algebraMap K (Localization.Away s)) := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, φ₀, Spec.map_preimage] using hbase
  let φ : B →ₐ[K] Localization.Away s :=
    { φ₀.hom with commutes' := fun k ↦ congrArg (fun f : CommRingCat.of K ⟶
        CommRingCat.of (Localization.Away s) ↦ f k) hcomm }
  have hf : Spec.map (CommRingCat.ofHom φ.toRingHom) = f₀ := Spec.map_preimage f₀
  exact ⟨s, B, hft, y, φ, hps, hf ▸ hf₀⟩

/- Turning a factorization of a localized algebra map into a local scheme map
only uses the open immersion identifying a principal open with its localization. -/
set_option backward.isDefEq.respectTransparency false in
private lemma Scheme.exists_local_map_of_localized_factor
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    (x : Spec (.of S) ⟶ X) (A : Subalgebra R S) (s : A)
    (B : CommAlgCat.{u, u} K)
    (y : (algSpec (.of K)).obj (op B) ⟶ X.asOver (Spec (.of K)))
    (φ : B →ₐ[K] Localization.Away (s : S))
    (ψ : B →ₐ[K] Localization.Away s)
    (hψ : (IsLocalization.Away.mapₐ (Localization.Away s)
      (Localization.Away (s : S)) (A.val.restrictScalars K) s).comp ψ = φ)
    (hφ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ y.left =
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s : S)))) ≫ x) :
    ∃ a : Scheme.Opens.toScheme (X := Spec (.of A)) (PrimeSpectrum.basicOpen s) ⟶ X,
      a ≫ (X ↘ Spec (.of K)) =
        Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen s) ≫
          (Spec (.of A) ↘ Spec (.of K)) ∧
      (Spec.map (CommRingCat.ofHom A.val.toRingHom) ∣_ PrimeSpectrum.basicOpen s) ≫ a =
        (Spec.map (CommRingCat.ofHom A.val.toRingHom) ⁻¹ᵁ PrimeSpectrum.basicOpen s).ι ≫ x := by
  let U : (Spec (.of A)).Opens := PrimeSpectrum.basicOpen s
  let v := Spec.map (CommRingCat.ofHom A.val.toRingHom)
  let pA := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s)))
  let pS := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s : S))))
  let ℓ := IsLocalization.Away.mapₐ (Localization.Away s)
    (Localization.Away (s : S)) (A.val.restrictScalars K) s
  have hsquare : Spec.map (CommRingCat.ofHom ℓ.toRingHom) ≫ pA = pS ≫ v := by
    dsimp [pA, pS, v]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    let : IsLocalization.Away ((A.val.restrictScalars K).toRingHom s)
        (Localization.Away (s : S)) := by
      change IsLocalization.Away (s : S) (Localization.Away (s : S))
      infer_instance
    change IsLocalization.Away.map (Localization.Away s) (Localization.Away (s : S))
      (A.val.restrictScalars K).toRingHom s (algebraMap A (Localization.Away s) a) =
        algebraMap S (Localization.Away (s : S)) (a : S)
    rw [IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  have hrange : Set.range pS = Set.range (v ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    change Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away (s : S)))) =
      (PrimeSpectrum.comap A.val.toRingHom) ⁻¹' (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum A))
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away (s : S)) (s : S)
  let e : Spec (.of (Localization.Away (s : S))) ≅ (v ⁻¹ᵁ U) :=
    IsOpenImmersion.isoOfRangeEq pS (v ⁻¹ᵁ U).ι hrange
  have hAι : (basicOpenIsoSpecAway (R := .of A) s).hom ≫ pA = U.ι :=
    basicOpenIsoSpecAway_hom_SpecMap (R := .of A) s
  have he : e.hom ≫ (v ∣_ U) ≫ (basicOpenIsoSpecAway (R := .of A) s).hom =
      Spec.map (CommRingCat.ofHom ℓ.toRingHom) := by
    rw [← cancel_mono pA]
    calc
      (e.hom ≫ (v ∣_ U) ≫ (basicOpenIsoSpecAway (R := .of A) s).hom) ≫ pA =
          e.hom ≫ (v ∣_ U) ≫ U.ι := by
            simp only [Category.assoc, hAι]
      _ = e.hom ≫ (v ⁻¹ᵁ U).ι ≫ v := by rw [morphismRestrict_ι]
      _ = pS ≫ v := by simp only [e, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
      _ = Spec.map (CommRingCat.ofHom ℓ.toRingHom) ≫ pA := hsquare.symm
  let a : U.toScheme ⟶ X :=
    (basicOpenIsoSpecAway (R := .of A) s).hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ y.left
  refine ⟨a, ?_, ?_⟩
  · have hy := y.w
    change y.left ≫ (X ↘ Spec (.of K)) =
      Spec.map (CommRingCat.ofHom (algebraMap K B)) at hy
    have hψbase := Scheme.specMap_algHom_comp K ψ
    have hpAbase := Scheme.specMap_algHom_comp K
      (IsScalarTower.toAlgHom K A (Localization.Away s))
    change a ≫ (X ↘ Spec (.of K)) = U.ι ≫ (Spec (.of A) ↘ Spec (.of K))
    dsimp only [a]
    rw [Category.assoc, Category.assoc, hy]
    change (basicOpenIsoSpecAway (R := .of A) s).hom ≫
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        (Spec (.of B) ↘ Spec (.of K)) = _
    rw [hψbase, ← hpAbase]
    change ((basicOpenIsoSpecAway (R := .of A) s).hom ≫ pA) ≫
      (Spec (.of A) ↘ Spec (.of K)) = U.ι ≫ (Spec (.of A) ↘ Spec (.of K))
    rw [hAι]
  · change (v ∣_ U) ≫ a = (v ⁻¹ᵁ U).ι ≫ x
    rw [← cancel_epi e.hom]
    have hmaps : Spec.map (CommRingCat.ofHom ℓ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ψ.toRingHom) =
          Spec.map (CommRingCat.ofHom φ.toRingHom) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun f : B →ₐ[K] Localization.Away (s : S) ↦
        Spec.map (CommRingCat.ofHom f.toRingHom)) hψ
    calc
      e.hom ≫ (v ∣_ U) ≫ a =
          (e.hom ≫ (v ∣_ U) ≫ (basicOpenIsoSpecAway (R := .of A) s).hom) ≫
            Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ y.left := by simp [a, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom ℓ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ y.left := by rw [he]
      _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ y.left := by
        rw [← Category.assoc, hmaps]
      _ = pS ≫ x := hφ
      _ = e.hom ≫ (v ⁻¹ᵁ U).ι ≫ x := by simp [e]

/- A finite family of affine local factors suffices. The covering equation and
all overlap equations descend using the same spectrum cone. -/
set_option backward.isDefEq.respectTransparency false in
private lemma Scheme.exists_stage_of_finite_local_maps
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))]
    (x : Spec (.of S) ⟶ X)
    (A : (FGSubalgebra R S)ᵒᵖ) {E : Type u} [Finite E]
    (U : E → ((fgSubalgebraSpecDiagram R S).obj A).Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (a : ∀ i, (U i).toScheme ⟶ X)
    (ha : ∀ i, a i ≫ (X ↘ Spec (.of K)) =
      (U i).ι ≫ (fgSubalgebraSpecBase K).app A)
    (hax : ∀ i, ((fgSubalgebraSpecCone R S).π.app A ∣_ U i) ≫ a i =
      (((fgSubalgebraSpecCone R S).π.app A) ⁻¹ᵁ U i).ι ≫ x)
    (hcover : ⨆ i, ((fgSubalgebraSpecCone R S).π.app A) ⁻¹ᵁ U i = ⊤) :
    ∃ (B : (FGSubalgebra R S)ᵒᵖ) (g : (fgSubalgebraSpecDiagram R S).obj B ⟶ X),
      (fgSubalgebraSpecCone R S).π.app B ≫ g = x ∧
        g ≫ (X ↘ Spec (.of K)) = (fgSubalgebraSpecBase K).app B := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let D := fgSubalgebraSpecDiagram R S
  let c := fgSubalgebraSpecCone R S
  obtain ⟨B₀, f₀, hf₀⟩ := exists_map_eq_top D c (fgSubalgebraSpecIsLimit R S)
    (⨆ i, U i) (by simpa only [Scheme.Hom.preimage_iSup] using hcover)
  have hover : ∀ p : E × E, ∃ (B : (FGSubalgebra R S)ᵒᵖ) (f : B ⟶ A),
      (D.map f ∣_ (U p.1 ⊓ U p.2)) ≫ (D.obj A).homOfLE inf_le_left ≫ a p.1 =
        (D.map f ∣_ (U p.1 ⊓ U p.2)) ≫ (D.obj A).homOfLE inf_le_right ≫ a p.2 := by
    intro p
    apply Scheme.exists_overlap_stage_of_locallyOfFiniteType K X A
      (U p.1 ⊓ U p.2) ((hU p.1).inf (hU p.2))
    · simp [Category.assoc, ha]
    · simp [Category.assoc, ha]
    · rw [morphismRestrict_homOfLE_assoc, morphismRestrict_homOfLE_assoc, hax, hax]
      simp only [← Category.assoc, Scheme.homOfLE_ι]
  choose B f hf using hover
  let T : Finset (FGSubalgebra R S)ᵒᵖ := {B₀} ∪ Finset.univ.image B
  obtain ⟨C, hC⟩ := IsCofiltered.inf_objs_exists T
  let q₀ : C ⟶ B₀ := (hC (X := B₀) (by simp [T])).some
  let q (p : E × E) : C ⟶ B p := (hC (X := B p) (by simp [T])).some
  let r : C ⟶ A := q₀ ≫ f₀
  let V (i : E) := D.map r ⁻¹ᵁ U i
  let b (i : E) : (V i).toScheme ⟶ X := (D.map r ∣_ U i) ≫ a i
  have hV : ⨆ i, V i = ⊤ := by
    dsimp only [V, r]
    rw [D.map_comp]
    simp only [Scheme.Hom.comp_preimage, ← Scheme.Hom.preimage_iSup, hf₀,
      Scheme.Hom.preimage_top]
  have hb : ∀ i j, (D.obj C).homOfLE (U := V i ⊓ V j) inf_le_left ≫ b i =
      (D.obj C).homOfLE inf_le_right ≫ b j := by
    intro i j
    have hr : r = q (i, j) ≫ f (i, j) := Subsingleton.elim _ _
    have H : (D.map r ∣_ (U i ⊓ U j)) ≫ (D.obj A).homOfLE inf_le_left ≫ a i =
        (D.map r ∣_ (U i ⊓ U j)) ≫ (D.obj A).homOfLE inf_le_right ≫ a j := by
      rw [hr, D.map_comp, morphismRestrict_comp]
      simpa only [Category.assoc] using congrArg (fun h ↦
        (D.map (q (i, j)) ∣_ (D.map (f (i, j)) ⁻¹ᵁ (U i ⊓ U j))) ≫ h) (hf (i, j))
    dsimp only [b, V]
    rw [← morphismRestrict_homOfLE_assoc (D.map r) (U i ⊓ U j) (U i) inf_le_left,
      ← morphismRestrict_homOfLE_assoc (D.map r) (U i ⊓ U j) (U j) inf_le_right]
    exact H
  let 𝒰 := Scheme.openCoverOfIsOpenCover (D.obj C) V hV
  have hb' : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ b i =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ b j := by
    intro i j
    change pullback.fst (V i).ι (V j).ι ≫ b i = pullback.snd (V i).ι (V j).ι ≫ b j
    rw [← cancel_epi (isPullback_opens_inf (V i) (V j)).isoPullback.hom]
    simpa only [IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_snd_assoc] using hb i j
  let g := 𝒰.glueMorphisms b hb'
  have hg : ∀ i, (V i).ι ≫ g = b i := 𝒰.ι_glueMorphisms b hb'
  refine ⟨C, g, ?_, ?_⟩
  · apply Scheme.Cover.hom_ext (𝒰.pullback₁ (c.π.app C))
    intro i
    change E at i
    change pullback.fst (c.π.app C) (V i).ι ≫ c.π.app C ≫ g =
      pullback.fst (c.π.app C) (V i).ι ≫ x
    rw [pullback.condition_assoc, hg]
    rw [← cancel_epi (pullbackRestrictIsoRestrict (c.π.app C) (V i)).inv]
    simp only [pullbackRestrictIsoRestrict_inv_fst_assoc]
    have H : (c.π.app C ∣_ V i) ≫ b i = (c.π.app C ⁻¹ᵁ V i).ι ≫ x := by
      have H₀ := hax i
      change (c.π.app A ∣_ U i) ≫ a i = (c.π.app A ⁻¹ᵁ U i).ι ≫ x at H₀
      rw [← c.w r, morphismRestrict_comp] at H₀
      simpa only [b, V, D, Scheme.Hom.comp_preimage, Category.assoc] using H₀
    change (c.π.app C ∣_ V i) ≫ b i = (c.π.app C ⁻¹ᵁ V i).ι ≫ x
    exact H
  · apply 𝒰.hom_ext
    intro i
    change E at i
    change (V i).ι ≫ g ≫ (X ↘ Spec (.of K)) =
      (V i).ι ≫ (fgSubalgebraSpecBase K).app C
    rw [← Category.assoc, hg]
    dsimp only [b]
    rw [Category.assoc, ha, ← Category.assoc, morphismRestrict_ι, Category.assoc]
    have ht : D.map r ≫ (fgSubalgebraSpecBase K).app A =
        (fgSubalgebraSpecBase K).app C := by
      have ht := (fgSubalgebraSpecBase K).naturality r
      change D.map r ≫ (fgSubalgebraSpecBase K).app A =
        (fgSubalgebraSpecBase K).app C ≫ 𝟙 (Spec (.of K)) at ht
      exact ht.trans (Category.comp_id ((fgSubalgebraSpecBase K).app C))
    exact congrArg (fun h ↦ (V i).ι ≫ h) ht

set_option backward.isDefEq.respectTransparency false in
/-- A point of a scheme locally of finite type over `Spec K` descends to a
finitely generated `R`-subalgebra of its coefficient algebra `S`.

The coefficient data are the given tower `K → R → S`: the stage inherits its
`K`-structure from the original `S`. The forward map is the `algSpec` map of
`A.val.restrictScalars K`, whose underlying ring map is the original inclusion `A → S`.
The equality is in the original over category, with the original point `x` on the right.
In particular, `algSpec_map_left` reads it back as
`Spec.map (CommRingCat.ofHom A.val.toRingHom) ≫ xA.left = x.left`.

Only the structural morphism of `X` is assumed locally of finite type;
`X` need not be affine or quasi-compact, and `R` need not be finitely generated over `K`. -/
theorem Scheme.exists_algSpec_map_subalgebra_val_comp_eq_of_locallyOfFiniteType
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))]
    (x : (Spec (.of S)).asOver (Spec (.of K)) ⟶ X.asOver (Spec (.of K))) :
    ∃ (A : Subalgebra R S), A.FG ∧
      ∃ (xA : (Spec (.of A)).asOver (Spec (.of K)) ⟶ X.asOver (Spec (.of K))),
        (algSpec (.of K)).map (CommAlgCat.ofHom (A.val.restrictScalars K)).op ≫ xA = x := by
  classical
  choose s B hB y φ hp hφ using
    Scheme.exists_principal_chart_point K X x
  let V : Spec (.of S) → (Spec (.of S)).Opens := fun p ↦ PrimeSpectrum.basicOpen (s p)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p : Spec (.of S) ↦ (V p).1) (fun p ↦ (V p).isOpen)
    (fun p _ ↦ Set.mem_iUnion.mpr ⟨p, hp p⟩)
  let E := ↥t
  have hcoverS : ⨆ i : E, PrimeSpectrum.basicOpen (s i.1) = ⊤ := by
    apply top_unique
    intro p _
    obtain ⟨q, hqt, hpq⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨q, hqt⟩, hpq⟩
  have hstage : ∀ i : E, ∃ (A : Subalgebra R S), A.FG ∧
      ∃ (hs : s i.1 ∈ A) (ψ : B i.1 →ₐ[K] Localization.Away (⟨s i.1, hs⟩ : A)),
        ∀ b, IsLocalization.Away.mapₐ
          (Localization.Away (⟨s i.1, hs⟩ : A)) (Localization.Away (s i.1))
          (A.val.restrictScalars K) (⟨s i.1, hs⟩ : A) (ψ b) = φ i.1 b := by
    intro i
    let : Algebra.FiniteType K (B i.1) := hB i.1
    obtain ⟨A, -, hA, hs, ψ, hψ⟩ :=
      exists_fgSubalgebra_factor_localizationAway K (R := R) (s i.1) (φ i.1) ⊥ Subalgebra.fg_bot
    exact ⟨A, hA, hs, ψ, hψ⟩
  choose A hA hs ψ hψ using hstage
  let T : Finset (FGSubalgebra R S) := Finset.univ.image fun i : E ↦ ⟨A i, hA i⟩
  obtain ⟨C, hC⟩ := IsFiltered.sup_objs_exists T
  let hAC (i : E) : A i ≤ C.1 :=
    leOfHom (hC (X := ⟨A i, hA i⟩) (by simp [T])).some
  choose ψC hψC using fun i : E ↦
    localizationAway_factor_pushup K (R := R) (A i) C.1 (hAC i) (s i.1) (hs i)
      (φ i.1) (ψ i) (hψ i)
  let sc (i : E) : C.1 := ⟨s i.1, hAC i (hs i)⟩
  let U (i : E) : (Spec (.of C.1)).Opens := PrimeSpectrum.basicOpen (sc i)
  have hlocal : ∀ i : E, ∃ a : (U i).toScheme ⟶ X,
      a ≫ (X ↘ Spec (.of K)) = (U i).ι ≫ (fgSubalgebraSpecBase K).app (op C) ∧
      ((fgSubalgebraSpecCone R S).π.app (op C) ∣_ U i) ≫ a =
        ((fgSubalgebraSpecCone R S).π.app (op C) ⁻¹ᵁ U i).ι ≫ x.left := by
    intro i
    apply Scheme.exists_local_map_of_localized_factor K X x.left C.1 (sc i)
      (B i.1) (y i.1) (φ i.1) (ψC i)
    · exact AlgHom.ext (hψC i)
    · exact hφ i.1
  choose a ha hax using hlocal
  obtain ⟨D, g, hg, hgbase⟩ := Scheme.exists_stage_of_finite_local_maps K X x.left
    (op C) U (fun i ↦ by
      exact IsAffineOpen.Spec_basicOpen (R := .of C.1) (sc i)) a ha hax
    (by
      change (⨆ i : E, PrimeSpectrum.basicOpen (s i.1)) = ⊤
      exact hcoverS)
  refine ⟨D.unop.1, D.unop.2, Over.homMk g hgbase, ?_⟩
  apply Over.OverMorphism.ext
  exact hg

/-- The locally finite-presentation specialization of relative point descent.
The stage, inherited coefficient structures and original inclusion map agree with
`Scheme.exists_algSpec_map_subalgebra_val_comp_eq_of_locallyOfFiniteType`. -/
theorem Scheme.exists_algSpec_map_subalgebra_val_comp_eq_of_locallyOfFinitePresentation
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFinitePresentation (X ↘ Spec (.of K))]
    (x : (Spec (.of S)).asOver (Spec (.of K)) ⟶ X.asOver (Spec (.of K))) :
    ∃ (A : Subalgebra R S), A.FG ∧
      ∃ (xA : (Spec (.of A)).asOver (Spec (.of K)) ⟶ X.asOver (Spec (.of K))),
        (algSpec (.of K)).map (CommAlgCat.ofHom (A.val.restrictScalars K)).op ≫ xA = x := by
  exact Scheme.exists_algSpec_map_subalgebra_val_comp_eq_of_locallyOfFiniteType K X x

set_option backward.isDefEq.respectTransparency false in
/-- Two points over finitely generated `R`-subalgebras of `S` that agree after
pullback to `S` agree after pullback to a common finitely generated subalgebra.

The points and their forward maps retain the given tower `K → R → S`. Only the
structural morphism of `X` is assumed locally of finite type; neither stage need
be finitely generated over `K`, and `X` need not be affine, quasi-compact, or separated.
This applies `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType` to the
spectrum diagram of finitely generated `R`-subalgebras of `S`. -/
theorem Scheme.exists_algSpec_map_subalgebra_inclusion_comp_eq_of_locallyOfFiniteType
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))]
    (A B : Subalgebra R S) (hA : A.FG) (hB : B.FG)
    (xA : (Spec (.of A)).asOver (Spec (.of K)) ⟶ X.asOver (Spec (.of K)))
    (xB : (Spec (.of B)).asOver (Spec (.of K)) ⟶ X.asOver (Spec (.of K)))
    (h : (algSpec (.of K)).map (CommAlgCat.ofHom (A.val.restrictScalars K)).op ≫ xA =
      (algSpec (.of K)).map (CommAlgCat.ofHom (B.val.restrictScalars K)).op ≫ xB) :
    ∃ (C : Subalgebra R S), C.FG ∧
      ∃ (hAC : A ≤ C) (hBC : B ≤ C),
        (algSpec (.of K)).map
            (CommAlgCat.ofHom ((Subalgebra.inclusion hAC).restrictScalars K)).op ≫ xA =
          (algSpec (.of K)).map
            (CommAlgCat.ofHom ((Subalgebra.inclusion hBC).restrictScalars K)).op ≫ xB := by
  have hab : (fgSubalgebraSpecCone R S).π.app (op ⟨A, hA⟩) ≫ xA.left =
      (fgSubalgebraSpecCone R S).π.app (op ⟨B, hB⟩) ≫ xB.left := by
    have hleft := congrArg
      (fun g : (Spec (.of S)).asOver (Spec (.of K)) ⟶ X.asOver (Spec (.of K)) ↦
        g.left) h
    change Spec.map (CommRingCat.ofHom A.val.toRingHom) ≫ xA.left =
      Spec.map (CommRingCat.ofHom B.val.toRingHom) ≫ xB.left at hleft
    exact hleft
  obtain ⟨C, hAC, hBC, heq⟩ :=
    Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
      (fgSubalgebraSpecDiagram R S) (fgSubalgebraSpecBase K) (X ↘ Spec (.of K))
      (fgSubalgebraSpecCone R S) (fgSubalgebraSpecIsLimit R S)
      (i := op ⟨A, hA⟩) xA.left
      (by
        change (Spec (.of A) ↘ Spec (.of K)) = xA.left ≫ (X ↘ Spec (.of K))
        exact xA.w.symm)
      (j := op ⟨B, hB⟩) xB.left
      (by
        change (Spec (.of B) ↘ Spec (.of K)) = xB.left ≫ (X ↘ Spec (.of K))
        exact xB.w.symm) hab
  refine ⟨C.unop.1, C.unop.2, leOfHom hAC.unop, leOfHom hBC.unop, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map
      (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom hAC.unop)).toRingHom) ≫ xA.left =
    Spec.map
      (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom hBC.unop)).toRingHom) ≫ xB.left
  exact heq


end ScalarTower

end AlgebraicGeometry
