/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.KernImage
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Algebra.Field.Rat
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# A coproduct square over the rational point

Let `S = Spec ℚ` and `D = S ⨿ S`. The source is the pullback of the two fold
maps `D ⟶ S`, not a replacement for that pullback. Mathlib's finitary extensive
comparison, transported through `coprodIsoSigma`, identifies it with four
components. Each component is a pullback of two identities, canonically
isomorphic to `S`, rather than definitionally equal to `S`.

The morphism to `D` is AND on these components: only 11 maps to the right
component. For the left-component target open, the open of good fibres is
nonempty and proper. Its projection preimage has two components, whereas the
target-open preimage has three. All calculations use the comparison isomorphism
and Mathlib's coproduct homeomorphisms, not a pointwise-product description of
general scheme pullbacks. The factor is Mathlib's `resLE`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.CoproductSquare

private abbrev S : Scheme := Spec (CommRingCat.of ℚ)
private abbrev D : Scheme := S ⨿ S
private def fold : D ⟶ S := coprod.desc (𝟙 S) (𝟙 S)
private abbrev E : Scheme := pullback fold fold
private abbrev π : E ⟶ D := pullback.snd fold fold

private instance : IsFinite fold := by
  dsimp [fold]
  infer_instance

private instance : UniversallyClosed fold := inferInstance
private instance : UniversallyClosed π := inferInstance

private abbrev I := ULift.{0} WalkingPair
private abbrev l : I := ⟨.left⟩
private abbrev r : I := ⟨.right⟩
private abbrev C (i : I) : Scheme := i.down.casesOn S S
private def τ (i : I) : C i ⟶ S :=
  match i with
  | ⟨.left⟩ => 𝟙 S
  | ⟨.right⟩ => 𝟙 S

private def binary : D ≅ ∐ C := coprodIsoSigma S S
private def inc (i : I) : C i ⟶ D := Sigma.ι C i ≫ binary.inv

@[simp] private lemma inc_l : inc l = (coprod.inl : S ⟶ D) :=
  ι_left_coprodIsoSigma_inv S S

@[simp] private lemma inc_r : inc r = (coprod.inr : S ⟶ D) :=
  ι_right_coprodIsoSigma_inv S S

private lemma desc_τ : Sigma.desc τ = binary.inv ≫ fold := by
  apply Sigma.hom_ext
  rintro ⟨i⟩
  cases i
  · calc
      Sigma.ι C l ≫ Sigma.desc τ = τ l := Sigma.ι_desc τ l
      _ = inc l ≫ fold := by
        rw [inc_l]
        exact (coprod.inl_desc (𝟙 S) (𝟙 S)).symm
      _ = Sigma.ι C l ≫ (binary.inv ≫ fold) := Category.assoc _ _ _
  · calc
      Sigma.ι C r ≫ Sigma.desc τ = τ r := Sigma.ι_desc τ r
      _ = inc r ≫ fold := by
        rw [inc_r]
        exact (coprod.inr_desc (𝟙 S) (𝟙 S)).symm
      _ = Sigma.ι C r ≫ (binary.inv ≫ fold) := Category.assoc _ _ _

private abbrev Q (k : I × I) : Scheme := pullback (τ k.1) (τ k.2)
private abbrev Four : Scheme := ∐ Q
private def left : Four ⟶ D :=
  (Sigma.desc fun k : I × I ↦ pullback.fst (τ k.1) (τ k.2) ≫ Sigma.ι C k.1) ≫
    binary.inv
private def right : Four ⟶ D :=
  (Sigma.desc fun k : I × I ↦ pullback.snd (τ k.1) (τ k.2) ≫ Sigma.ι C k.2) ≫
    binary.inv

private lemma square : IsPullback left right fold fold := by
  refine (FinitaryPreExtensive.isPullback_sigmaDesc τ τ).of_iso
    (Iso.refl _) binary.symm binary.symm (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.id_comp left).symm
  · exact (Category.id_comp right).symm
  · exact (Category.comp_id (Sigma.desc τ)).trans desc_τ
  · exact (Category.comp_id (Sigma.desc τ)).trans desc_τ

private def comparison : Four ≅ E := square.isoPullback

@[reassoc (attr := simp)]
private lemma comparison_fst : comparison.hom ≫ pullback.fst fold fold = left :=
  square.isoPullback_hom_fst

@[reassoc (attr := simp)]
private lemma comparison_snd : comparison.hom ≫ π = right :=
  square.isoPullback_hom_snd

-- The component projection is an isomorphism, not a definitional identification.
private def componentIso (k : I × I) : Q k ≅ S := by
  rcases k with ⟨⟨i⟩, ⟨j⟩⟩
  cases i <;> cases j <;> exact (IsPullback.id_horiz (𝟙 S)).isoPullback.symm

private def component (k : I × I) : Q k ⟶ E := Sigma.ι Q k ≫ comparison.hom

@[reassoc (attr := simp)]
private lemma component_fst (k : I × I) :
    component k ≫ pullback.fst fold fold = pullback.fst (τ k.1) (τ k.2) ≫ inc k.1 := by
  calc
    component k ≫ pullback.fst fold fold = Sigma.ι Q k ≫ left := by
      rw [component, Category.assoc, comparison_fst]
    _ = (pullback.fst (τ k.1) (τ k.2) ≫ Sigma.ι C k.1) ≫ binary.inv := by
      rw [left, ← Category.assoc, Sigma.ι_desc]
    _ = pullback.fst (τ k.1) (τ k.2) ≫ inc k.1 := Category.assoc _ _ _

@[reassoc (attr := simp)]
private lemma component_snd (k : I × I) :
    component k ≫ π = pullback.snd (τ k.1) (τ k.2) ≫ inc k.2 := by
  calc
    component k ≫ π = Sigma.ι Q k ≫ right := by
      rw [component, Category.assoc, comparison_snd]
    _ = (pullback.snd (τ k.1) (τ k.2) ≫ Sigma.ι C k.2) ≫ binary.inv := by
      rw [right, ← Category.assoc, Sigma.ι_desc]
    _ = pullback.snd (τ k.1) (τ k.2) ≫ inc k.2 := Category.assoc _ _ _

private def bothRight (k : I × I) : Bool :=
  match k.1.down, k.2.down with
  | .right, .right => true
  | _, _ => false

private def andMap : Four ⟶ D :=
  Sigma.desc fun k : I × I ↦ pullback.fst (τ k.1) (τ k.2) ≫ τ k.1 ≫
    (if bothRight k then (coprod.inr : S ⟶ D) else coprod.inl)

-- Transport is along the INVERSE of the comparison to the original pullback.
private def f : E ⟶ D := comparison.inv ≫ andMap

@[reassoc (attr := simp)]
private lemma component_f (k : I × I) :
    component k ≫ f = pullback.fst (τ k.1) (τ k.2) ≫ τ k.1 ≫
      (if bothRight k then (coprod.inr : S ⟶ D) else coprod.inl) := by
  calc
    component k ≫ f = Sigma.ι Q k ≫ andMap := by
      rw [component, f, Category.assoc, comparison.hom_inv_id_assoc]
    _ = _ := Sigma.ι_desc _ k

private def p : S := (default : PrimeSpectrum ℚ)
private def pC (i : I) : C i :=
  match i with
  | ⟨.left⟩ => p
  | ⟨.right⟩ => p

private lemma point_unique (i : I) (x : C i) : x = pC i := by
  rcases i with ⟨i⟩
  cases i <;> exact Subsingleton.elim (α := PrimeSpectrum ℚ) _ _

private def y (i : I) : D := inc i (pC i)
private def y₀ : D := (coprod.inl : S ⟶ D) p
private def y₁ : D := (coprod.inr : S ⟶ D) p

@[simp] private lemma y_l : y l = y₀ :=
  congrArg (fun a : S ⟶ D ↦ a p) inc_l

@[simp] private lemma y_r : y r = y₁ :=
  congrArg (fun a : S ⟶ D ↦ a p) inc_r

private lemma distinct : y₀ ≠ y₁ := inl_ne_inr S S p p

private def e (k : I × I) : E := component k ((componentIso k).inv p)

private lemma e_fst (k : I × I) : pullback.fst fold fold (e k) = y k.1 := by
  change pullback.fst fold fold (component k ((componentIso k).inv p)) = inc k.1 (pC k.1)
  rw [← Scheme.Hom.comp_apply (component k) (pullback.fst fold fold), component_fst,
    Scheme.Hom.comp_apply]
  exact congrArg (fun x : C k.1 ↦ inc k.1 x)
    (point_unique k.1 (pullback.fst (τ k.1) (τ k.2) ((componentIso k).inv p)))

private lemma e_snd (k : I × I) : π (e k) = y k.2 := by
  change π (component k ((componentIso k).inv p)) = inc k.2 (pC k.2)
  rw [← Scheme.Hom.comp_apply (component k) π, component_snd,
    Scheme.Hom.comp_apply]
  exact congrArg (fun x : C k.2 ↦ inc k.2 x)
    (point_unique k.2 (pullback.snd (τ k.1) (τ k.2) ((componentIso k).inv p)))

private lemma e_f (k : I × I) : f (e k) = if bothRight k then y₁ else y₀ := by
  change f (component k ((componentIso k).inv p)) = _
  rw [← Scheme.Hom.comp_apply (component k) f, component_f,
    Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  have hp : τ k.1 (pullback.fst (τ k.1) (τ k.2) ((componentIso k).inv p)) = p :=
    Subsingleton.elim (α := PrimeSpectrum ℚ) _ _
  rw [hp]
  cases hb : bothRight k <;> rfl

-- Exhaustion comes from two homeomorphisms and the component isomorphisms.
private lemma exists_e (x : E) : ∃ k, x = e k := by
  obtain ⟨z, rfl⟩ := comparison.hom.homeomorph.surjective x
  obtain ⟨⟨k, q⟩, rfl⟩ := (sigmaMk Q).surjective z
  have hq : q = (componentIso k).inv p := by
    apply (componentIso k).hom.homeomorph.injective
    exact Subsingleton.elim _ _
  refine ⟨k, ?_⟩
  rw [sigmaMk_mk, hq]
  rfl

private def U : D.Opens := (coprod.inl : S ⟶ D).opensRange

private lemma y₀_mem_U : y₀ ∈ U := ⟨p, rfl⟩
private lemma y₁_not_mem_U : y₁ ∉ U := by
  rintro ⟨q, hq⟩
  exact inl_ne_inr S S q p hq

private lemma good_fibre (x : E) (hx : π x = y₀) : f x ∈ U := by
  obtain ⟨⟨⟨i⟩, ⟨j⟩⟩, rfl⟩ := exists_e x
  cases i <;> cases j
  · simpa [e_f, bothRight] using y₀_mem_U
  · exact False.elim (distinct.symm (by simpa [e_snd] using hx))
  · simpa [e_f, bothRight] using y₀_mem_U
  · exact False.elim (distinct.symm (by simpa [e_snd] using hx))

private lemma bad_fibre : π (e (r, r)) = y₁ ∧ f (e (r, r)) ∉ U := by
  constructor
  · simp [e_snd]
  · simpa [e_f, bothRight] using y₁_not_mem_U

private def V : D.Opens := π.kernImage π.isClosedMap (f ⁻¹ᵁ U)

private lemma y₀_mem_V : y₀ ∈ V :=
  (π.mem_kernImage π.isClosedMap (f ⁻¹ᵁ U) y₀).mpr (fun _ hx ↦ good_fibre _ hx)

private lemma y₁_not_mem_V : y₁ ∉ V := by
  intro h
  exact bad_fibre.2 ((π.mem_kernImage π.isClosedMap (f ⁻¹ᵁ U) y₁).mp h bad_fibre.1)

private lemma V_eq_U : V = U := by
  ext x
  obtain ⟨(q | q), rfl⟩ := (coprodMk S S).surjective x
  · obtain rfl : q = p := Subsingleton.elim _ _
    rw [coprodMk_inl]
    change y₀ ∈ V ↔ y₀ ∈ U
    exact iff_of_true y₀_mem_V y₀_mem_U
  · obtain rfl : q = p := Subsingleton.elim _ _
    rw [coprodMk_inr]
    change y₁ ∈ V ↔ y₁ ∈ U
    exact iff_of_false y₁_not_mem_V y₁_not_mem_U

private lemma three_components (i j : I) :
    e (i, j) ∈ f ⁻¹ᵁ U ↔ ¬ (i = r ∧ j = r) := by
  rw [Scheme.Hom.mem_preimage]
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  cases i <;> cases j <;>
    simp [e_f, bothRight, y₀_mem_U, y₁_not_mem_U]

private lemma two_components (i j : I) : e (i, j) ∈ π ⁻¹ᵁ V ↔ j = l := by
  rw [Scheme.Hom.mem_preimage]
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  cases i <;> cases j <;>
    simp [e_snd, V_eq_U, y₀_mem_U, y₁_not_mem_U]

private lemma not_saturated : ¬ f ⁻¹ᵁ U ≤ π ⁻¹ᵁ V := by
  intro h
  have hx : e (l, r) ∈ f ⁻¹ᵁ U := (three_components l r).mpr (by simp)
  exact (by simp : r ≠ l) ((two_components l r).mp (h hx))

-- This source inequality is proved by the characteristic API, not the headline.
private lemma source_le : π ⁻¹ᵁ V ≤ f ⁻¹ᵁ U :=
  π.preimage_kernImage_le π.isClosedMap (f ⁻¹ᵁ U)

private def g : (π ⁻¹ᵁ V).toScheme ⟶ U.toScheme := f.resLE U (π ⁻¹ᵁ V) source_le

/-- Both factors have distinct points; the good-fibre open is nonempty and proper,
and the original projection preimage has a factor constructed by `resLE`.
The three-versus-two component calculation is independent of the factorization
universal property. -/
example :
    (∃ x₀ x₁ : D, x₀ ≠ x₁) ∧
    y₀ ∈ V ∧ y₁ ∉ V ∧ (V : Set D).Nonempty ∧ V ≠ ⊤ ∧ V = U ∧
    (∀ x : E, π x = y₀ → f x ∈ U) ∧
    (π (e (r, r)) = y₁ ∧ f (e (r, r)) ∉ U) ∧
    (∀ i j, e (i, j) ∈ f ⁻¹ᵁ U ↔ ¬ (i = r ∧ j = r)) ∧
    (∀ i j, e (i, j) ∈ π ⁻¹ᵁ V ↔ j = l) ∧
    (¬ f ⁻¹ᵁ U ≤ π ⁻¹ᵁ V) ∧
    (g ≫ U.ι = (π ⁻¹ᵁ V).ι ≫ f) ∧
    (∀ x : π ⁻¹ᵁ V, (g x).1 = f x) := by
  have hproper : V ≠ ⊤ := by
    intro h
    apply y₁_not_mem_V
    rw [h]
    trivial
  refine ⟨⟨y₀, y₁, distinct⟩, y₀_mem_V, y₁_not_mem_V,
    ⟨y₀, y₀_mem_V⟩, hproper, V_eq_U,
    good_fibre, bad_fibre, three_components, two_components, not_saturated, ?_, ?_⟩
  · exact f.resLE_comp_ι source_le
  · exact fun x ↦ f.coe_resLE_apply source_le x

end AlgebraicGeometry.CoproductSquare

namespace AlgebraicGeometry.CoproductSquare

/-- Over the good-fibre open of the coproduct square, the restriction factors
uniquely through the left component as a scheme morphism. -/
example :
    ∃! h : (π ⁻¹ᵁ V).toScheme ⟶ U.toScheme,
      h ≫ U.ι = (π ⁻¹ᵁ V).ι ≫ f := by
  have hV : V ≤ π.kernImage π.isClosedMap (f ⁻¹ᵁ U) :=
    (π.le_kernImage_iff π.isClosedMap V (f ⁻¹ᵁ U)).mpr source_le
  exact (π.le_kernImage_preimage_iff_existsUnique π.isClosedMap f U V).mp hV

end AlgebraicGeometry.CoproductSquare
