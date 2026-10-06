/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products

/-!
# Extension from a subfunctor dense for single covers

A subfunctor is *one-cover dense* for a class of morphisms if every section of its ambient
functor restricts to the subfunctor along **one** morphism of that class. This differs from
local surjectivity for a general covering sieve, which may require a family of morphisms.

When covers admit pullbacks and are stable under base change, a map from a one-cover dense
subfunctor to a target satisfying singleton Čech descent extends uniquely to the ambient
functor. The target condition is `Presieve.IsSheafFor` on each singleton presieve: it
includes both separatedness and existence of a glue. Neither the ambient functor nor its
subfunctor is assumed to be a sheaf.

An isomorphism of two dense subfunctors extends to their ambient presheaves when
both ambient presheaves satisfy singleton descent. No descent condition is imposed
on either subfunctor.

## References

- J. S. Milne, *Algebraic Groups*, Definition 5.6 for the fat-subfunctor
  condition, Lemma 5.9 and Proposition 5.10 for the single faithfully flat
  extension argument, and Corollary 5.11 for the isomorphism of two fat
  subfunctors.
- Mathlib's `Subfunctor` and `Presieve.IsSheafFor` for the categorical formulation.
- Scheme Properties' restricted functor-of-points API for the finite-type specialization.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u w

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w}

/-- Every section enters `D` after one morphism satisfying `W`. This abstracts
the fat-subfunctor condition of J. S. Milne, *Algebraic Groups*, Definition 5.6
from one faithfully flat algebra extension to an arbitrary category and morphism
property, not to arbitrary covering families. In the algebraic specialization
`W` consists of faithfully flat maps of finitely generated algebras. -/
def IsOneCoverDense (D : Subfunctor F) (W : MorphismProperty C) : Prop :=
  ∀ (X : C) (x : F.obj (op X)),
    ∃ (U : C) (f : U ⟶ X), W f ∧ F.map f.op x ∈ D.obj (op U)

/-- The defining witness for one-cover density, including membership after restriction. -/
theorem isOneCoverDense_iff (D : Subfunctor F) (W : MorphismProperty C) :
    D.IsOneCoverDense W ↔
      ∀ (X : C) (x : F.obj (op X)),
        ∃ (U : C) (f : U ⟶ X), W f ∧ F.map f.op x ∈ D.obj (op U) := Iff.rfl

/-- The full subfunctor is one-cover dense when identities are covers. -/
theorem isOneCoverDense_top (W : MorphismProperty C) [W.ContainsIdentities] :
    (⊤ : Subfunctor F).IsOneCoverDense W := by
  intro X x
  exact ⟨X, 𝟙 X, W.id_mem X, Set.mem_univ _⟩

/-- Enlarging a one-cover dense subfunctor preserves one-cover density. -/
theorem IsOneCoverDense.mono {D E : Subfunctor F} {W : MorphismProperty C}
    (hD : D.IsOneCoverDense W) (h : D ≤ E) : E.IsOneCoverDense W := by
  intro X x
  obtain ⟨U, f, hf, hx⟩ := hD X x
  exact ⟨U, f, hf, h _ hx⟩

/-- A pointwise-surjective natural transformation has one-cover dense range. -/
theorem isOneCoverDense_range_of_surjective {G : Cᵒᵖ ⥤ Type w}
    (W : MorphismProperty C) [W.ContainsIdentities] (p : G ⟶ F)
    (hp : ∀ X, Function.Surjective (p.app X)) :
    (Subfunctor.range p).IsOneCoverDense W := by
  intro X x
  obtain ⟨y, hy⟩ := hp (op X) x
  refine ⟨X, 𝟙 X, W.id_mem X, ?_⟩
  simp only [op_id, Functor.map_id, Subfunctor.range] at *
  exact ⟨y, hy⟩

/-- One-cover density implies local surjectivity on any topology that admits
these singleton covers. The converse is not asserted: general covering sieves
can require more than one morphism. -/
theorem IsOneCoverDense.isLocallySurjective {W : MorphismProperty C}
    {D : Subfunctor F} (hD : D.IsOneCoverDense W) (J : GrothendieckTopology C)
    (hW : ∀ {X U : C} (f : U ⟶ X), W f →
      Sieve.generate (Presieve.singleton f) ∈ J X) :
    Presheaf.IsLocallySurjective J D.ι := by
  refine ⟨fun {X} x => ?_⟩
  obtain ⟨U, f, hf, hx⟩ := hD X x
  refine J.superset_covering ?_ (hW f hf)
  rw [Sieve.generate_le_iff]
  intro V g hg
  obtain ⟨rfl⟩ := hg
  exact ⟨⟨F.map f.op x, hx⟩, rfl⟩

/-- A one-cover witness pulls back along any test morphism. This is the refinement
needed to compare restrictions and to prove naturality of extension. -/
theorem IsOneCoverDense.exists_baseChange
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {D : Subfunctor F} (hD : D.IsOneCoverDense W)
    {X Y : C} (g : Y ⟶ X) (x : F.obj (op X)) :
    ∃ (U : C) (f : U ⟶ X) (P : C) (p : P ⟶ U) (q : P ⟶ Y),
      W f ∧ IsPullback p q f g ∧ W q ∧
        F.map q.op (F.map g.op x) ∈ D.obj (op P) := by
  obtain ⟨U, f, hf, hx⟩ := hD X x
  have : HasPullback f g := W.hasPullback g hf
  refine ⟨U, f, pullback f g, pullback.fst f g, pullback.snd f g,
    hf, IsPullback.of_hasPullback f g, W.pullback_snd f g hf, ?_⟩
  have hmem : F.map (pullback.fst f g).op (F.map f.op x) ∈
      D.obj (op (pullback f g)) := D.map _ hx
  have heq : F.map (pullback.snd f g).op (F.map g.op x) =
      F.map (pullback.fst f g).op (F.map f.op x) := by
    calc
      _ = F.map ((pullback.snd f g) ≫ g).op x := by rw [op_comp, F.map_comp]; rfl
      _ = F.map ((pullback.fst f g) ≫ f).op x := by rw [pullback.condition]
      _ = F.map (pullback.fst f g).op (F.map f.op x) := by rw [op_comp, F.map_comp]; rfl
  rw [heq]
  exact hmem

/-- Intersect two dense subfunctors by taking successive single covers. Their
composite remains one cover when the morphism property is composition-stable. -/
theorem IsOneCoverDense.inf
    {W : MorphismProperty C} [W.IsStableUnderComposition]
    {D E : Subfunctor F} (hD : D.IsOneCoverDense W) (hE : E.IsOneCoverDense W) :
    (D ⊓ E).IsOneCoverDense W := by
  intro X x
  obtain ⟨U, f, hf, hx⟩ := hD X x
  obtain ⟨V, g, hg, hy⟩ := hE U (F.map f.op x)
  refine ⟨V, g ≫ f, W.comp_mem g f hg hf, ?_⟩
  change F.map (g ≫ f).op x ∈ D.obj (op V) ∩ E.obj (op V)
  rw [op_comp, F.map_comp]
  exact ⟨D.map g.op hx, hy⟩

/-- The pointwise product of two subfunctors, formed with Mathlib's
product and inverse-image constructions. -/
noncomputable def product {G : Cᵒᵖ ⥤ Type w} (D : Subfunctor F) (E : Subfunctor G) :
    Subfunctor (F ⨯ G) :=
  D.preimage (Limits.prod.fst : F ⨯ G ⟶ F) ⊓
    E.preimage (Limits.prod.snd : F ⨯ G ⟶ G)

/-- Membership in a product subfunctor is membership in each factor. -/
theorem mem_product_iff {G : Cᵒᵖ ⥤ Type w} (D : Subfunctor F) (E : Subfunctor G)
    (X : Cᵒᵖ) (x : (F ⨯ G).obj X) :
    x ∈ (D.product E).obj X ↔
      ((Limits.prod.fst : F ⨯ G ⟶ F).app X x ∈ D.obj X ∧
        (Limits.prod.snd : F ⨯ G ⟶ G).app X x ∈ E.obj X) := Iff.rfl

/-- A product of one-cover dense subfunctors is one-cover dense: successive
faithfully flat extensions suffice to make both components enter their factors. -/
theorem IsOneCoverDense.product {G : Cᵒᵖ ⥤ Type w}
    {W : MorphismProperty C} [W.IsStableUnderComposition]
    {D : Subfunctor F} {E : Subfunctor G}
    (hD : D.IsOneCoverDense W) (hE : E.IsOneCoverDense W) :
    (D.product E).IsOneCoverDense W := by
  intro X x
  obtain ⟨U, f, hf, hx⟩ := hD X ((Limits.prod.fst : F ⨯ G ⟶ F).app (op X) x)
  obtain ⟨V, g, hg, hy⟩ := hE U
    ((Limits.prod.snd : F ⨯ G ⟶ G).app (op U) ((F ⨯ G).map f.op x))
  refine ⟨V, g ≫ f, W.comp_mem g f hg hf, ?_⟩
  rw [mem_product_iff, op_comp, Functor.map_comp]
  constructor
  · change ((Limits.prod.fst : F ⨯ G ⟶ F).app (op V)
        ((F ⨯ G).map g.op ((F ⨯ G).map f.op x))) ∈ D.obj (op V)
    rw [NatTrans.naturality_apply (Limits.prod.fst : F ⨯ G ⟶ F) g.op,
      NatTrans.naturality_apply (Limits.prod.fst : F ⨯ G ⟶ F) f.op]
    exact D.map g.op hx
  · change ((Limits.prod.snd : F ⨯ G ⟶ G).app (op V)
        ((F ⨯ G).map g.op ((F ⨯ G).map f.op x))) ∈ E.obj (op V)
    rwa [NatTrans.naturality_apply (Limits.prod.snd : F ⨯ G ⟶ G) g.op]

/-- Applying a map on a subfunctor to a restriction gives compatible singleton data. -/
private lemma compatible_of_section
    {D : Subfunctor F} {Y : Cᵒᵖ ⥤ Type w} (φ : D.toFunctor ⟶ Y)
    {X U : C} (f : U ⟶ X) (x : F.obj (op X))
    (hx : F.map f.op x ∈ D.obj (op U)) :
    ∀ {Z : C} (p₁ p₂ : Z ⟶ U), p₁ ≫ f = p₂ ≫ f →
      Y.map p₁.op (φ.app (op U) ⟨F.map f.op x, hx⟩) =
        Y.map p₂.op (φ.app (op U) ⟨F.map f.op x, hx⟩) := by
  intro Z p₁ p₂ heq
  have hsub : D.toFunctor.map p₁.op ⟨F.map f.op x, hx⟩ =
      D.toFunctor.map p₂.op ⟨F.map f.op x, hx⟩ := by
    apply Subtype.ext
    change F.map p₁.op (F.map f.op x) = F.map p₂.op (F.map f.op x)
    calc
      _ = F.map (p₁ ≫ f).op x := by rw [op_comp, F.map_comp]; rfl
      _ = F.map (p₂ ≫ f).op x := by rw [heq]
      _ = F.map p₂.op (F.map f.op x) := by rw [op_comp, F.map_comp]; rfl
  simpa only [NatTrans.naturality_apply] using congrArg (φ.app (op Z)) hsub

/-- A section has a unique target value characterized by its restrictions wherever it
enters the subfunctor, including along morphisms not necessarily in the cover class. -/
lemma existsUnique_oneCover_glue
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {D : Subfunctor F} (hD : D.IsOneCoverDense W) {Y : Cᵒᵖ ⥤ Type w}
    (hY : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor Y (Presieve.singleton f))
    (φ : D.toFunctor ⟶ Y) (X : C) (x : F.obj (op X)) :
    ∃! t : Y.obj (op X), ∀ {U : C} (f : U ⟶ X)
      (hx : F.map f.op x ∈ D.obj (op U)),
        Y.map f.op t = φ.app (op U) ⟨F.map f.op x, hx⟩ := by
  obtain ⟨U, f, hf, hx⟩ := hD X x
  obtain ⟨t, ht⟩ := ((Presieve.isSheafFor_singleton (P := Y)).mp (hY f hf)
    (φ.app (op U) ⟨F.map f.op x, hx⟩) (compatible_of_section φ f x hx)).exists
  refine ⟨t, ?_, ?_⟩
  · intro V g hg
    have : HasPullback f g := W.hasPullback g hf
    have hq : W (pullback.snd f g) := W.pullback_snd f g hf
    apply (Presieve.isSeparatedFor_singleton (P := Y)).mp (hY _ hq).isSeparatedFor
    have hsub : D.toFunctor.map (pullback.fst f g).op ⟨F.map f.op x, hx⟩ =
        D.toFunctor.map (pullback.snd f g).op ⟨F.map g.op x, hg⟩ := by
      apply Subtype.ext
      change F.map (pullback.fst f g).op (F.map f.op x) =
        F.map (pullback.snd f g).op (F.map g.op x)
      calc
        _ = F.map ((pullback.fst f g) ≫ f).op x := by rw [op_comp, F.map_comp]; rfl
        _ = F.map ((pullback.snd f g) ≫ g).op x := by rw [pullback.condition]
        _ = F.map (pullback.snd f g).op (F.map g.op x) := by
          rw [op_comp, F.map_comp]; rfl
    calc
      Y.map (pullback.snd f g).op (Y.map g.op t) =
          Y.map (pullback.fst f g).op (Y.map f.op t) := by
        rw [← comp_apply, ← Y.map_comp, ← op_comp, ← pullback.condition,
          op_comp, Y.map_comp, comp_apply]
      _ = Y.map (pullback.fst f g).op (φ.app (op U) ⟨F.map f.op x, hx⟩) := by
        rw [ht]
      _ = φ.app (op (pullback f g))
          (D.toFunctor.map (pullback.fst f g).op ⟨F.map f.op x, hx⟩) := by
        rw [NatTrans.naturality_apply]
      _ = φ.app (op (pullback f g))
          (D.toFunctor.map (pullback.snd f g).op ⟨F.map g.op x, hg⟩) := by
        rw [hsub]
      _ = Y.map (pullback.snd f g).op (φ.app (op V) ⟨F.map g.op x, hg⟩) := by
        rw [NatTrans.naturality_apply]
  · intro t' ht'
    apply (Presieve.isSeparatedFor_singleton (P := Y)).mp (hY f hf).isSeparatedFor
    exact (ht' f hx).trans ht.symm

/-- Restriction of natural transformations is an equivalence when the target has
unique Čech gluing for each singleton cover and these covers admit pullback refinement.
This does not require descent for `F` or `D`, nor composition stability of the
cover class. This categorical strengthening of Milne, *Algebraic Groups*,
Lemma 5.9 and Proposition 5.10 recovers the faithfully flat finite-type case. -/
noncomputable def oneCoverExtensionEquiv
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {D : Subfunctor F} (hD : D.IsOneCoverDense W) {Y : Cᵒᵖ ⥤ Type w}
    (hY : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor Y (Presieve.singleton f)) :
    (F ⟶ Y) ≃ (D.toFunctor ⟶ Y) := by
  refine ⟨fun φ => D.ι ≫ φ, (fun φ => ?_), ?_, ?_⟩
  · refine {
      app := fun
        | .op X => ↾fun x => (existsUnique_oneCover_glue hD hY φ X x).choose
      naturality := ?_ }
    intro X Z g
    cases X with
    | op X =>
      cases Z with
      | op Z =>
        apply ConcreteCategory.hom_ext
        intro x
        symm
        obtain ⟨U, f, hf, hx⟩ := hD Z (F.map g x)
        apply (Presieve.isSeparatedFor_singleton (P := Y)).mp (hY f hf).isSeparatedFor
        have hcomp : F.map (f ≫ g.unop).op x ∈ D.obj (op U) := by
          simpa only [op_comp, Quiver.Hom.op_unop, F.map_comp, types_comp_apply] using hx
        have h₁ := (existsUnique_oneCover_glue hD hY φ X x).choose_spec.1
          (f ≫ g.unop) hcomp
        have h₂ := (existsUnique_oneCover_glue hD hY φ Z (F.map g x)).choose_spec.1
          f hx
        change Y.map f.op (Y.map g ((existsUnique_oneCover_glue hD hY φ X x).choose)) =
          Y.map f.op ((existsUnique_oneCover_glue hD hY φ Z (F.map g x)).choose)
        calc
          _ = Y.map (f ≫ g.unop).op
              ((existsUnique_oneCover_glue hD hY φ X x).choose) := by
            simp only [op_comp, Quiver.Hom.op_unop, Y.map_comp, types_comp_apply]
          _ = φ.app (op U) ⟨F.map (f ≫ g.unop).op x, hcomp⟩ := h₁
          _ = φ.app (op U) ⟨F.map f.op (F.map g x), hx⟩ := by
            congr 1
            apply Subtype.ext
            simp only [op_comp, Quiver.Hom.op_unop, F.map_comp, types_comp_apply]
          _ = Y.map f.op
              ((existsUnique_oneCover_glue hD hY φ Z (F.map g x)).choose) := h₂.symm
  · intro φ
    ext X x
    cases X with
    | op X =>
      obtain ⟨U, f, hf, hx⟩ := hD X x
      apply (Presieve.isSeparatedFor_singleton (P := Y)).mp (hY f hf).isSeparatedFor
      have hspec := (existsUnique_oneCover_glue hD hY (D.ι ≫ φ) X x).choose_spec.1
        f hx
      calc
        _ = (D.ι ≫ φ).app (op U) ⟨F.map f.op x, hx⟩ := by
          change Y.map f.op
            ((existsUnique_oneCover_glue hD hY (D.ι ≫ φ) X x).choose) =
              (D.ι ≫ φ).app (op U) ⟨F.map f.op x, hx⟩
          exact hspec
        _ = φ.app (op U) (F.map f.op x) := by
          simp only [NatTrans.comp_app, types_comp_apply, Subfunctor.ι_app]
          rfl
        _ = Y.map f.op (φ.app (op X) x) := NatTrans.naturality_apply φ f.op x
  · intro φ
    ext X a
    cases X with
    | op X =>
      obtain ⟨x, hx⟩ := a
      have hspec := (existsUnique_oneCover_glue hD hY φ X x).choose_spec.1
        (𝟙 X) (by simpa only [op_id, Functor.map_id, types_id_apply] using hx)
      simpa [op_id, Functor.map_id, types_id_apply, Subfunctor.ι,
        NatTrans.comp_app, types_comp_apply] using hspec

/-- The equivalence sends an ambient map to its restriction. -/
theorem oneCoverExtensionEquiv_apply
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {D : Subfunctor F} (hD : D.IsOneCoverDense W) {Y : Cᵒᵖ ⥤ Type w}
    (hY : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor Y (Presieve.singleton f)) (φ : F ⟶ Y) :
    oneCoverExtensionEquiv hD hY φ = D.ι ≫ φ := by
  rfl

/-- Extend a map from a one-cover dense subfunctor by singleton Čech descent. -/
noncomputable def extendOneCover
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {D : Subfunctor F} (hD : D.IsOneCoverDense W) {Y : Cᵒᵖ ⥤ Type w}
    (hY : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor Y (Presieve.singleton f))
    (φ : D.toFunctor ⟶ Y) : F ⟶ Y :=
  (oneCoverExtensionEquiv hD hY).symm φ

/-- Restricting an extension recovers the original map. -/
@[reassoc (attr := simp)]
theorem ι_comp_extendOneCover
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {D : Subfunctor F} (hD : D.IsOneCoverDense W) {Y : Cᵒᵖ ⥤ Type w}
    (hY : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor Y (Presieve.singleton f)) (φ : D.toFunctor ⟶ Y) :
    D.ι ≫ extendOneCover hD hY φ = φ := by
  rw [← oneCoverExtensionEquiv_apply hD hY, extendOneCover]
  exact (oneCoverExtensionEquiv hD hY).apply_symm_apply φ

/-- A map extending `φ` agrees with the singleton-descent extension. -/
theorem extendOneCover_unique
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {D : Subfunctor F} (hD : D.IsOneCoverDense W) {Y : Cᵒᵖ ⥤ Type w}
    (hY : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor Y (Presieve.singleton f))
    (φ : D.toFunctor ⟶ Y) (ψ : F ⟶ Y) (hψ : D.ι ≫ ψ = φ) :
    ψ = extendOneCover hD hY φ := by
  apply (oneCoverExtensionEquiv hD hY).injective
  rw [oneCoverExtensionEquiv_apply, hψ]
  exact (oneCoverExtensionEquiv hD hY).apply_symm_apply φ |>.symm

/-- Extend an isomorphism of two one-cover dense subfunctors to their ambient
presheaves. Each ambient presheaf satisfies singleton descent; neither
subfunctor is required to satisfy descent. This abstracts the
finite-type faithfully flat setting of Milne, *Algebraic Groups*, Corollary 5.11. -/
noncomputable def extendOneCoverIso
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {G : Cᵒᵖ ⥤ Type w} {D : Subfunctor F} (hD : D.IsOneCoverDense W)
    {E : Subfunctor G} (hE : E.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f))
    (hG : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor G (Presieve.singleton f))
    (e : D.toFunctor ≅ E.toFunctor) : F ≅ G where
  hom := extendOneCover hD hG (e.hom ≫ E.ι)
  inv := extendOneCover hE hF (e.inv ≫ D.ι)
  hom_inv_id := by
    apply (oneCoverExtensionEquiv hD hF).injective
    rw [oneCoverExtensionEquiv_apply, oneCoverExtensionEquiv_apply]
    calc
      D.ι ≫ (extendOneCover hD hG (e.hom ≫ E.ι) ≫
          extendOneCover hE hF (e.inv ≫ D.ι)) =
          e.hom ≫ E.ι ≫ extendOneCover hE hF (e.inv ≫ D.ι) := by
            rw [← Category.assoc, ι_comp_extendOneCover, Category.assoc]
      _ = e.hom ≫ e.inv ≫ D.ι := by
            rw [ι_comp_extendOneCover]
      _ = D.ι ≫ 𝟙 F := by simp
  inv_hom_id := by
    apply (oneCoverExtensionEquiv hE hG).injective
    rw [oneCoverExtensionEquiv_apply, oneCoverExtensionEquiv_apply]
    calc
      E.ι ≫ (extendOneCover hE hF (e.inv ≫ D.ι) ≫
          extendOneCover hD hG (e.hom ≫ E.ι)) =
          e.inv ≫ D.ι ≫ extendOneCover hD hG (e.hom ≫ E.ι) := by
            rw [← Category.assoc, ι_comp_extendOneCover, Category.assoc]
      _ = e.inv ≫ e.hom ≫ E.ι := by
            rw [ι_comp_extendOneCover]
      _ = E.ι ≫ 𝟙 G := by simp

/-- The forward ambient isomorphism restricts to the specified map. -/
@[reassoc (attr := simp)]
theorem ι_comp_extendOneCoverIso_hom
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {G : Cᵒᵖ ⥤ Type w} {D : Subfunctor F} (hD : D.IsOneCoverDense W)
    {E : Subfunctor G} (hE : E.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f))
    (hG : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor G (Presieve.singleton f))
    (e : D.toFunctor ≅ E.toFunctor) :
    D.ι ≫ (extendOneCoverIso hD hE hF hG e).hom = e.hom ≫ E.ι :=
  ι_comp_extendOneCover hD hG (e.hom ≫ E.ι)

/-- The inverse ambient isomorphism restricts to the specified inverse. -/
@[reassoc (attr := simp)]
theorem ι_comp_extendOneCoverIso_inv
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {G : Cᵒᵖ ⥤ Type w} {D : Subfunctor F} (hD : D.IsOneCoverDense W)
    {E : Subfunctor G} (hE : E.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f))
    (hG : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor G (Presieve.singleton f))
    (e : D.toFunctor ≅ E.toFunctor) :
    E.ι ≫ (extendOneCoverIso hD hE hF hG e).inv = e.inv ≫ D.ι :=
  ι_comp_extendOneCover hE hF (e.inv ≫ D.ι)

/-- An ambient isomorphism with the prescribed forward restriction is unique. -/
theorem extendOneCoverIso_unique
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {G : Cᵒᵖ ⥤ Type w} {D : Subfunctor F} (hD : D.IsOneCoverDense W)
    {E : Subfunctor G} (hE : E.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f))
    (hG : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor G (Presieve.singleton f))
    (e : D.toFunctor ≅ E.toFunctor) (i : F ≅ G)
    (hi : D.ι ≫ i.hom = e.hom ≫ E.ι) :
    i = extendOneCoverIso hD hE hF hG e := by
  apply Iso.ext
  exact extendOneCover_unique hD hG (e.hom ≫ E.ι) i.hom hi

/-- Extending the identity on a dense subfunctor gives the identity. -/
theorem extendOneCoverIso_refl
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {D : Subfunctor F} (hD : D.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f)) :
    extendOneCoverIso hD hD hF hF (Iso.refl D.toFunctor) = Iso.refl F := by
  symm
  apply extendOneCoverIso_unique hD hD hF hF (Iso.refl D.toFunctor)
  simp

/-- Extending an inverse agrees with inverting the extended isomorphism. -/
theorem extendOneCoverIso_symm
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {G : Cᵒᵖ ⥤ Type w} {D : Subfunctor F} (hD : D.IsOneCoverDense W)
    {E : Subfunctor G} (hE : E.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f))
    (hG : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor G (Presieve.singleton f))
    (e : D.toFunctor ≅ E.toFunctor) :
    (extendOneCoverIso hD hE hF hG e).symm =
      extendOneCoverIso hE hD hG hF e.symm := by
  apply extendOneCoverIso_unique hE hD hG hF e.symm
  exact ι_comp_extendOneCoverIso_inv hD hE hF hG e

/-- Extension preserves composition through a shared dense subfunctor. -/
theorem extendOneCoverIso_comp
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {G H : Cᵒᵖ ⥤ Type w} {D : Subfunctor F} (hD : D.IsOneCoverDense W)
    {E : Subfunctor G} (hE : E.IsOneCoverDense W)
    {T : Subfunctor H} (hT : T.IsOneCoverDense W)
    (hF : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor F (Presieve.singleton f))
    (hG : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor G (Presieve.singleton f))
    (hH : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor H (Presieve.singleton f))
    (e : D.toFunctor ≅ E.toFunctor) (e' : E.toFunctor ≅ T.toFunctor) :
    extendOneCoverIso hD hT hF hH (e ≪≫ e') =
      extendOneCoverIso hD hE hF hG e ≪≫ extendOneCoverIso hE hT hG hH e' := by
  symm
  apply extendOneCoverIso_unique hD hT hF hH (e ≪≫ e')
  simp only [Iso.trans_hom, Category.assoc, ι_comp_extendOneCoverIso_hom_assoc]
  exact congrArg (fun φ : E.toFunctor ⟶ H ↦ e.hom ≫ φ)
    (ι_comp_extendOneCoverIso_hom hE hT hG hH e')

end CategoryTheory.Subfunctor
