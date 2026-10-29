/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.MaximalPointMorphisms
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Recovering homomorphisms from maximal-point spaces

A morphism of maximal-point locally ringed spaces determines a ring homomorphism
by its action on global sections and the coordinate isomorphisms. The unit of
the global-sections/spectrum adjunction identifies its composite with the affine
inclusion. Consequently its map on points is contraction, and the recovered
homomorphism preserves maximal ideals under contraction.

`maximalPointHomEquiv` identifies all such locally ringed space morphisms with
the maximal-contraction-preserving ring homomorphisms. Its forward map is
`maximalPointMap`; its inverse uses the given global-section maps. Supplied
scalar homomorphisms can lie in an independent universe. For algebras in one
common universe, `maximalPointAlgHomEquiv` gives the corresponding morphisms in
the over category of locally ringed spaces over `Spec K`. A finite-type target
algebra supplies the contraction hypothesis automatically.

## Implementation notes

No scheme structure on a maximal-point space or isomorphism of that space with
the affine spectrum is asserted. All section rings and stalks retain nilpotents,
and the zero ring is allowed. Full section and stalk readbacks are inherited
from `maximalPointMap` through `maximalPoint_eq_map_ringHom`, including their
dependent transports.

## References

* `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`, for the locally ringed space
  global-sections/spectrum adjunction and its unit-naturality formalization.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry.Spec

variable {R S : Type u} [CommRing R] [CommRing S]
variable [IsJacobsonRing R] [IsJacobsonRing S]

/-- The ring homomorphism recovered from the global-section map of a morphism
of maximal-point locally ringed spaces, using the coordinate isomorphisms. -/
def maximalPointRingHom (g : maximalPointSpace S ⟶ maximalPointSpace R) : R →+* S :=
  (maximalPointCoordinates S).symm.toRingHom.comp
    ((LocallyRingedSpace.Γ.map g.op).hom.comp (maximalPointCoordinates R).toRingHom)

/-- Evaluation of the recovered homomorphism in the global coordinates. -/
lemma maximalPointRingHom_apply (g : maximalPointSpace S ⟶ maximalPointSpace R) (r : R) :
    maximalPointRingHom g r = (maximalPointCoordinates S).symm
      ((LocallyRingedSpace.Γ.map g.op) (maximalPointCoordinates R r)) := rfl

/-- The recovered homomorphism reads the top component of the given morphism. -/
lemma maximalPointRingHom_coordinates_apply
    (g : maximalPointSpace S ⟶ maximalPointSpace R) (r : R) :
    maximalPointCoordinates S (maximalPointRingHom g r) =
      g.c.app (op ⊤) (maximalPointCoordinates R r) := by
  change maximalPointCoordinates S ((maximalPointCoordinates S).symm _) = _
  exact (maximalPointCoordinates S).apply_symm_apply _

/-- The global-section square for the recovered coordinate homomorphism. -/
lemma maximalPointRingHom_coordinates (g : maximalPointSpace S ⟶ maximalPointSpace R) :
    CommRingCat.ofHom (maximalPointCoordinates R).toRingHom ≫
        LocallyRingedSpace.Γ.map g.op =
      CommRingCat.ofHom (maximalPointRingHom g) ≫
        CommRingCat.ofHom (maximalPointCoordinates S).toRingHom := by
  apply CommRingCat.hom_ext
  ext r
  exact (maximalPointRingHom_coordinates_apply g r).symm

set_option backward.isDefEq.respectTransparency false in
/-- Every full morphism of maximal-point spaces commutes with the affine
inclusions for its recovered homomorphism. No point-map hypothesis is required. -/
lemma maximalPointRingHom_comp_inclusion
    (g : maximalPointSpace S ⟶ maximalPointSpace R) :
    g ≫ maximalPointInclusion R =
      maximalPointInclusion S ≫
        locallyRingedSpaceMap (CommRingCat.ofHom (maximalPointRingHom g)) := by
  -- Use naturality of the unit of the all-locally-ringed-space adjunction
  -- and the expression of the affine inclusion in terms of that unit.
  have hunit : g ≫ (maximalPointSpace R).toΓSpec =
      (maximalPointSpace S).toΓSpec ≫
        locallyRingedSpaceMap (LocallyRingedSpace.Γ.map g.op) :=
    identityToΓSpec.naturality g
  calc
    g ≫ maximalPointInclusion R =
        (g ≫ (maximalPointSpace R).toΓSpec) ≫
          locallyRingedSpaceMap
            (CommRingCat.ofHom (R := R)
              (S := LocallyRingedSpace.Γ.obj (op (maximalPointSpace R)))
              (maximalPointCoordinates R).toRingHom) := by
      rw [maximalPointInclusion_eq_toΓSpec, Category.assoc]
    _ = ((maximalPointSpace S).toΓSpec ≫
          locallyRingedSpaceMap (LocallyRingedSpace.Γ.map g.op)) ≫
          locallyRingedSpaceMap
            (CommRingCat.ofHom (R := R)
              (S := LocallyRingedSpace.Γ.obj (op (maximalPointSpace R)))
              (maximalPointCoordinates R).toRingHom) := by
      rw [hunit]
    _ = (maximalPointSpace S).toΓSpec ≫
          locallyRingedSpaceMap
            (CommRingCat.ofHom (R := R)
                (S := LocallyRingedSpace.Γ.obj (op (maximalPointSpace R)))
                (maximalPointCoordinates R).toRingHom ≫
              LocallyRingedSpace.Γ.map g.op) := by
      rw [locallyRingedSpaceMap_comp, Category.assoc]
    _ = (maximalPointSpace S).toΓSpec ≫
          locallyRingedSpaceMap
            (CommRingCat.ofHom (maximalPointRingHom g) ≫
              CommRingCat.ofHom (R := S)
                (S := LocallyRingedSpace.Γ.obj (op (maximalPointSpace S)))
                (maximalPointCoordinates S).toRingHom) := by
      rw [maximalPointRingHom_coordinates]
    _ = _ := by
      rw [maximalPointInclusion_eq_toΓSpec, locallyRingedSpaceMap_comp, Category.assoc]

/-- The point map of an arbitrary full morphism is contraction by its recovered
ring homomorphism. This follows from the full affine square. -/
lemma maximalPointRingHom_base_apply
    (g : maximalPointSpace S ⟶ maximalPointSpace R) (x : maximalPointSpace S) :
    (g.base x).val = PrimeSpectrum.comap (maximalPointRingHom g) x.val := by
  exact congrArg
    (fun k : maximalPointSpace S ⟶ locallyRingedSpaceObj (CommRingCat.of R) => k.base x)
    (maximalPointRingHom_comp_inclusion g)

/-- Locality forces the recovered homomorphism to preserve maximal ideals under
contraction. Every maximal prime is used as a point of the source. -/
lemma maximalPointRingHom_maximal_comap
    (g : maximalPointSpace S ⟶ maximalPointSpace R)
    (n : PrimeSpectrum S) (hn : n.asIdeal.IsMaximal) :
    (n.asIdeal.comap (maximalPointRingHom g)).IsMaximal := by
  let x : maximalPointSpace S :=
    ⟨n, (PrimeSpectrum.isClosed_singleton_iff_isMaximal n).mpr hn⟩
  have hx := congrArg PrimeSpectrum.asIdeal (maximalPointRingHom_base_apply g x)
  have hmax : (g.base x).val.asIdeal.IsMaximal := inferInstance
  rw [hx] at hmax
  change (n.asIdeal.comap (maximalPointRingHom g)).IsMaximal at hmax
  exact hmax

/-- Recovering the coordinate homomorphism of the constructed map returns the
given ring homomorphism, rather than its reduction or a residue-field map. -/
@[simp]
lemma maximalPointRingHom_map (φ : R →+* S)
    (hφ : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal → (n.asIdeal.comap φ).IsMaximal) :
    maximalPointRingHom (maximalPointMap φ hφ) = φ := by
  ext r
  apply (maximalPointCoordinates S).injective
  exact (maximalPointRingHom_coordinates_apply (maximalPointMap φ hφ) r).trans
    (maximalPointMap_coordinates_apply φ hφ r)

/-- Every full morphism is `maximalPointMap` for its
recovered homomorphism. Rewriting by this equality also transports the indexed
section and stalk components, so their full localization readbacks apply. -/
lemma maximalPoint_eq_map_ringHom (g : maximalPointSpace S ⟶ maximalPointSpace R) :
    g = maximalPointMap (maximalPointRingHom g) (maximalPointRingHom_maximal_comap g) :=
  maximalPointMap_unique (maximalPointRingHom g) (maximalPointRingHom_maximal_comap g)
    g (maximalPointRingHom_comp_inclusion g)

/-- Ring homomorphisms preserving maximal contraction correspond contravariantly
to all morphisms of the maximal-point locally ringed spaces. -/
def maximalPointHomEquiv (R S : Type u) [CommRing R] [CommRing S]
    [IsJacobsonRing R] [IsJacobsonRing S] :
    {φ : R →+* S // ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap φ).IsMaximal} ≃
      (maximalPointSpace S ⟶ maximalPointSpace R) where
  toFun φ := maximalPointMap φ.val φ.property
  invFun g := ⟨maximalPointRingHom g, maximalPointRingHom_maximal_comap g⟩
  left_inv φ := Subtype.ext (maximalPointRingHom_map φ.val φ.property)
  right_inv g := (maximalPoint_eq_map_ringHom g).symm

/-- The forward equivalence is the maximal-point map construction. -/
@[simp]
lemma maximalPointHomEquiv_apply
    (φ : {φ : R →+* S // ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap φ).IsMaximal}) :
    maximalPointHomEquiv R S φ = maximalPointMap φ.val φ.property := rfl

/-- The inverse equivalence is coordinate conjugation of the global-section map. -/
@[simp]
lemma maximalPointHomEquiv_symm_apply
    (g : maximalPointSpace S ⟶ maximalPointSpace R) :
    ((maximalPointHomEquiv R S).symm g).val = maximalPointRingHom g := rfl

/-- Identity morphisms recover identity ring homomorphisms. -/
@[simp]
lemma maximalPointRingHom_id :
    maximalPointRingHom (𝟙 (maximalPointSpace R)) = RingHom.id R := by
  simpa only [maximalPointMap_id] using
    (maximalPointRingHom_map (RingHom.id R)
      (fun (n : PrimeSpectrum R) (hn : n.asIdeal.IsMaximal) => by
        simpa only [Ideal.comap_id] using hn))

set_option backward.isDefEq.respectTransparency false in
/-- Recovery is contravariant with respect to composition. -/
lemma maximalPointRingHom_comp {T : Type u} [CommRing T] [IsJacobsonRing T]
    (g : maximalPointSpace S ⟶ maximalPointSpace R)
    (h : maximalPointSpace T ⟶ maximalPointSpace S) :
    maximalPointRingHom (h ≫ g) = (maximalPointRingHom h).comp (maximalPointRingHom g) := by
  ext r
  apply (maximalPointCoordinates T).injective
  calc
    maximalPointCoordinates T (maximalPointRingHom (h ≫ g) r) =
        LocallyRingedSpace.Γ.map (h ≫ g).op (maximalPointCoordinates R r) :=
      maximalPointRingHom_coordinates_apply (h ≫ g) r
    _ = LocallyRingedSpace.Γ.map h.op
        (LocallyRingedSpace.Γ.map g.op (maximalPointCoordinates R r)) := by
      simp only [op_comp, Functor.map_comp, CommRingCat.comp_apply]
    _ = LocallyRingedSpace.Γ.map h.op
        (maximalPointCoordinates S (maximalPointRingHom g r)) :=
      congrArg (LocallyRingedSpace.Γ.map h.op)
        (maximalPointRingHom_coordinates_apply g r).symm
    _ = maximalPointCoordinates T (maximalPointRingHom h (maximalPointRingHom g r)) :=
      (maximalPointRingHom_coordinates_apply h (maximalPointRingHom g r)).symm

section SuppliedScalars

variable {K : Type v} [CommRing K]

/-- Compatibility of the global-section map with supplied scalars is
exactly compatibility of the recovered ring homomorphism with those same maps. -/
lemma maximalPointRingHom_scalars_iff (g : maximalPointSpace S ⟶ maximalPointSpace R)
    (κR : K →+* R) (κS : K →+* S) :
    (LocallyRingedSpace.Γ.map g.op).hom.comp (maximalPointScalars R κR) =
        maximalPointScalars S κS ↔
      (maximalPointRingHom g).comp κR = κS := by
  constructor
  · intro hκ
    ext k
    apply (maximalPointCoordinates S).injective
    exact (maximalPointRingHom_coordinates_apply g (κR k)).trans
      (RingHom.congr_fun hκ k)
  · intro hκ
    rw [maximalPoint_eq_map_ringHom g]
    exact maximalPointMap_scalars (maximalPointRingHom g)
      (maximalPointRingHom_maximal_comap g) κR κS hκ

/-- The maximal-point Hom equivalence restricted to supplied scalar maps.
The target condition is compatibility of the global-section map, expressed
using its top component. The scalar ring need not share the universe of the
coordinate rings, and no algebra structure is replaced. -/
def maximalPointHomEquivScalars (κR : K →+* R) (κS : K →+* S) :
    {φ : R →+* S //
      (∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal → (n.asIdeal.comap φ).IsMaximal) ∧
        φ.comp κR = κS} ≃
      {g : maximalPointSpace S ⟶ maximalPointSpace R //
        (g.c.app (op ⊤)).hom.comp (maximalPointScalars R κR) =
          maximalPointScalars S κS} :=
  (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun φ : R →+* S => ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap φ).IsMaximal)
    (fun φ : R →+* S => φ.comp κR = κS)).symm.trans
      ((maximalPointHomEquiv R S).subtypeEquiv fun φ => by
        constructor
        · intro hκ
          exact maximalPointMap_scalars φ.val φ.property κR κS hκ
        · intro hκ
          ext k
          apply (maximalPointCoordinates S).injective
          exact (maximalPointMap_coordinates_apply φ.val φ.property (κR k)).symm.trans
            (RingHom.congr_fun hκ k))

/-- The scalar restriction retains the same forward maximal-point morphism. -/
@[simp]
lemma maximalPointHomEquivScalars_apply (κR : K →+* R) (κS : K →+* S)
    (φ : {φ : R →+* S //
      (∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal → (n.asIdeal.comap φ).IsMaximal) ∧
        φ.comp κR = κS}) :
    (maximalPointHomEquivScalars κR κS φ).val =
      maximalPointMap φ.val φ.property.1 := rfl

/-- The scalar restriction retains the same inverse ring map. -/
@[simp]
lemma maximalPointHomEquivScalars_symm_apply (κR : K →+* R) (κS : K →+* S)
    (g : {g : maximalPointSpace S ⟶ maximalPointSpace R //
      (g.c.app (op ⊤)).hom.comp (maximalPointScalars R κR) =
        maximalPointScalars S κS}) :
    ((maximalPointHomEquivScalars κR κS).symm g).val =
      maximalPointRingHom g.val := rfl

end SuppliedScalars

section OverSpectrum

-- The over category here has the common ambient universe of locally ringed spaces.
variable {K : Type u} [CommRing K]

set_option backward.isDefEq.respectTransparency false in
/-- A triangle over an affine spectrum is equivalent to the supplied
scalar equation for the recovered homomorphism. The scalar ring need not be
Jacobson, since the target is its full spectrum. -/
lemma maximalPointRingHom_over_iff (g : maximalPointSpace S ⟶ maximalPointSpace R)
    (κR : K →+* R) (κS : K →+* S) :
    g ≫ (maximalPointInclusion R ≫ locallyRingedSpaceMap (CommRingCat.ofHom κR)) =
        maximalPointInclusion S ≫ locallyRingedSpaceMap (CommRingCat.ofHom κS) ↔
      (maximalPointRingHom g).comp κR = κS := by
  constructor
  · intro h
    apply (maximalPointRingHom_scalars_iff g κR κS).mp
    have hΓ :
        LocallyRingedSpace.Γ.map (locallyRingedSpaceMap (CommRingCat.ofHom κR)).op ≫
            LocallyRingedSpace.Γ.map (maximalPointInclusion R).op ≫
              LocallyRingedSpace.Γ.map g.op =
          LocallyRingedSpace.Γ.map (locallyRingedSpaceMap (CommRingCat.ofHom κS)).op ≫
            LocallyRingedSpace.Γ.map (maximalPointInclusion S).op := by
      simpa only [op_comp, Functor.map_comp, Category.assoc] using
        congrArg
          (fun k : maximalPointSpace S ⟶ locallyRingedSpaceObj (CommRingCat.of K) =>
            LocallyRingedSpace.Γ.map k.op) h
    have hR : CommRingCat.ofHom (maximalPointCoordinates R).toRingHom =
        toSpecΓ (CommRingCat.of R) ≫
          LocallyRingedSpace.Γ.map (maximalPointInclusion R).op :=
      maximalPointCoordinates_hom R
    have hS : CommRingCat.ofHom (maximalPointCoordinates S).toRingHom =
        toSpecΓ (CommRingCat.of S) ≫
          LocallyRingedSpace.Γ.map (maximalPointInclusion S).op :=
      maximalPointCoordinates_hom S
    have hκR : CommRingCat.ofHom κR ≫ toSpecΓ (CommRingCat.of R) =
        toSpecΓ (CommRingCat.of K) ≫
          LocallyRingedSpace.Γ.map (locallyRingedSpaceMap (CommRingCat.ofHom κR)).op :=
      Spec_Γ_naturality (CommRingCat.ofHom κR)
    have hκS : CommRingCat.ofHom κS ≫ toSpecΓ (CommRingCat.of S) =
        toSpecΓ (CommRingCat.of K) ≫
          LocallyRingedSpace.Γ.map (locallyRingedSpaceMap (CommRingCat.ofHom κS)).op :=
      Spec_Γ_naturality (CommRingCat.ofHom κS)
    have hcoordinates :
        CommRingCat.ofHom κR ≫ CommRingCat.ofHom (maximalPointCoordinates R).toRingHom ≫
            LocallyRingedSpace.Γ.map g.op =
          CommRingCat.ofHom κS ≫
            CommRingCat.ofHom (maximalPointCoordinates S).toRingHom := by
      calc
        _ = (CommRingCat.ofHom κR ≫ toSpecΓ (CommRingCat.of R)) ≫
            LocallyRingedSpace.Γ.map (maximalPointInclusion R).op ≫
              LocallyRingedSpace.Γ.map g.op := by
          simp only [hR, Category.assoc]
        _ = (toSpecΓ (CommRingCat.of K) ≫
            LocallyRingedSpace.Γ.map (locallyRingedSpaceMap (CommRingCat.ofHom κR)).op) ≫
              LocallyRingedSpace.Γ.map (maximalPointInclusion R).op ≫
                LocallyRingedSpace.Γ.map g.op := by rw [hκR]
        _ = (toSpecΓ (CommRingCat.of K) ≫
            LocallyRingedSpace.Γ.map (locallyRingedSpaceMap (CommRingCat.ofHom κS)).op) ≫
              LocallyRingedSpace.Γ.map (maximalPointInclusion S).op := by
          simpa only [Category.assoc] using
            congrArg (fun k => toSpecΓ (CommRingCat.of K) ≫ k) hΓ
        _ = (CommRingCat.ofHom κS ≫ toSpecΓ (CommRingCat.of S)) ≫
            LocallyRingedSpace.Γ.map (maximalPointInclusion S).op := by rw [← hκS]
        _ = _ := by simp only [hS, Category.assoc]
    ext k
    exact congrArg (fun f => f k) hcoordinates
  · intro hκ
    calc
      g ≫ (maximalPointInclusion R ≫ locallyRingedSpaceMap (CommRingCat.ofHom κR)) =
          (g ≫ maximalPointInclusion R) ≫
            locallyRingedSpaceMap (CommRingCat.ofHom κR) := (Category.assoc _ _ _).symm
      _ = (maximalPointInclusion S ≫
            locallyRingedSpaceMap (CommRingCat.ofHom (maximalPointRingHom g))) ≫
            locallyRingedSpaceMap (CommRingCat.ofHom κR) := by
        rw [maximalPointRingHom_comp_inclusion]
      _ = maximalPointInclusion S ≫
            locallyRingedSpaceMap (CommRingCat.ofHom ((maximalPointRingHom g).comp κR)) := by
        rw [CommRingCat.ofHom_comp, locallyRingedSpaceMap_comp, Category.assoc]
      _ = _ := by rw [hκ]

variable [Algebra K R] [Algebra K S]

/-- Maximal-contraction-preserving homomorphisms for the given algebra actions
correspond to full morphisms over the affine spectrum of scalars. -/
def maximalPointAlgHomEquiv (K R S : Type u) [CommRing K] [CommRing R] [CommRing S]
    [IsJacobsonRing R] [IsJacobsonRing S] [Algebra K R] [Algebra K S] :
    {φ : R →ₐ[K] S // ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (φ : R →+* S)).IsMaximal} ≃
      (Over.mk (maximalPointInclusion S ≫
          locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap K S))) ⟶
        Over.mk (maximalPointInclusion R ≫
          locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap K R)))) where
  toFun φ := Over.homMk (maximalPointMap (φ.val : R →+* S) φ.property)
    ((maximalPointRingHom_over_iff _ (algebraMap K R) (algebraMap K S)).mpr (by
      rw [maximalPointRingHom_map]
      exact φ.val.comp_algebraMap))
  invFun g :=
    ⟨{ toRingHom := maximalPointRingHom g.left
       commutes' k := RingHom.congr_fun
         ((maximalPointRingHom_over_iff g.left (algebraMap K R) (algebraMap K S)).mp
           (Over.w g)) k },
      maximalPointRingHom_maximal_comap g.left⟩
  left_inv φ := by
    apply Subtype.ext
    apply AlgHom.ext
    intro r
    exact RingHom.congr_fun (maximalPointRingHom_map (φ.val : R →+* S) φ.property) r
  right_inv g := by
    apply Over.OverMorphism.ext
    exact (maximalPoint_eq_map_ringHom g.left).symm

/-- Forgetting the over-category triangle gives `maximalPointMap`. -/
@[simp]
lemma maximalPointAlgHomEquiv_apply_left
    (φ : {φ : R →ₐ[K] S // ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (φ : R →+* S)).IsMaximal}) :
    (maximalPointAlgHomEquiv K R S φ).left =
      maximalPointMap (φ.val : R →+* S) φ.property := rfl

/-- The inverse over-category equivalence recovers the ring map of the
underlying locally ringed space morphism. Its scalar linearity is derived. -/
@[simp]
lemma maximalPointAlgHomEquiv_symm_apply_toRingHom
    (g : Over.mk (maximalPointInclusion S ≫
        locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap K S))) ⟶
      Over.mk (maximalPointInclusion R ≫
        locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap K R)))) :
    (((maximalPointAlgHomEquiv K R S).symm g).val : R →+* S) =
      maximalPointRingHom g.left := rfl

variable [Algebra.FiniteType K S]

/-- For a finite-type target algebra every algebra homomorphism preserves
maximal contraction. Thus all algebra homomorphisms correspond to full maps of
maximal-point spaces over `Spec K`. No finite-type assumption on `R` is needed.
For finitely generated algebras over a field, the Jacobson hypotheses follow
from `isJacobsonRing_of_finiteType`. -/
def maximalPointAlgHomEquivOfFiniteType :
    (R →ₐ[K] S) ≃
      (Over.mk (maximalPointInclusion S ≫
          locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap K S))) ⟶
        Over.mk (maximalPointInclusion R ≫
          locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap K R)))) :=
  (Equiv.subtypeUnivEquiv (fun φ : R →ₐ[K] S => maximal_comap_of_algHom φ)).symm.trans
    (maximalPointAlgHomEquiv K R S)

/-- The finite-type specialization has `maximalPointMapOfAlgHom` as its
underlying locally ringed space morphism. -/
@[simp]
lemma maximalPointAlgHomEquivOfFiniteType_apply_left (φ : R →ₐ[K] S) :
    (maximalPointAlgHomEquivOfFiniteType (K := K) (R := R) (S := S) φ).left =
      maximalPointMapOfAlgHom φ := rfl

/-- The finite-type inverse uses the global-section readback. -/
@[simp]
lemma maximalPointAlgHomEquivOfFiniteType_symm_apply_toRingHom
    (g : Over.mk (maximalPointInclusion S ≫
        locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap K S))) ⟶
      Over.mk (maximalPointInclusion R ≫
        locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap K R)))) :
    ((maximalPointAlgHomEquivOfFiniteType (K := K) (R := R) (S := S)).symm g : R →+* S) =
      maximalPointRingHom g.left := rfl

end OverSpectrum

end AlgebraicGeometry.Spec
