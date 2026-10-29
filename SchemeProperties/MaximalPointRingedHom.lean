/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.MaximalPointSheafMaps

/-!
# Locality of ringed morphisms between maximal-point spaces

A full ringed-space morphism from the maximal-point space of `S` to that of
`R`, for Jacobson rings `R` and `S`, determines a homomorphism `R →+* S` of
coordinate rings. Naturality of germs and preservation of units imply that
contraction of a source point is contained in its given image. If those
contractions are maximal, the points agree and uniqueness of the full sheaf
component identifies the original morphism with `maximalPointMap`. In
particular, the original morphism is local.

`maximalPointRingedHomLift` equips that same ringed morphism with its derived
locality proof. It is inverse to forgetting locality and respects composition.
For the given algebra structures over any commutative ring `K`, finite type
of `S` over `K` makes every scalar-compatible ringed morphism local; no
finite-type assumption on `R` is needed. Here `S` is the coordinate ring of
the source space and the codomain of the coordinate homomorphism `R →+* S`.

All sections and stalks are the full rings, including nilpotents. The zero
ring is allowed. Stalk and principal-open localization readbacks follow from
`maximalPointRingedHomLift_eq_map` and the existing `maximalPointMap` API.

## References

The argument uses Mathlib's naturality of germs, its unit criterion for prime
localizations, and its constructor for locally ringed space morphisms. Full
component uniqueness and localization comparisons are those of
`SchemeProperties.MaximalPointSheafMaps` and `SchemeProperties.MaximalPointMorphisms`.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory TopCat TopologicalSpace Opposite

namespace AlgebraicGeometry.Spec

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [IsJacobsonRing R] [IsJacobsonRing S] [IsJacobsonRing T]

/-- The original global-section map in the coordinate rings, without any
locality assumption on the ringed-space morphism. -/
def maximalPointRingedHomCoordinates
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace) :
    R →+* S :=
  (maximalPointCoordinates S).symm.toRingHom.comp
    ((SheafedSpace.Γ.map g.op).hom.comp (maximalPointCoordinates R).toRingHom)

/-- Evaluation of the original top component on a coordinate element. -/
lemma maximalPointRingedHomCoordinates_apply
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (r : R) :
    g.hom.c.app (op ⊤) (maximalPointCoordinates R r) =
      maximalPointCoordinates S (maximalPointRingedHomCoordinates g r) := by
  change _ = maximalPointCoordinates S ((maximalPointCoordinates S).symm _)
  exact ((maximalPointCoordinates S).apply_symm_apply _).symm

/-- The global coordinate square of an arbitrary ringed morphism. -/
lemma maximalPointRingedHomCoordinates_coordinates
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace) :
    CommRingCat.ofHom (maximalPointCoordinates R).toRingHom ≫ g.hom.c.app (op ⊤) =
      CommRingCat.ofHom (maximalPointRingedHomCoordinates g) ≫
        CommRingCat.ofHom (maximalPointCoordinates S).toRingHom := by
  apply CommRingCat.hom_ext
  ext r
  exact maximalPointRingedHomCoordinates_apply g r

set_option backward.isDefEq.respectTransparency false in
/-- The original stalk map preserves the original global coordinate map.
This germ square does not assume locality. -/
lemma maximalPointRingedHom_stalkMap_algebraMap
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (n : maximalPointSpace S) (r : R) :
    g.hom.stalkMap n (algebraMap R _ r) =
      algebraMap S _ (maximalPointRingedHomCoordinates g r) := by
  have h := PresheafedSpace.stalkMap_germ_apply g.hom ⊤ n
    (Opens.mem_top (g.hom.base n))
    (maximalPointCoordinates R r)
  have hR : (maximalPointSpace R).presheaf.germ ⊤ (g.hom.base n)
      (Opens.mem_top _) (maximalPointCoordinates R r) = algebraMap R _ r := by
    rw [maximalPointCoordinates_apply]
    exact maximalPoint_germ_algebraMap R ⊤ _ _ r
  have hS : (maximalPointSpace S).presheaf.germ ⊤ n (Opens.mem_top _)
      (g.hom.c.app (op ⊤) (maximalPointCoordinates R r)) =
        algebraMap S _ (maximalPointRingedHomCoordinates g r) := by
    calc
      _ = (maximalPointSpace S).presheaf.germ ⊤ n (Opens.mem_top _)
          (maximalPointCoordinates S (maximalPointRingedHomCoordinates g r)) :=
        congrArg ((maximalPointSpace S).presheaf.germ ⊤ n (Opens.mem_top _))
          (maximalPointRingedHomCoordinates_apply g r)
      _ = _ := by
        rw [maximalPointCoordinates_apply]
        exact maximalPoint_germ_algebraMap S ⊤ n _ _
  exact (congrArg (g.hom.stalkMap n) hR).symm.trans (h.trans hS)

/-- Preservation of stalk units gives containment of contraction in the
original image point, even when the morphism is not local. -/
lemma maximalPointRingedHom_comap_le
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (n : maximalPointSpace S) :
    n.val.asIdeal.comap (maximalPointRingedHomCoordinates g) ≤
      (g.hom.base n).val.asIdeal := by
  intro r hr
  by_contra hm
  have hu : IsUnit (algebraMap R ((maximalPointSpace R).presheaf.stalk (g.hom.base n)) r) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff _ (g.hom.base n).val.asIdeal r).mpr hm
  have hv := hu.map (g.hom.stalkMap n).hom
  rw [maximalPointRingedHom_stalkMap_algebraMap] at hv
  exact ((IsLocalization.AtPrime.isUnit_to_map_iff _ n.val.asIdeal _).mp hv) hr

/-- Maximality of the original coordinate contraction recovers the given
point map. -/
lemma maximalPointRingedHom_base_apply
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hg : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (maximalPointRingedHomCoordinates g)).IsMaximal)
    (n : maximalPointSpace S) :
    (g.hom.base n).val = PrimeSpectrum.comap (maximalPointRingedHomCoordinates g) n.val := by
  apply PrimeSpectrum.ext
  exact ((hg n.val inferInstance).eq_of_le
    (inferInstance : (g.hom.base n).val.asIdeal.IsMaximal).ne_top
    (maximalPointRingedHom_comap_le g n)).symm

private lemma maximalPointRingedHom_ext {Y : SheafedSpace CommRingCat.{u}}
    (g h : Y ⟶ (maximalPointSpace R).toRingedSpace)
    (hbase : g.hom.base = h.hom.base)
    (hΓ : SheafedSpace.Γ.map g.op = SheafedSpace.Γ.map h.op) : g = h := by
  rcases g with ⟨⟨f, α⟩⟩
  rcases h with ⟨⟨f', β⟩⟩
  change f = f' at hbase
  subst f'
  change α.app (op ⊤) = β.app (op ⊤) at hΓ
  have hα : α = β := by
    apply maximalPoint_component_ext R Y.sheaf f
    exact congrArg (fun k => CommRingCat.ofHom (maximalPointCoordinates R).toRingHom ≫ k) hΓ
  subst β
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- When coordinate contractions are maximal, the entire original ringed
morphism is the forgotten maximal-point construction. The proof uses full
component uniqueness only after recovering the base map. -/
lemma maximalPointRingedHom_eq_map
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hg : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (maximalPointRingedHomCoordinates g)).IsMaximal) :
    g = (maximalPointMap (maximalPointRingedHomCoordinates g) hg).toShHom := by
  have hbase : g.hom.base = (maximalPointMap (maximalPointRingedHomCoordinates g) hg).base := by
    ext n
    apply Subtype.ext
    exact maximalPointRingedHom_base_apply g hg n
  apply maximalPointRingedHom_ext g
    (maximalPointMap (maximalPointRingedHomCoordinates g) hg).toShHom hbase
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  obtain ⟨r, rfl⟩ := (maximalPointCoordinates R).surjective s
  exact (maximalPointRingedHomCoordinates_apply g r).trans
    (maximalPointMap_coordinates_apply (maximalPointRingedHomCoordinates g) hg r).symm

private lemma maximalPointRingedHom_comap_eq_of_isLocal
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hlocal : ∀ n : maximalPointSpace S, IsLocalHom (g.hom.stalkMap n).hom)
    (n : maximalPointSpace S) :
    n.val.asIdeal.comap (maximalPointRingedHomCoordinates g) = (g.hom.base n).val.asIdeal := by
  let := hlocal n
  ext r
  have hu : IsUnit (algebraMap S ((maximalPointSpace S).presheaf.stalk n)
      (maximalPointRingedHomCoordinates g r)) ↔
      IsUnit (algebraMap R ((maximalPointSpace R).presheaf.stalk (g.hom.base n)) r) := by
    rw [← maximalPointRingedHom_stalkMap_algebraMap]
    exact isUnit_map_iff (g.hom.stalkMap n).hom _
  have hn : maximalPointRingedHomCoordinates g r ∉ n.val.asIdeal ↔
      r ∉ (g.hom.base n).val.asIdeal := by
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ n.val.asIdeal _).symm.trans
      (hu.trans (IsLocalization.AtPrime.isUnit_to_map_iff _ (g.hom.base n).val.asIdeal r))
  exact not_iff_not.mp hn

/-- A full ringed morphism of maximal-point spaces is local exactly when its
original coordinate homomorphism preserves maximal ideals under contraction.
The converse uses reflection of units in the original stalk maps. -/
lemma maximalPointRingedHom_isLocal_iff
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace) :
    (∀ n : maximalPointSpace S, IsLocalHom (g.hom.stalkMap n).hom) ↔
      ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
        (n.asIdeal.comap (maximalPointRingedHomCoordinates g)).IsMaximal := by
  constructor
  · intro hlocal n hn
    let x : maximalPointSpace S :=
      ⟨n, (PrimeSpectrum.isClosed_singleton_iff_isMaximal n).mpr hn⟩
    have hx := maximalPointRingedHom_comap_eq_of_isLocal g hlocal x
    change (x.val.asIdeal.comap (maximalPointRingedHomCoordinates g)).IsMaximal
    rw [hx]
    infer_instance
  · intro hg
    rw [maximalPointRingedHom_eq_map g hg]
    intro n
    exact (maximalPointMap (maximalPointRingedHomCoordinates g) hg).prop n

/-- Equip the supplied ringed morphism with its derived locality proof.
Its underlying presheafed-space morphism is definitionally the supplied one. -/
def maximalPointRingedHomLift
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hg : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (maximalPointRingedHomCoordinates g)).IsMaximal) :
    maximalPointSpace S ⟶ maximalPointSpace R :=
  LocallyRingedSpace.homMk g ((maximalPointRingedHom_isLocal_iff g).mpr hg)

/-- The lift retains the original full presheafed-space morphism. -/
@[simp]
lemma maximalPointRingedHomLift_toHom
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hg : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (maximalPointRingedHomCoordinates g)).IsMaximal) :
    (maximalPointRingedHomLift g hg).toHom = g.hom := rfl

/-- Forgetting locality from the lift returns the same ringed morphism. -/
@[simp]
lemma maximalPointRingedHomLift_toShHom
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hg : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (maximalPointRingedHomCoordinates g)).IsMaximal) :
    (maximalPointRingedHomLift g hg).toShHom = g := rfl

/-- The lift equals the public maximal-point construction. This equality
transports all of its section, stalk and localization readbacks. -/
lemma maximalPointRingedHomLift_eq_map
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hg : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (maximalPointRingedHomCoordinates g)).IsMaximal) :
    maximalPointRingedHomLift g hg = maximalPointMap (maximalPointRingedHomCoordinates g) hg := by
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  exact maximalPointRingedHom_eq_map g hg

/-- There is at most one locally ringed space lift of the supplied full
ringed morphism. -/
lemma maximalPointRingedHomLift_unique
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hg : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (maximalPointRingedHomCoordinates g)).IsMaximal)
    (f : maximalPointSpace S ⟶ maximalPointSpace R) (hf : f.toShHom = g) :
    f = maximalPointRingedHomLift g hg := by
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  exact hf

/-- Forgetting locality leaves coordinate contractions maximal. -/
lemma maximalPointRingedHom_preservesMaximal_of_locallyRinged
    (f : maximalPointSpace S ⟶ maximalPointSpace R) :
    ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (maximalPointRingedHomCoordinates f.toShHom)).IsMaximal :=
  (maximalPointRingedHom_isLocal_iff f.toShHom).mp (fun n => f.prop n)

/-- Lifting after forgetting locality returns the original locally ringed
space morphism. -/
@[simp]
lemma maximalPointRingedHomLift_of_toShHom (f : maximalPointSpace S ⟶ maximalPointSpace R) :
    maximalPointRingedHomLift f.toShHom
      (maximalPointRingedHom_preservesMaximal_of_locallyRinged f) = f :=
  (maximalPointRingedHomLift_unique _ _ f rfl).symm

set_option backward.isDefEq.respectTransparency false in
/-- Coordinates of the forgotten maximal-point construction are the given
ring homomorphism, including its action on nilpotents. -/
@[simp]
lemma maximalPointRingedHomCoordinates_map (φ : R →+* S)
    (hφ : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal → (n.asIdeal.comap φ).IsMaximal) :
    maximalPointRingedHomCoordinates (maximalPointMap φ hφ).toShHom = φ := by
  ext r
  apply (maximalPointCoordinates S).injective
  exact (maximalPointRingedHomCoordinates_apply (maximalPointMap φ hφ).toShHom r).symm.trans
    (maximalPointMap_coordinates_apply φ hφ r)

set_option backward.isDefEq.respectTransparency false in
/-- Original global coordinates are contravariantly compatible with
composition of the original ringed morphisms. -/
lemma maximalPointRingedHomCoordinates_comp
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (h : (maximalPointSpace T).toRingedSpace ⟶ (maximalPointSpace S).toRingedSpace) :
    maximalPointRingedHomCoordinates (h ≫ g) =
      (maximalPointRingedHomCoordinates h).comp (maximalPointRingedHomCoordinates g) := by
  ext r
  apply (maximalPointCoordinates T).injective
  rw [← maximalPointRingedHomCoordinates_apply]
  rw [SheafedSpace.comp_hom_c_app']
  change h.hom.c.app (op ⊤) (g.hom.c.app (op ⊤) (maximalPointCoordinates R r)) = _
  rw [maximalPointRingedHomCoordinates_apply, maximalPointRingedHomCoordinates_apply]
  rfl

/-- Maximal-contraction preservation composes for the original coordinates. -/
lemma maximalPointRingedHom_preservesMaximal_comp
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (h : (maximalPointSpace T).toRingedSpace ⟶ (maximalPointSpace S).toRingedSpace)
    (hg : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (maximalPointRingedHomCoordinates g)).IsMaximal)
    (hh : ∀ n : PrimeSpectrum T, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (maximalPointRingedHomCoordinates h)).IsMaximal) :
    ∀ n : PrimeSpectrum T, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (maximalPointRingedHomCoordinates (h ≫ g))).IsMaximal := by
  intro n hn
  rw [maximalPointRingedHomCoordinates_comp, ← Ideal.comap_comap]
  exact hg (PrimeSpectrum.comap (maximalPointRingedHomCoordinates h) n) (hh n hn)

/-- The canonical lift respects the composition of the same original arrows. -/
lemma maximalPointRingedHomLift_comp
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (h : (maximalPointSpace T).toRingedSpace ⟶ (maximalPointSpace S).toRingedSpace)
    (hg : ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (maximalPointRingedHomCoordinates g)).IsMaximal)
    (hh : ∀ n : PrimeSpectrum T, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (maximalPointRingedHomCoordinates h)).IsMaximal) :
    maximalPointRingedHomLift (h ≫ g)
        (maximalPointRingedHom_preservesMaximal_comp g h hg hh) =
      maximalPointRingedHomLift h hh ≫ maximalPointRingedHomLift g hg := by
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  rfl

section Scalars

variable {K : Type v} [CommRing K] [Algebra K R] [Algebra K S]

/-- Bundle the same original coordinate homomorphism as an algebra homomorphism
for the given scalar actions, using compatibility of the original top component. -/
def maximalPointRingedHomCoordinatesAlgHom
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hK : (g.hom.c.app (op ⊤)).hom.comp (maximalPointScalars R (algebraMap K R)) =
      maximalPointScalars S (algebraMap K S)) : R →ₐ[K] S where
  toRingHom := maximalPointRingedHomCoordinates g
  commutes' k := by
    apply (maximalPointCoordinates S).injective
    exact (maximalPointRingedHomCoordinates_apply g (algebraMap K R k)).symm.trans
      (RingHom.congr_fun hK k)

/-- Bundling scalar compatibility changes no coordinate ring homomorphism. -/
@[simp]
lemma maximalPointRingedHomCoordinatesAlgHom_toRingHom
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hK : (g.hom.c.app (op ⊤)).hom.comp (maximalPointScalars R (algebraMap K R)) =
      maximalPointScalars S (algebraMap K S)) :
    (maximalPointRingedHomCoordinatesAlgHom g hK : R →+* S) =
      maximalPointRingedHomCoordinates g := rfl

variable [Algebra.FiniteType K S]

/-- Finite type of `S` over `K` forces the original coordinate map to preserve
maximal contraction. The scalar ring may be any commutative ring. -/
lemma maximalPointRingedHom_preservesMaximal_of_scalars
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hK : (g.hom.c.app (op ⊤)).hom.comp (maximalPointScalars R (algebraMap K R)) =
      maximalPointScalars S (algebraMap K S)) :
    ∀ n : PrimeSpectrum S, n.asIdeal.IsMaximal →
      (n.asIdeal.comap (maximalPointRingedHomCoordinates g)).IsMaximal :=
  maximal_comap_of_algHom (maximalPointRingedHomCoordinatesAlgHom g hK)

/-- Every scalar-compatible full ringed morphism is local when `S` is finite
type over the given commutative scalar ring `K`.
Neither locality nor maximal preservation is a premise. -/
lemma maximalPointRingedHom_isLocal_of_scalars
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hK : (g.hom.c.app (op ⊤)).hom.comp (maximalPointScalars R (algebraMap K R)) =
      maximalPointScalars S (algebraMap K S)) :
    ∀ n : maximalPointSpace S, IsLocalHom (g.hom.stalkMap n).hom :=
  (maximalPointRingedHom_isLocal_iff g).mpr
    (maximalPointRingedHom_preservesMaximal_of_scalars g hK)

/-- The canonical locally ringed lift of the same scalar-compatible ringed
morphism, with locality derived from finite type of `S` over `K`. -/
def maximalPointRingedHomLiftOfScalars
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hK : (g.hom.c.app (op ⊤)).hom.comp (maximalPointScalars R (algebraMap K R)) =
      maximalPointScalars S (algebraMap K S)) : maximalPointSpace S ⟶ maximalPointSpace R :=
  maximalPointRingedHomLift g (maximalPointRingedHom_preservesMaximal_of_scalars g hK)

/-- The scalar lift retains the whole original presheafed-space morphism. -/
@[simp]
lemma maximalPointRingedHomLiftOfScalars_toHom
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hK : (g.hom.c.app (op ⊤)).hom.comp (maximalPointScalars R (algebraMap K R)) =
      maximalPointScalars S (algebraMap K S)) :
    (maximalPointRingedHomLiftOfScalars g hK).toHom = g.hom := rfl

/-- Forgetting the scalar lift returns the same original ringed morphism. -/
@[simp]
lemma maximalPointRingedHomLiftOfScalars_toShHom
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hK : (g.hom.c.app (op ⊤)).hom.comp (maximalPointScalars R (algebraMap K R)) =
      maximalPointScalars S (algebraMap K S)) :
    (maximalPointRingedHomLiftOfScalars g hK).toShHom = g := rfl

/-- The scalar lift is the existing algebra-homomorphism construction, so its
full open, stalk, inclusion and scalar readbacks apply without new providers. -/
lemma maximalPointRingedHomLiftOfScalars_eq_mapOfAlgHom
    (g : (maximalPointSpace S).toRingedSpace ⟶ (maximalPointSpace R).toRingedSpace)
    (hK : (g.hom.c.app (op ⊤)).hom.comp (maximalPointScalars R (algebraMap K R)) =
      maximalPointScalars S (algebraMap K S)) :
    maximalPointRingedHomLiftOfScalars g hK =
      maximalPointMapOfAlgHom (maximalPointRingedHomCoordinatesAlgHom g hK) :=
  maximalPointRingedHomLift_eq_map _ _

end Scalars

end AlgebraicGeometry.Spec
