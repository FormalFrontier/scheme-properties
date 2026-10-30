/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Closed points of scheme pullbacks over a field

For specified locally finite-type arrows to the spectrum of a field, the projections
of any specified pullback induce a surjective comparison on closed points. Over a
separably closed field this comparison is an equivalence, with inverse
`AlgebraicGeometry.Scheme.closedPointPair`. Projection, extensionality, uniqueness,
eta and fixed-base naturality laws characterize the pairing.

The equivalence is between sets. It is not a homeomorphism to the ordinary product
of the closed-point spaces. Neither quasi-compactness nor separation is required.
Closed points over an imperfect separably closed field need not be rational.

## Implementation notes

Surjectivity uses a nonempty closed fibre in the Jacobson ambient pullback.
Injectivity uses Mathlib's residue-tensor description of pullback points. All scalar
structures in that argument come from the specified arrows and their residue maps;
pure inseparability descends along the resulting scalar tower to the base residue field.

## References

* Mathlib's `Scheme.Pullback.carrierEquiv` and its projection laws.
* Mathlib's `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`.
* Formal Frontier, *Closed points of scheme products*, Sections 3–7: the
  closed-Jacobson-fibre and purely-inseparable residue-tensor arguments.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K]

/-- An arrow over a field preserves closed points if its original source and target
structure arrows are locally of finite type. No finiteness assumption on the arrow
itself is needed. -/
theorem Hom.mapsTo_closedPoints_of_comp_eq {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    (a : X ⟶ Y) (ha : a ≫ fY = fX) :
    Set.MapsTo a (closedPoints X) (closedPoints Y) := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace fY
  have : LocallyOfFiniteType (a ≫ fY) := ha.symm ▸ inferInstance
  have : LocallyOfFiniteType a := locallyOfFiniteType_of_comp a fY
  exact a.closePoints_subset_preimage_closedPoints

variable {P X Y : Scheme.{u}}
    (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    (πX : P ⟶ X) (πY : P ⟶ Y) (hP : IsPullback πX πY fX fY)

/-- The comparison from closed points of a specified scheme pullback to pairs of
closed points of its factors, induced by its original projections. -/
def closedPointProductComparison : closedPoints P → closedPoints X × closedPoints Y := by
  have : LocallyOfFiniteType πX := MorphismProperty.of_isPullback hP.flip inferInstance
  have : LocallyOfFiniteType πY := MorphismProperty.of_isPullback hP inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace fX
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace fY
  exact fun z ↦ (⟨πX z.val, πX.closePoints_subset_preimage_closedPoints z.property⟩,
    ⟨πY z.val, πY.closePoints_subset_preimage_closedPoints z.property⟩)

@[simp]
theorem closedPointProductComparison_fst (z : closedPoints P) :
    (closedPointProductComparison fX fY πX πY hP z).1.val = πX z.val := rfl

@[simp]
theorem closedPointProductComparison_snd (z : closedPoints P) :
    (closedPointProductComparison fX fY πX πY hP z).2.val = πY z.val := rfl

/-- Over every field, each pair of closed points has a closed point above it in the
specified scheme pullback. The proof uses a closed fibre in the Jacobson ambient
scheme, as in *Closed points of scheme products*, Section 6. -/
theorem closedPointProductComparison_surjective :
    Function.Surjective (closedPointProductComparison fX fY πX πY hP) := by
  have : LocallyOfFiniteType πX := MorphismProperty.of_isPullback hP.flip inferInstance
  have : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace (πX ≫ fX)
  rintro ⟨x, y⟩
  let F : Set P := πX ⁻¹' {x.val} ∩ πY ⁻¹' {y.val}
  have hF : IsClosed F :=
    (x.property.preimage πX.continuous).inter (y.property.preimage πY.continuous)
  have hn : F.Nonempty := by
    obtain ⟨z, hx, hy⟩ := exists_preimage_of_isPullback hP x.val y.val
      (Subsingleton.elim _ _)
    exact ⟨z, hx, hy⟩
  obtain ⟨z, hzF, hz⟩ := nonempty_inter_closedPoints hn hF.isLocallyClosed
  refine ⟨⟨z, hz⟩, Prod.ext (Subtype.ext hzF.1) (Subtype.ext hzF.2)⟩

private theorem residue_scalar_comp {Z : Scheme.{u}} (f : Z ⟶ Spec (.of K))
    (z : Z) (s : Spec (.of K)) (h : f z = s) :
    Spec.preimage ((Spec (.of K)).fromSpecResidueField s) ≫
        ((Spec (.of K)).residueFieldCongr h).inv ≫ f.residueFieldMap z =
      Spec.preimage (Z.fromSpecResidueField z ≫ f) := by
  subst s
  apply Spec.map_injective
  simp only [residueFieldCongr_refl, Iso.refl_inv, Category.id_comp,
    Spec.map_comp, Spec.map_preimage]
  exact f.SpecMap_residueFieldMap_fromSpecResidueField z

omit [LocallyOfFiniteType fX] in
private theorem tensor_spectrum_subsingleton [IsSepClosed K]
    (T : Pullback.Triplet fX fY) (hy : IsClosed {T.y}) :
    Subsingleton (Spec T.tensor) := by
  let B := (Spec (.of K)).residueField T.s
  let L := X.residueField T.x
  let M := Y.residueField T.y
  let β : CommRingCat.of K ⟶ B :=
    Spec.preimage ((Spec (.of K)).fromSpecResidueField T.s)
  let δx : B ⟶ L := ((Spec (.of K)).residueFieldCongr T.hx).inv ≫ fX.residueFieldMap T.x
  let δy : B ⟶ M := ((Spec (.of K)).residueFieldCongr T.hy).inv ≫ fY.residueFieldMap T.y
  let α : CommRingCat.of K ⟶ M := Spec.preimage (Y.fromSpecResidueField T.y ≫ fY)
  let : Algebra K B := β.hom.toAlgebra
  let : Algebra B L := δx.hom.toAlgebra
  let : Algebra B M := δy.hom.toAlgebra
  let : Algebra K M := α.hom.toAlgebra
  have hβα : β ≫ δy = α := residue_scalar_comp fY T.y T.s T.hy
  have : IsScalarTower K B M :=
    IsScalarTower.of_algebraMap_eq' (by
      change α.hom = δy.hom.comp β.hom
      exact (congrArg CommRingCat.Hom.hom hβα).symm)
  have : Module.Finite K M := by
    change α.hom.Finite
    rw [← IsFinite.SpecMap_iff, Spec.map_preimage]
    have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace fY
    have : IsClosedImmersion (Y.fromSpecResidueField T.y) :=
      isClosed_singleton_iff_isClosedImmersion.mp hy
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  have : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  have : IsPurelyInseparable K M := inferInstance
  have : IsPurelyInseparable B M := IsPurelyInseparable.tower_top K B M
  have : Subsingleton (PrimeSpectrum (L ⊗[B] M)) :=
    (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable B M L).injective.subsingleton
  let e : CommRingCat.of (L ⊗[B] M) ≅ T.tensor :=
    (CommRingCat.isPushout_tensorProduct B L M).isoPushout
  change Subsingleton (PrimeSpectrum T.tensor)
  refine ⟨fun p q ↦ ?_⟩
  exact (PrimeSpectrum.comapEquiv e.commRingCatIsoToRingEquiv).symm.injective
    (Subsingleton.elim _ _)

omit [LocallyOfFiniteType fX] in
private theorem pullback_point_ext [IsSepClosed K]
    (p q : ↑(pullback fX fY))
    (hp : IsClosed {pullback.snd fX fY p})
    (hx : pullback.fst fX fY p = pullback.fst fX fY q)
    (hy : pullback.snd fX fY p = pullback.snd fX fY q) : p = q := by
  obtain ⟨⟨T, t⟩, rfl⟩ := Pullback.carrierEquiv.symm.surjective p
  obtain ⟨⟨U, v⟩, rfl⟩ := Pullback.carrierEquiv.symm.surjective q
  simp only [Pullback.carrierEquiv_symm_fst, Pullback.carrierEquiv_symm_snd] at hx hy hp
  have hTU : T = U := Pullback.Triplet.ext hx hy
  subst U
  have := tensor_spectrum_subsingleton fX fY T hp
  exact congrArg (fun w ↦ Pullback.carrierEquiv.symm ⟨T, w⟩) (Subsingleton.elim t v)

/-- Over a separably closed field, the original projections distinguish closed
points of a specified scheme pullback. This uses the purely-inseparable tensor
argument of *Closed points of scheme products*, Sections 4–6. -/
theorem closedPointProductComparison_injective [IsSepClosed K] :
    Function.Injective (closedPointProductComparison fX fY πX πY hP) := by
  intro z w h
  have hx := congrArg (fun t : closedPoints X × closedPoints Y ↦ t.1.val) h
  have hy := congrArg (fun t : closedPoints X × closedPoints Y ↦ t.2.val) h
  simp only [closedPointProductComparison_fst] at hx
  simp only [closedPointProductComparison_snd] at hy
  have hz : IsClosed {(closedPointProductComparison fX fY πX πY hP z).2.val} :=
    (closedPointProductComparison fX fY πX πY hP z).2.property
  rw [closedPointProductComparison_snd] at hz
  apply Subtype.ext
  apply hP.isoPullback.hom.isOpenEmbedding.injective
  apply pullback_point_ext fX fY
  · simpa only [← Hom.comp_apply, hP.isoPullback_hom_snd] using hz
  · simpa only [← Hom.comp_apply, hP.isoPullback_hom_fst] using hx
  · simpa only [← Hom.comp_apply, hP.isoPullback_hom_snd] using hy

/-- Closed points of a specified scheme pullback over a separably closed field are
canonically equivalent to pairs of closed points of its factors. The forward map
is the comparison induced by the original projections. -/
def closedPointProductEquiv [IsSepClosed K] :
    closedPoints P ≃ closedPoints X × closedPoints Y :=
  Equiv.ofBijective (closedPointProductComparison fX fY πX πY hP)
    ⟨closedPointProductComparison_injective fX fY πX πY hP,
      closedPointProductComparison_surjective fX fY πX πY hP⟩

@[simp]
theorem closedPointProductEquiv_apply [IsSepClosed K] (z : closedPoints P) :
    closedPointProductEquiv fX fY πX πY hP z =
      closedPointProductComparison fX fY πX πY hP z := rfl

/-- The unique closed point of the specified scheme pullback above a pair of
closed points, over a separably closed field. -/
def closedPointPair [IsSepClosed K] (x : closedPoints X) (y : closedPoints Y) :
    closedPoints P := (closedPointProductEquiv fX fY πX πY hP).symm (x, y)

@[simp]
theorem closedPointProductComparison_pair [IsSepClosed K]
    (x : closedPoints X) (y : closedPoints Y) :
    closedPointProductComparison fX fY πX πY hP (closedPointPair fX fY πX πY hP x y) =
      (x, y) := (closedPointProductEquiv fX fY πX πY hP).apply_symm_apply (x, y)

@[simp]
theorem closedPointPair_fst [IsSepClosed K] (x : closedPoints X) (y : closedPoints Y) :
    πX (closedPointPair fX fY πX πY hP x y).val = x.val :=
  congrArg (fun t : closedPoints X × closedPoints Y ↦ t.1.val)
    (closedPointProductComparison_pair fX fY πX πY hP x y)

@[simp]
theorem closedPointPair_snd [IsSepClosed K] (x : closedPoints X) (y : closedPoints Y) :
    πY (closedPointPair fX fY πX πY hP x y).val = y.val :=
  congrArg (fun t : closedPoints X × closedPoints Y ↦ t.2.val)
    (closedPointProductComparison_pair fX fY πX πY hP x y)

include hP in
/-- Extensionality for closed points of the specified pullback, using its two
original projections. -/
theorem closedPointProduct_ext [IsSepClosed K] {z w : closedPoints P}
    (hx : πX z.val = πX w.val) (hy : πY z.val = πY w.val) : z = w :=
  closedPointProductComparison_injective fX fY πX πY hP
    (Prod.ext (Subtype.ext hx) (Subtype.ext hy))

/-- The projection equations characterize the pairing uniquely. -/
theorem closedPointPair_unique [IsSepClosed K]
    (x : closedPoints X) (y : closedPoints Y) (z : closedPoints P)
    (hx : πX z.val = x.val) (hy : πY z.val = y.val) :
    z = closedPointPair fX fY πX πY hP x y := by
  apply closedPointProduct_ext fX fY πX πY hP
  · simpa using hx
  · simpa using hy

@[simp]
theorem closedPointPair_eta [IsSepClosed K] (z : closedPoints P) :
    closedPointPair fX fY πX πY hP
      (closedPointProductComparison fX fY πX πY hP z).1
      (closedPointProductComparison fX fY πX πY hP z).2 = z :=
  (closedPointProductEquiv fX fY πX πY hP).symm_apply_apply z

section Naturality

variable {P' X' Y' : Scheme.{u}}
    (fX' : X' ⟶ Spec (.of K)) (fY' : Y' ⟶ Spec (.of K))
    [LocallyOfFiniteType fX'] [LocallyOfFiniteType fY']
    (πX' : P' ⟶ X') (πY' : P' ⟶ Y') (hP' : IsPullback πX' πY' fX' fY')

include hP hP' in
/-- An arrow between the specified pullbacks preserves closed points if it commutes
with one projection and its original scalar square. All local finite-type and
Jacobson facts are consequences of the specified squares. -/
theorem closedPointProduct_mapsTo (a : X ⟶ X') (c : P ⟶ P')
    (ha : a ≫ fX' = fX) (hc : c ≫ πX' = πX ≫ a) :
    Set.MapsTo c (closedPoints P) (closedPoints P') := by
  have : LocallyOfFiniteType πX := MorphismProperty.of_isPullback hP.flip inferInstance
  have : LocallyOfFiniteType πX' := MorphismProperty.of_isPullback hP'.flip inferInstance
  apply Hom.mapsTo_closedPoints_of_comp_eq (πX ≫ fX) (πX' ≫ fX') c
  rw [← Category.assoc, hc, Category.assoc, ha]

/-- The comparison commutes with the closed-point restrictions of the original
arrows in two specified pullback squares over the same field. -/
theorem closedPointProductComparison_naturality
    (a : X ⟶ X') (b : Y ⟶ Y') (c : P ⟶ P')
    (ha : a ≫ fX' = fX) (hb : b ≫ fY' = fY)
    (hcX : c ≫ πX' = πX ≫ a) (hcY : c ≫ πY' = πY ≫ b)
    (z : closedPoints P) :
    closedPointProductComparison fX' fY' πX' πY' hP'
        ⟨c z.val, closedPointProduct_mapsTo fX fY πX πY hP
          fX' fY' πX' πY' hP' a c ha hcX z.property⟩ =
      (⟨a (closedPointProductComparison fX fY πX πY hP z).1.val,
          Hom.mapsTo_closedPoints_of_comp_eq fX fX' a ha
            (closedPointProductComparison fX fY πX πY hP z).1.property⟩,
       ⟨b (closedPointProductComparison fX fY πX πY hP z).2.val,
          Hom.mapsTo_closedPoints_of_comp_eq fY fY' b hb
            (closedPointProductComparison fX fY πX πY hP z).2.property⟩) := by
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg (fun f : P ⟶ X' ↦ f z.val) hcX
  · exact congrArg (fun f : P ⟶ Y' ↦ f z.val) hcY

/-- Pairing commutes with the closed-point restrictions of the original arrows
in two specified pullback squares over a separably closed field. -/
theorem closedPointPair_naturality [IsSepClosed K]
    (a : X ⟶ X') (b : Y ⟶ Y') (c : P ⟶ P')
    (ha : a ≫ fX' = fX) (hb : b ≫ fY' = fY)
    (hcX : c ≫ πX' = πX ≫ a) (hcY : c ≫ πY' = πY ≫ b)
    (x : closedPoints X) (y : closedPoints Y) :
    (⟨c (closedPointPair fX fY πX πY hP x y).val,
        closedPointProduct_mapsTo fX fY πX πY hP fX' fY' πX' πY' hP' a c ha hcX
          (closedPointPair fX fY πX πY hP x y).property⟩ : closedPoints P') =
      closedPointPair fX' fY' πX' πY' hP'
        ⟨a x.val, Hom.mapsTo_closedPoints_of_comp_eq fX fX' a ha x.property⟩
        ⟨b y.val, Hom.mapsTo_closedPoints_of_comp_eq fY fY' b hb y.property⟩ := by
  apply closedPointPair_unique fX' fY' πX' πY' hP'
  · change πX' (c _) = a x.val
    rw [← Hom.comp_apply, hcX, Hom.comp_apply, closedPointPair_fst]
  · change πY' (c _) = b y.val
    rw [← Hom.comp_apply, hcY, Hom.comp_apply, closedPointPair_snd]

end Naturality

/-- A specified diagonal arrow sends a closed point to its pair with itself.
This identifies the closed-point diagonal using the scheme pullback, without
asserting anything about the ordinary product topology. -/
theorem closedPointPair_diagonal [IsSepClosed K] {P X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (π₁ π₂ : P ⟶ X) (h : IsPullback π₁ π₂ f f)
    (d : X ⟶ P) (hd₁ : d ≫ π₁ = 𝟙 X) (hd₂ : d ≫ π₂ = 𝟙 X)
    (x : closedPoints X) : d x.val = (closedPointPair f f π₁ π₂ h x x).val := by
  have : LocallyOfFiniteType π₁ := MorphismProperty.of_isPullback h.flip inferInstance
  have hd : d ≫ (π₁ ≫ f) = f := by rw [← Category.assoc, hd₁, Category.id_comp]
  have hx := Hom.mapsTo_closedPoints_of_comp_eq f (π₁ ≫ f) d hd x.property
  exact congrArg Subtype.val (closedPointPair_unique f f π₁ π₂ h x x ⟨d x.val, hx⟩
    (by rw [← Hom.comp_apply, hd₁]; rfl)
    (by rw [← Hom.comp_apply, hd₂]; rfl))

end AlgebraicGeometry.Scheme
