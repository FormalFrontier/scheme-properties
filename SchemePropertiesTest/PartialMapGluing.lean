/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SchemeProperties.PartialMapGluing
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Prime.Int

/-!
# Compatible affine-line sections on a strict two-open cover

On `Spec ℤ`, the principal opens `D(2)` and `D(3)` are dense and proper, and their
union is the whole scheme. Their inclusions give compatible partial identities.
These source facts supply the strict cover for partial maps into the affine line
`Spec (Polynomial ℤ)`.

Evaluation at zero and one induces two distinct sections of the affine-line
projection. Faithfulness of `Spec` and evaluation of `Polynomial.X` distinguish
them, so the morphisms from `Spec ℤ` to this target are not a subsingleton. The
zero section also separates the points `(0)` and `(2)`: projecting their images
recovers the distinct original points.

Postcomposing the partial identities with the zero section gives full scheme-
morphism compatibility on the intersection. The zero section as a total partial
map is an independent witness on the union, with full morphism restrictions and
equalities of restricted partial maps. These facts use only spectrum maps,
composition, restriction and open inclusions, not gluing characteristic laws.
Within this independent model, gluing the first partial section with the morphism on the second
open is used only through its domain projection to exhibit strict growth from both
input domains and the exact whole-source domain. The partial-identity construction
also retains a proper self-gluing boundary. A compatible zero section on the empty
open gives a second boundary: that open is not dense in `Spec ℤ`, and adjoining it
leaves the first domain unchanged.

Subsequent characteristic-law applications identify the glued morphisms with the restriction
of the total zero section, recover the local sections and preserve the affine-line projection.
All declarations are private; this module introduces no public gluing API.
-/

open CategoryTheory AlgebraicGeometry

namespace SchemePropertiesTest.PartialMapGluing

private noncomputable abbrev integerSpectrum : Scheme := Spec (.of ℤ)

private def integerBasicOpen (n : ℤ) : integerSpectrum.Opens :=
  PrimeSpectrum.basicOpen n

private theorem integerBasicOpen_dense {n : ℤ} (hn : n ≠ 0) :
    Dense (integerBasicOpen n : Set integerSpectrum) := by
  apply (integerBasicOpen n).isOpen.dense
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℤ), ?_⟩
  change n ∉ (⊥ : Ideal ℤ)
  simpa only [Ideal.mem_bot] using hn

private theorem integerBasicOpen_ne_top {n : ℤ} (hn : Prime n) :
    integerBasicOpen n ≠ ⊤ := by
  intro h
  let x : integerSpectrum :=
    ⟨Ideal.span {n}, Ideal.isPrime_span_singleton_of_prime hn⟩
  have hx : x ∈ integerBasicOpen n := by
    rw [h]
    trivial
  change n ∉ Ideal.span ({n} : Set ℤ) at hx
  exact hx (Ideal.subset_span (Set.mem_singleton n))

private theorem integerBasicOpen_two_sup_three :
    integerBasicOpen 2 ⊔ integerBasicOpen 3 = ⊤ := by
  apply top_unique
  intro x _
  change (2 : ℤ) ∉ x.asIdeal ∨ (3 : ℤ) ∉ x.asIdeal
  by_cases h2 : (2 : ℤ) ∈ x.asIdeal
  · right
    intro h3
    have h1 : (1 : ℤ) ∈ x.asIdeal := by
      simpa only [show (3 : ℤ) - 2 = 1 from rfl] using x.asIdeal.sub_mem h3 h2
    exact x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · exact Or.inl h2

private noncomputable def awayTwoIdentity : integerSpectrum.PartialMap integerSpectrum where
  domain := integerBasicOpen 2
  dense_domain := integerBasicOpen_dense (by decide)
  hom := (integerBasicOpen 2).ι

private noncomputable def awayThreeIdentity : integerSpectrum.PartialMap integerSpectrum where
  domain := integerBasicOpen 3
  dense_domain := integerBasicOpen_dense (by decide)
  hom := (integerBasicOpen 3).ι

private theorem awayTwoIdentity_awayThreeIdentity_strict_cover :
    Dense (awayTwoIdentity.domain : Set integerSpectrum) ∧
      Dense (awayThreeIdentity.domain : Set integerSpectrum) ∧
      awayTwoIdentity.domain < awayTwoIdentity.domain ⊔ awayThreeIdentity.domain ∧
      awayThreeIdentity.domain < awayTwoIdentity.domain ⊔ awayThreeIdentity.domain ∧
      awayTwoIdentity.domain ⊔ awayThreeIdentity.domain = ⊤ := by
  refine ⟨awayTwoIdentity.dense_domain, awayThreeIdentity.dense_domain, ?_, ?_,
    integerBasicOpen_two_sup_three⟩
  · change integerBasicOpen 2 < integerBasicOpen 2 ⊔ integerBasicOpen 3
    rw [integerBasicOpen_two_sup_three]
    exact lt_top_iff_ne_top.mpr (integerBasicOpen_ne_top Int.prime_two)
  · change integerBasicOpen 3 < integerBasicOpen 2 ⊔ integerBasicOpen 3
    rw [integerBasicOpen_two_sup_three]
    exact lt_top_iff_ne_top.mpr (integerBasicOpen_ne_top Int.prime_three)

private theorem awayTwoIdentity_compatible_awayThreeIdentity :
    integerSpectrum.homOfLE
        (inf_le_left : awayTwoIdentity.domain ⊓ awayThreeIdentity.domain ≤
          awayTwoIdentity.domain) ≫ awayTwoIdentity.hom =
      integerSpectrum.homOfLE
        (inf_le_right : awayTwoIdentity.domain ⊓ awayThreeIdentity.domain ≤
          awayThreeIdentity.domain) ≫ awayThreeIdentity.hom := by
  change integerSpectrum.homOfLE
      (inf_le_left : integerBasicOpen 2 ⊓ integerBasicOpen 3 ≤ integerBasicOpen 2) ≫
        (integerBasicOpen 2).ι =
    integerSpectrum.homOfLE
      (inf_le_right : integerBasicOpen 2 ⊓ integerBasicOpen 3 ≤ integerBasicOpen 3) ≫
        (integerBasicOpen 3).ι
  rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]

private theorem integerSpectrum_identity_separates_points :
    ∃ x y : integerSpectrum, (𝟙 integerSpectrum) x ≠ (𝟙 integerSpectrum) y := by
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩,
    ⟨Ideal.span {(2 : ℤ)}, Ideal.isPrime_span_singleton_of_prime Int.prime_two⟩, ?_⟩
  intro h
  have hi : (⊥ : Ideal ℤ) = Ideal.span {(2 : ℤ)} := congrArg PrimeSpectrum.asIdeal h
  have h2 : (2 : ℤ) ∈ (⊥ : Ideal ℤ) := by
    rw [hi]
    exact Ideal.subset_span (Set.mem_singleton 2)
  exact (by decide : (2 : ℤ) ≠ 0) (Ideal.mem_bot.mp h2)

private theorem awayTwoIdentity_glue_self_domain :
    (awayTwoIdentity.glue awayTwoIdentity (by rfl)).domain = awayTwoIdentity.domain := by
  rw [Scheme.PartialMap.glue_domain]
  exact sup_idem awayTwoIdentity.domain

private noncomputable abbrev integerAffineLine : Scheme := Spec (.of (Polynomial ℤ))

private noncomputable def integerEvaluationSection (n : ℤ) :
    integerSpectrum ⟶ integerAffineLine :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom n))

private noncomputable abbrev zeroSection : integerSpectrum ⟶ integerAffineLine :=
  integerEvaluationSection 0

private noncomputable abbrev oneSection : integerSpectrum ⟶ integerAffineLine :=
  integerEvaluationSection 1

private noncomputable def affineLineProjection : integerAffineLine ⟶ integerSpectrum :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : ℤ →+* Polynomial ℤ))

private theorem integerEvaluationSection_projection (n : ℤ) :
    integerEvaluationSection n ≫ affineLineProjection = 𝟙 integerSpectrum := by
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom n)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : ℤ →+* Polynomial ℤ)) = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (Polynomial.C : ℤ →+* Polynomial ℤ) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom n) = 𝟙 (CommRingCat.of ℤ) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change (Polynomial.C a).eval n = a
    exact Polynomial.eval_C
  rw [h, Spec.map_id]

private theorem zeroSection_ne_oneSection : zeroSection ≠ oneSection := by
  intro h
  have he : CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℤ)) =
      CommRingCat.ofHom (Polynomial.evalRingHom (1 : ℤ)) :=
    Spec.map_injective h
  have hX := congrArg
    (fun f : CommRingCat.of (Polynomial ℤ) ⟶ CommRingCat.of ℤ =>
      f.hom (Polynomial.X : Polynomial ℤ)) he
  change (Polynomial.X : Polynomial ℤ).eval (0 : ℤ) =
    (Polynomial.X : Polynomial ℤ).eval (1 : ℤ) at hX
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (by simpa only [Polynomial.eval_X] using hX)

private theorem integerSpectrum_to_integerAffineLine_not_subsingleton :
    ¬ Subsingleton (integerSpectrum ⟶ integerAffineLine) := by
  intro h
  exact zeroSection_ne_oneSection (@Subsingleton.elim _ h zeroSection oneSection)

private theorem zeroSection_separates_points :
    ∃ x y : integerSpectrum, zeroSection x ≠ zeroSection y := by
  obtain ⟨x, y, hxy⟩ := integerSpectrum_identity_separates_points
  refine ⟨x, y, ?_⟩
  intro h
  have hprojection : (zeroSection ≫ affineLineProjection) x =
      (zeroSection ≫ affineLineProjection) y := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun z : integerAffineLine => affineLineProjection z) h
  have hsection : zeroSection ≫ affineLineProjection = 𝟙 integerSpectrum :=
    integerEvaluationSection_projection 0
  rw [hsection] at hprojection
  exact hxy hprojection

private noncomputable def awayTwoZeroSection :
    integerSpectrum.PartialMap integerAffineLine :=
  awayTwoIdentity.compHom zeroSection

private noncomputable def awayThreeZeroSection :
    integerSpectrum.PartialMap integerAffineLine :=
  awayThreeIdentity.compHom zeroSection

private theorem awayTwoZeroSection_awayThreeZeroSection_strict_cover :
    Dense (awayTwoZeroSection.domain : Set integerSpectrum) ∧
      Dense (awayThreeZeroSection.domain : Set integerSpectrum) ∧
      awayTwoZeroSection.domain < awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain ∧
      awayThreeZeroSection.domain < awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain ∧
      awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain = ⊤ := by
  exact awayTwoIdentity_awayThreeIdentity_strict_cover

private theorem awayTwoZeroSection_compatible_awayThreeZeroSection :
    integerSpectrum.homOfLE
        (inf_le_left : awayTwoZeroSection.domain ⊓ awayThreeZeroSection.domain ≤
          awayTwoZeroSection.domain) ≫ awayTwoZeroSection.hom =
      integerSpectrum.homOfLE
        (inf_le_right : awayTwoZeroSection.domain ⊓ awayThreeZeroSection.domain ≤
          awayThreeZeroSection.domain) ≫ awayThreeZeroSection.hom := by
  change integerSpectrum.homOfLE
      (inf_le_left : awayTwoIdentity.domain ⊓ awayThreeIdentity.domain ≤
        awayTwoIdentity.domain) ≫ (awayTwoIdentity.hom ≫ zeroSection) =
    integerSpectrum.homOfLE
      (inf_le_right : awayTwoIdentity.domain ⊓ awayThreeIdentity.domain ≤
        awayThreeIdentity.domain) ≫ (awayThreeIdentity.hom ≫ zeroSection)
  simpa only [Category.assoc] using congrArg
    (fun f : (awayTwoIdentity.domain ⊓ awayThreeIdentity.domain).toScheme ⟶
      integerSpectrum => f ≫ zeroSection)
    awayTwoIdentity_compatible_awayThreeIdentity

private theorem zeroSection_union_domain_and_hom_restrictions :
    zeroSection.toPartialMap.domain =
        awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain ∧
      integerSpectrum.homOfLE
          (le_top : awayTwoZeroSection.domain ≤ zeroSection.toPartialMap.domain) ≫
          zeroSection.toPartialMap.hom = awayTwoZeroSection.hom ∧
      integerSpectrum.homOfLE
          (le_top : awayThreeZeroSection.domain ≤ zeroSection.toPartialMap.domain) ≫
          zeroSection.toPartialMap.hom = awayThreeZeroSection.hom := by
  refine ⟨integerBasicOpen_two_sup_three.symm, ?_, ?_⟩
  · change integerSpectrum.homOfLE (le_top : integerBasicOpen 2 ≤ ⊤) ≫
      (integerSpectrum.topIso.hom ≫ zeroSection) = (integerBasicOpen 2).ι ≫ zeroSection
    rw [← Category.assoc, Scheme.topIso_hom, Scheme.homOfLE_ι]
  · change integerSpectrum.homOfLE (le_top : integerBasicOpen 3 ≤ ⊤) ≫
      (integerSpectrum.topIso.hom ≫ zeroSection) = (integerBasicOpen 3).ι ≫ zeroSection
    rw [← Category.assoc, Scheme.topIso_hom, Scheme.homOfLE_ι]

private theorem zeroSection_restricts_to_both_partial_sections :
    zeroSection.toPartialMap.restrict awayTwoZeroSection.domain
        awayTwoZeroSection.dense_domain le_top = awayTwoZeroSection ∧
      zeroSection.toPartialMap.restrict awayThreeZeroSection.domain
        awayThreeZeroSection.dense_domain le_top = awayThreeZeroSection := by
  constructor
  · refine Scheme.PartialMap.ext _ _ rfl ?_
    calc
      _ = integerSpectrum.homOfLE
          (le_top : awayTwoZeroSection.domain ≤ zeroSection.toPartialMap.domain) ≫
            zeroSection.toPartialMap.hom := rfl
      _ = awayTwoZeroSection.hom := zeroSection_union_domain_and_hom_restrictions.2.1
      _ = (integerSpectrum.isoOfEq
          (rfl : awayTwoZeroSection.domain = awayTwoZeroSection.domain)).hom ≫
            awayTwoZeroSection.hom := by
        rw [Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  · refine Scheme.PartialMap.ext _ _ rfl ?_
    calc
      _ = integerSpectrum.homOfLE
          (le_top : awayThreeZeroSection.domain ≤ zeroSection.toPartialMap.domain) ≫
            zeroSection.toPartialMap.hom := rfl
      _ = awayThreeZeroSection.hom := zeroSection_union_domain_and_hom_restrictions.2.2
      _ = (integerSpectrum.isoOfEq
          (rfl : awayThreeZeroSection.domain = awayThreeZeroSection.domain)).hom ≫
            awayThreeZeroSection.hom := by
        rw [Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp]

private theorem partial_sections_over_integerSpectrum :
    awayTwoZeroSection.hom ≫ affineLineProjection = (integerBasicOpen 2).ι ∧
      awayThreeZeroSection.hom ≫ affineLineProjection = (integerBasicOpen 3).ι := by
  constructor
  · change ((integerBasicOpen 2).ι ≫ integerEvaluationSection 0) ≫ affineLineProjection = _
    rw [Category.assoc, integerEvaluationSection_projection, Category.comp_id]
  · change ((integerBasicOpen 3).ι ≫ integerEvaluationSection 0) ≫ affineLineProjection = _
    rw [Category.assoc, integerEvaluationSection_projection, Category.comp_id]

private noncomputable def gluedZeroSection : integerSpectrum.PartialMap integerAffineLine :=
  awayTwoZeroSection.glueHom awayThreeZeroSection.domain awayThreeZeroSection.hom
    awayTwoZeroSection_compatible_awayThreeZeroSection

private theorem gluedZeroSection_strict_cover :
    awayTwoZeroSection.domain < gluedZeroSection.domain ∧
      awayThreeZeroSection.domain < gluedZeroSection.domain ∧
      gluedZeroSection.domain = ⊤ := by
  exact awayTwoZeroSection_awayThreeZeroSection_strict_cover.2.2

/-- The zero section restricted to the empty open of the integer spectrum. -/
private noncomputable def emptyZeroSection :
    (⊥ : integerSpectrum.Opens).toScheme ⟶ integerAffineLine :=
  (⊥ : integerSpectrum.Opens).ι ≫ zeroSection

/-- The zero sections on `D(2)` and the empty open agree on their intersection. -/
private theorem awayTwoZeroSection_compatible_emptyZeroSection :
    integerSpectrum.homOfLE
        (inf_le_left : awayTwoZeroSection.domain ⊓ ⊥ ≤ awayTwoZeroSection.domain) ≫
        awayTwoZeroSection.hom =
      integerSpectrum.homOfLE
        (inf_le_right : awayTwoZeroSection.domain ⊓ ⊥ ≤ ⊥) ≫ emptyZeroSection := by
  change integerSpectrum.homOfLE
      (inf_le_left : integerBasicOpen 2 ⊓ ⊥ ≤ integerBasicOpen 2) ≫
        ((integerBasicOpen 2).ι ≫ zeroSection) =
    integerSpectrum.homOfLE
      (inf_le_right : integerBasicOpen 2 ⊓ ⊥ ≤ ⊥) ≫
        ((⊥ : integerSpectrum.Opens).ι ≫ zeroSection)
  rw [← Category.assoc, ← Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι]

/-- Adjoin the empty zero-section patch to the zero section on `D(2)`. -/
private noncomputable def awayTwoZeroSectionWithEmptyPatch :
    integerSpectrum.PartialMap integerAffineLine :=
  awayTwoZeroSection.glueHom ⊥ emptyZeroSection
    awayTwoZeroSection_compatible_emptyZeroSection

/-- Adjoining the empty patch leaves the domain `D(2)` unchanged. -/
private theorem awayTwoZeroSectionWithEmptyPatch_domain :
    awayTwoZeroSectionWithEmptyPatch.domain = awayTwoZeroSection.domain := by
  change awayTwoZeroSection.domain ⊔ (⊥ : integerSpectrum.Opens) = awayTwoZeroSection.domain
  exact sup_bot_eq awayTwoZeroSection.domain

/-- The empty open is not dense in the integer spectrum, which contains the prime `(0)`. -/
private theorem integerSpectrum_empty_not_dense :
    ¬ Dense ((⊥ : integerSpectrum.Opens) : Set integerSpectrum) := by
  intro h
  have hx := h (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℤ)
  rw [TopologicalSpace.Opens.coe_bot, closure_empty] at hx
  exact (Set.mem_empty_iff_false (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℤ)).mp hx

/-- The anchored gluing has the two prescribed full scheme-morphism restrictions. -/
private theorem gluedZeroSection_hom_restrictions :
    integerSpectrum.homOfLE
        (le_sup_left : awayTwoZeroSection.domain ≤
          awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain) ≫ gluedZeroSection.hom =
        awayTwoZeroSection.hom ∧
      integerSpectrum.homOfLE
        (le_sup_right : awayThreeZeroSection.domain ≤
          awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain) ≫ gluedZeroSection.hom =
        awayThreeZeroSection.hom := by
  exact ⟨Scheme.PartialMap.homOfLE_glueHom_left awayTwoZeroSection
      awayThreeZeroSection.domain awayThreeZeroSection.hom
      awayTwoZeroSection_compatible_awayThreeZeroSection,
    Scheme.PartialMap.homOfLE_glueHom_right awayTwoZeroSection
      awayThreeZeroSection.domain awayThreeZeroSection.hom
      awayTwoZeroSection_compatible_awayThreeZeroSection⟩

/-- The anchored gluing and the total zero section recover the same partial section on `D(2)`. -/
private theorem gluedZeroSection_restrict_awayTwoZeroSection :
    gluedZeroSection.restrict awayTwoZeroSection.domain awayTwoZeroSection.dense_domain
        (le_sup_left : awayTwoZeroSection.domain ≤
          awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain) =
      zeroSection.toPartialMap.restrict awayTwoZeroSection.domain
        awayTwoZeroSection.dense_domain le_top := by
  exact (Scheme.PartialMap.glueHom_restrict_left awayTwoZeroSection
    awayThreeZeroSection.domain awayThreeZeroSection.hom
    awayTwoZeroSection_compatible_awayThreeZeroSection).trans
      zeroSection_restricts_to_both_partial_sections.1.symm

/-- The independent total zero section, restricted to the union, is the anchored gluing. -/
private theorem gluedZeroSection_hom_eq :
    gluedZeroSection.hom =
      integerSpectrum.homOfLE
          (le_top : awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain ≤
            zeroSection.toPartialMap.domain) ≫ zeroSection.toPartialMap.hom := by
  refine (Scheme.PartialMap.glueHom_hom_eq_iff awayTwoZeroSection
    awayThreeZeroSection.domain awayThreeZeroSection.hom
    awayTwoZeroSection_compatible_awayThreeZeroSection _).mpr ?_
  constructor
  · exact (Category.assoc
      (integerSpectrum.homOfLE
        (U := awayTwoZeroSection.domain)
        (V := awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain) le_sup_left)
      (integerSpectrum.homOfLE
        (U := awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain)
        (V := zeroSection.toPartialMap.domain) le_top)
      zeroSection.toPartialMap.hom).symm.trans
        ((integerSpectrum.homOfLE_homOfLE_assoc
          (U := awayTwoZeroSection.domain)
          (V := awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain)
          (W := zeroSection.toPartialMap.domain)
          le_sup_left le_top zeroSection.toPartialMap.hom).trans
            zeroSection_union_domain_and_hom_restrictions.2.1)
  · exact (Category.assoc
      (integerSpectrum.homOfLE
        (U := awayThreeZeroSection.domain)
        (V := awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain) le_sup_right)
      (integerSpectrum.homOfLE
        (U := awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain)
        (V := zeroSection.toPartialMap.domain) le_top)
      zeroSection.toPartialMap.hom).symm.trans
        ((integerSpectrum.homOfLE_homOfLE_assoc
          (U := awayThreeZeroSection.domain)
          (V := awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain)
          (W := zeroSection.toPartialMap.domain)
          le_sup_right le_top zeroSection.toPartialMap.hom).trans
            zeroSection_union_domain_and_hom_restrictions.2.2)

/-- The anchored gluing represents the rational map of the total zero section. -/
private theorem gluedZeroSection_toRationalMap :
    gluedZeroSection.toRationalMap = zeroSection.toRationalMap := by
  calc
    _ = awayTwoZeroSection.toRationalMap :=
      Scheme.PartialMap.glueHom_toRationalMap awayTwoZeroSection
        awayThreeZeroSection.domain awayThreeZeroSection.hom
        awayTwoZeroSection_compatible_awayThreeZeroSection
    _ = (zeroSection.toPartialMap.restrict awayTwoZeroSection.domain
        awayTwoZeroSection.dense_domain le_top).toRationalMap :=
      congrArg (fun p : integerSpectrum.PartialMap integerAffineLine => p.toRationalMap)
        zeroSection_restricts_to_both_partial_sections.1.symm
    _ = zeroSection.toRationalMap :=
      Scheme.PartialMap.restrict_toRationalMap zeroSection.toPartialMap
        awayTwoZeroSection.domain awayTwoZeroSection.dense_domain le_top

/-- The anchored gluing is a section of the affine-line projection on its whole domain. -/
private theorem gluedZeroSection_projection :
    gluedZeroSection.hom ≫ affineLineProjection = gluedZeroSection.domain.ι := by
  let : integerSpectrum.Over integerSpectrum := ⟨𝟙 integerSpectrum⟩
  let : integerAffineLine.Over integerSpectrum := ⟨affineLineProjection⟩
  let : awayTwoZeroSection.IsOver integerSpectrum :=
    (Scheme.PartialMap.isOver_iff (S := integerSpectrum)
      (f := awayTwoZeroSection)).mpr (by
        change awayTwoZeroSection.hom ≫ affineLineProjection =
          (integerBasicOpen 2).ι ≫ 𝟙 integerSpectrum
        simpa only [Category.comp_id] using partial_sections_over_integerSpectrum.1)
  let : awayThreeZeroSection.hom.IsOver integerSpectrum :=
    (Scheme.PartialMap.isOver_iff (S := integerSpectrum)
      (f := awayThreeZeroSection)).mpr (by
        change awayThreeZeroSection.hom ≫ affineLineProjection =
          (integerBasicOpen 3).ι ≫ 𝟙 integerSpectrum
        simpa only [Category.comp_id] using partial_sections_over_integerSpectrum.2)
  have hOver : gluedZeroSection.IsOver integerSpectrum :=
    Scheme.PartialMap.isOver_glueHom awayTwoZeroSection
      awayThreeZeroSection.domain awayThreeZeroSection.hom
      awayTwoZeroSection_compatible_awayThreeZeroSection
  have h := (Scheme.PartialMap.isOver_iff (S := integerSpectrum)
    (f := gluedZeroSection)).mp hOver
  change gluedZeroSection.hom ≫ affineLineProjection =
    gluedZeroSection.domain.ι ≫ 𝟙 integerSpectrum at h
  simpa only [Category.comp_id] using h

/-- Binary gluing has the two prescribed full scheme-morphism restrictions. -/
private theorem zeroSection_glue_hom_restrictions :
    integerSpectrum.homOfLE
        (le_sup_left : awayTwoZeroSection.domain ≤
          awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain) ≫
        (awayTwoZeroSection.glue awayThreeZeroSection
          awayTwoZeroSection_compatible_awayThreeZeroSection).hom = awayTwoZeroSection.hom ∧
      integerSpectrum.homOfLE
        (le_sup_right : awayThreeZeroSection.domain ≤
          awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain) ≫
        (awayTwoZeroSection.glue awayThreeZeroSection
          awayTwoZeroSection_compatible_awayThreeZeroSection).hom = awayThreeZeroSection.hom := by
  exact ⟨Scheme.PartialMap.homOfLE_glue_left awayTwoZeroSection awayThreeZeroSection
      awayTwoZeroSection_compatible_awayThreeZeroSection,
    Scheme.PartialMap.homOfLE_glue_right awayTwoZeroSection awayThreeZeroSection
      awayTwoZeroSection_compatible_awayThreeZeroSection⟩

/-- Binary gluing and the total zero section have the same restrictions on both dense opens. -/
private theorem zeroSection_glue_restrictions :
    (awayTwoZeroSection.glue awayThreeZeroSection
        awayTwoZeroSection_compatible_awayThreeZeroSection).restrict
        awayTwoZeroSection.domain awayTwoZeroSection.dense_domain le_sup_left =
      zeroSection.toPartialMap.restrict awayTwoZeroSection.domain
        awayTwoZeroSection.dense_domain le_top ∧
    (awayTwoZeroSection.glue awayThreeZeroSection
        awayTwoZeroSection_compatible_awayThreeZeroSection).restrict
        awayThreeZeroSection.domain awayThreeZeroSection.dense_domain le_sup_right =
      zeroSection.toPartialMap.restrict awayThreeZeroSection.domain
        awayThreeZeroSection.dense_domain le_top := by
  exact ⟨(Scheme.PartialMap.glue_restrict_left awayTwoZeroSection awayThreeZeroSection
      awayTwoZeroSection_compatible_awayThreeZeroSection).trans
        zeroSection_restricts_to_both_partial_sections.1.symm,
    (Scheme.PartialMap.glue_restrict_right awayTwoZeroSection awayThreeZeroSection
      awayTwoZeroSection_compatible_awayThreeZeroSection).trans
        zeroSection_restricts_to_both_partial_sections.2.symm⟩

/-- The independent total zero section, restricted to the union, is the binary gluing. -/
private theorem zeroSection_glue_hom_eq :
    (awayTwoZeroSection.glue awayThreeZeroSection
        awayTwoZeroSection_compatible_awayThreeZeroSection).hom =
      integerSpectrum.homOfLE
          (le_top : awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain ≤
            zeroSection.toPartialMap.domain) ≫ zeroSection.toPartialMap.hom := by
  refine (Scheme.PartialMap.glue_hom_eq_iff awayTwoZeroSection awayThreeZeroSection
    awayTwoZeroSection_compatible_awayThreeZeroSection _).mpr ?_
  constructor
  · exact (Category.assoc
      (integerSpectrum.homOfLE
        (U := awayTwoZeroSection.domain)
        (V := awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain) le_sup_left)
      (integerSpectrum.homOfLE
        (U := awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain)
        (V := zeroSection.toPartialMap.domain) le_top)
      zeroSection.toPartialMap.hom).symm.trans
        ((integerSpectrum.homOfLE_homOfLE_assoc
          (U := awayTwoZeroSection.domain)
          (V := awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain)
          (W := zeroSection.toPartialMap.domain)
          le_sup_left le_top zeroSection.toPartialMap.hom).trans
            zeroSection_union_domain_and_hom_restrictions.2.1)
  · exact (Category.assoc
      (integerSpectrum.homOfLE
        (U := awayThreeZeroSection.domain)
        (V := awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain) le_sup_right)
      (integerSpectrum.homOfLE
        (U := awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain)
        (V := zeroSection.toPartialMap.domain) le_top)
      zeroSection.toPartialMap.hom).symm.trans
        ((integerSpectrum.homOfLE_homOfLE_assoc
          (U := awayThreeZeroSection.domain)
          (V := awayTwoZeroSection.domain ⊔ awayThreeZeroSection.domain)
          (W := zeroSection.toPartialMap.domain)
          le_sup_right le_top zeroSection.toPartialMap.hom).trans
            zeroSection_union_domain_and_hom_restrictions.2.2)

/-- Binary gluing reads back the rational maps of both partial sections. -/
private theorem zeroSection_glue_toRationalMap :
    (awayTwoZeroSection.glue awayThreeZeroSection
        awayTwoZeroSection_compatible_awayThreeZeroSection).toRationalMap =
      awayTwoZeroSection.toRationalMap ∧
    (awayTwoZeroSection.glue awayThreeZeroSection
        awayTwoZeroSection_compatible_awayThreeZeroSection).toRationalMap =
      awayThreeZeroSection.toRationalMap := by
  exact ⟨Scheme.PartialMap.glue_toRationalMap awayTwoZeroSection awayThreeZeroSection
      awayTwoZeroSection_compatible_awayThreeZeroSection,
    Scheme.PartialMap.glue_toRationalMap_right awayTwoZeroSection awayThreeZeroSection
      awayTwoZeroSection_compatible_awayThreeZeroSection⟩

/-- Binary gluing is a section of the affine-line projection on its whole domain. -/
private theorem zeroSection_glue_projection :
    (awayTwoZeroSection.glue awayThreeZeroSection
        awayTwoZeroSection_compatible_awayThreeZeroSection).hom ≫ affineLineProjection =
      (awayTwoZeroSection.glue awayThreeZeroSection
        awayTwoZeroSection_compatible_awayThreeZeroSection).domain.ι := by
  let : integerSpectrum.Over integerSpectrum := ⟨𝟙 integerSpectrum⟩
  let : integerAffineLine.Over integerSpectrum := ⟨affineLineProjection⟩
  let : awayTwoZeroSection.IsOver integerSpectrum :=
    (Scheme.PartialMap.isOver_iff (S := integerSpectrum)
      (f := awayTwoZeroSection)).mpr (by
        change awayTwoZeroSection.hom ≫ affineLineProjection =
          (integerBasicOpen 2).ι ≫ 𝟙 integerSpectrum
        simpa only [Category.comp_id] using partial_sections_over_integerSpectrum.1)
  let : awayThreeZeroSection.IsOver integerSpectrum :=
    (Scheme.PartialMap.isOver_iff (S := integerSpectrum)
      (f := awayThreeZeroSection)).mpr (by
        change awayThreeZeroSection.hom ≫ affineLineProjection =
          (integerBasicOpen 3).ι ≫ 𝟙 integerSpectrum
        simpa only [Category.comp_id] using partial_sections_over_integerSpectrum.2)
  have hOver : (awayTwoZeroSection.glue awayThreeZeroSection
      awayTwoZeroSection_compatible_awayThreeZeroSection).IsOver integerSpectrum :=
    Scheme.PartialMap.isOver_glue awayTwoZeroSection awayThreeZeroSection
      awayTwoZeroSection_compatible_awayThreeZeroSection
  have h := (Scheme.PartialMap.isOver_iff (S := integerSpectrum)
    (f := awayTwoZeroSection.glue awayThreeZeroSection
      awayTwoZeroSection_compatible_awayThreeZeroSection)).mp hOver
  change (awayTwoZeroSection.glue awayThreeZeroSection
      awayTwoZeroSection_compatible_awayThreeZeroSection).hom ≫ affineLineProjection =
    (awayTwoZeroSection.glue awayThreeZeroSection
      awayTwoZeroSection_compatible_awayThreeZeroSection).domain.ι ≫ 𝟙 integerSpectrum at h
  simpa only [Category.comp_id] using h

end SchemePropertiesTest.PartialMapGluing
