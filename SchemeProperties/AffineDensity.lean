/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.FiniteTypePoints

/-!
# Affine density among schemes

The spectrum functor `Scheme.Spec : CommRingCat.{u}ᵒᵖ ⥤ Scheme.{u}` is cover-dense
for the big Zariski topology and dense in the category of schemes. The tests are spectra
of all commutative rings in the same universe, including the zero ring. There are no
finite-type, field, reducedness, separatedness or nonemptiness assumptions.

## Reused API

The generic bridge `CategoryTheory.Functor.isDense_of_isCoverDense_of_subcanonical` is
already provided by `SchemeProperties.FiniteTypePoints`; it is not redefined here.
Mathlib supplies `Scheme.affineCover`, the covering-sieve API, `Spec.full`, the implication
from full to locally full, and subcanonicality of `Scheme.zariskiTopology`.

The density instance gives Mathlib's full and faithful instances for
`Presheaf.restrictedULiftYoneda.{0} Scheme.Spec` without a new points functor. Its value
at a scheme `X` and `op (op R)` is `ULift.{0} (Spec R ⟶ X) : Type u`; natural-transformation
Hom types lie in `Type (u + 1)`. The stock `Functor.FullyFaithful.ofFullyFaithful` constructs
reconstruction data, with `preimage`, `homEquiv` and both inverse equations. These are
existing constructions, not additional results of this module.

## References

- Mathlib's affine covers and scheme limits (Andrew Yang), big Zariski subcanonicality
  (Joël Riou and Adam Topaz), dense-subsite methods (Andrew Yang and Joël Riou), and
  functor density (Joël Riou).
- The existing generic cover-dense/subcanonical density bridge in
  `SchemeProperties.FiniteTypePoints`, adapted from Lattice's scheme-level formalization.
- Mathlib's restricted Yoneda API (Bhavik Mehta and Joël Riou), fully faithful
  reconstruction API (Kim Morrison), and Γ–Spec full faithfulness (Junyan Xu).
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- Spectra of all same-universe commutative rings are cover-dense for the big Zariski
topology on schemes. -/
instance Spec.isCoverDense :
    (Scheme.Spec : CommRingCat.{u}ᵒᵖ ⥤ Scheme.{u}).IsCoverDense Scheme.zariskiTopology := by
  refine ⟨fun X ↦ ?_⟩
  refine Scheme.mem_grothendieckTopology_iff.mpr ⟨X.affineOpenCover.openCover, ?_⟩
  rintro _ _ ⟨i⟩
  exact Presieve.in_coverByImage Scheme.Spec
    (Y := op (X.affineOpenCover.X i)) (X.affineOpenCover.f i)

/-- Spectra of all same-universe commutative rings form a dense family in the category
of schemes. -/
instance Spec.isDense : (Scheme.Spec : CommRingCat.{u}ᵒᵖ ⥤ Scheme.{u}).IsDense := by
  exact Functor.isDense_of_isCoverDense_of_subcanonical Scheme.Spec Scheme.zariskiTopology

end AlgebraicGeometry
