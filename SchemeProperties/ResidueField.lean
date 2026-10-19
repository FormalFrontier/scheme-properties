/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Category.Ring.EqualizerPushout
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Residue-field maps of monomorphisms

A monomorphism of arbitrary schemes induces an isomorphism on the canonical
residue-field map at every point. No finiteness, reducedness, separation or
splitting hypothesis is needed. The schemes lie in the same arbitrary universe,
as in Mathlib's residue-field API.

Naturality of the canonical map `Spec κ(x) ⟶ X` makes the spectrum of the
residue-field map monic. Faithfulness of `Spec` then makes the residue-field map
epic in `CommRingCat`, with all commutative rings as test objects. The field
extension is faithfully flat, hence a regular monomorphism and therefore an
isomorphism. This uses the faithfully-flat equalizer construction rather than
an additional field-epimorphism theorem.

The existing residue-field identity, composition, congruence and naturality API
is unchanged. The theorem supplies `IsIso` explicitly; `CategoryTheory.inv` and
`CategoryTheory.asIso` give the usual inverse and isomorphism. Under an
open-immersion hypothesis it concerns exactly the map of Mathlib's existing
instance, and the two proofs agree by proof irrelevance.

## References

* Mathlib's canonical residue-field, stalk and `Spec` APIs, by Andrew Yang,
  Fangming Li, Junyan Xu and their respective contributors.
* Mathlib's vector-space basis construction, by Johannes Hölzl, Mario Carneiro
  and Alexander Bentkamp; its free-module faithfully-flat instance, by Judith
  Ludwig, Florent Schaffhauser, Yunzhou Xie and Jujian Zhang; and its ring-map
  faithful-flatness API, by Christian Merten and Joël Riou.
* Mathlib's faithfully-flat equalizer in `CommRingCat`, by Yong-Gyu Choi.
* Mathlib's faithful-functor reflection API, by Markus Himmel; its opposite
  epi/mono API, by Reid Barton and Kim Morrison; and its regular-monomorphism
  API, by Kim Morrison and Bhavik Mehta.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical residue-field map of a monomorphism of schemes is an
isomorphism. The monomorphism is categorical, not merely universally injective. -/
theorem isIso_residueFieldMap_of_mono {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Mono f] (x : X) : IsIso (f.residueFieldMap x) := by
  have : Mono (Spec.map (f.residueFieldMap x) ≫
      Y.fromSpecResidueField (f x)) := by
    rw [f.SpecMap_residueFieldMap_fromSpecResidueField x]
    infer_instance
  have : Mono (Spec.map (f.residueFieldMap x)) :=
    mono_of_mono _ (Y.fromSpecResidueField (f x))
  have : Mono (f.residueFieldMap x).op :=
    Scheme.Spec.mono_of_mono_map (by
      change Mono (Spec.map (f.residueFieldMap x))
      infer_instance)
  have : Epi (f.residueFieldMap x) :=
    unop_epi_of_mono (f.residueFieldMap x).op
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have hff : (f.residueFieldMap x).hom.FaithfullyFlat := by
    change Module.FaithfullyFlat (Y.residueField (f x)) (X.residueField x)
    infer_instance
  exact isIso_of_regularMono_of_epi _
    (CommRingCat.regularMonoOfFaithfullyFlat _ hff)

/-- Specialization to an open immersion agrees with Mathlib's instance on the
same canonical residue-field map. -/
private theorem isIso_residueFieldMap_of_mono_eq_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    isIso_residueFieldMap_of_mono f x =
      (inferInstance : IsIso (f.residueFieldMap x)) :=
  Subsingleton.elim _ _

end AlgebraicGeometry.Scheme.Hom
