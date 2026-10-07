/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Algebra.Shrink

/-!
# Universe lift of finitely generated algebras

The existing `FGAlgCat.uliftFunctor` is fully faithful. When the base ring is small in the
source universe, finite generation makes every algebra in the target universe small in the
source universe as well. This gives essential surjectivity and hence an equivalence, without
assuming that the target universe embeds into the source universe.

The carrier of a finitely generated algebra is small by `Algebra.FiniteType.small`, and
`Shrink.algEquiv` transports its algebra structure to the source universe. The smallness
assumption is on the base, not on all types in the target universe. No assertion of essential
surjectivity is made here for a base with no such size bound.

## References

- Mathlib, `Mathlib.Algebra.Category.CommAlgCat.FiniteType` for `FGAlgCat.uliftFunctor` and
  its full and faithful instances, and `Mathlib.RingTheory.Finiteness.Small` for
  `Algebra.FiniteType.small`; `Mathlib.Algebra.Algebra.Shrink` provides `Shrink.algEquiv`.
- J. S. Milne, *Algebraic Groups* (2017), Appendix A.33, motivates comparison of
  finitely generated algebra presentations; the universe-lift statement concerns Mathlib's
  category itself rather than a particular presentation category.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace FGAlgCat

variable (R : Type u) [CommRing R]

/-- The underlying algebra and its morphisms in Mathlib's universe-lift functor. -/
@[simp] theorem uliftFunctor_obj_obj (A : FGAlgCat.{v} R) :
    ((uliftFunctor R : FGAlgCat.{v} R ⥤ FGAlgCat.{max v w} R).obj A).obj =
      ULift.{w} A.obj := rfl

/-- The universe-lift functor sends an algebra homomorphism to its lifted function. -/
@[simp] theorem uliftFunctor_map_apply {A B : FGAlgCat.{v} R} (f : A ⟶ B) (x : A.obj) :
    ((uliftFunctor R : FGAlgCat.{v} R ⥤ FGAlgCat.{max v w} R).map f).hom
      (ULift.up x) = ULift.up (f.hom x) := rfl

/-- Every finitely generated algebra in the larger universe is isomorphic to a lift of one
in the smaller universe when the base ring is small in the smaller universe. -/
instance essSurjUliftFunctor [Small.{v} R] :
    (uliftFunctor R : FGAlgCat.{v} R ⥤ FGAlgCat.{max v w} R).EssSurj := by
  classical
  exact ⟨fun B =>
    letI : Small.{v} B.obj := Algebra.FiniteType.small (R := R) (S := B.obj)
    letI : Algebra.FiniteType R (Shrink.{v} B.obj) :=
      Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType R B.obj)
        (Shrink.algEquiv R B.obj).symm
    ⟨⟨CommAlgCat.of R (Shrink.{v} B.obj), inferInstance⟩,
      ⟨ObjectProperty.isoMk _ (CommAlgCat.isoMk
        ((ULift.algEquiv (R := R)).trans (Shrink.algEquiv R B.obj)))⟩⟩⟩

/-- Universe lift is an equivalence on finitely generated algebras over a base ring
small in the source universe. -/
instance isEquivalenceUliftFunctor [Small.{v} R] :
    (uliftFunctor R : FGAlgCat.{v} R ⥤ FGAlgCat.{max v w} R).IsEquivalence := by
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

end FGAlgCat
