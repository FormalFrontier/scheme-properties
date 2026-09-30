# Dense-open rational maps over a base

Import `SchemeProperties.DenseOpenRationalCategoryOver`. For an
arbitrary scheme `S : AlgebraicGeometry.Scheme.{u}`,
`AlgebraicGeometry.DenseOpenRationalSchemeOver S` has fields
`toScheme : Scheme.{u}` and `toBase : toScheme ⟶ S`. The constructor
`DenseOpenRationalSchemeOver.of p` takes *any* total scheme morphism
`p : X ⟶ S`; no geometric assumption on the base or objects is needed.

The hom type `DenseOpenRationalSchemeOver.Hom X Y` contains
`toRationalMap : X.toScheme ⤏ Y.toScheme`, its native
`Scheme.RationalMap.PullsDenseOpens` proof, and its native
`Scheme.RationalMap.IsOver S` proof. The latter is an **existential over-base
partial-map representative**, not an assertion that every representative is
pointwise over `S`. The `Over` instances in that predicate are constructed
explicitly from `X.toBase` and `Y.toBase`; they remain distinct even when
`X.toScheme` and `Y.toScheme` happen to be the same scheme. The hom constructor
`hom r hr hS` accepts these exact three fields. The projections `toRationalMap`,
`pullsDenseOpens`, `isOver`, the constructor projection `toRationalMap_hom`, and
the quotient extensionality lemma `hom_ext` make the bundled arrows usable
without selecting a representative. For an arbitrary `r`,
`isOver_iff_compHom` reuses the native characterization
`r.IsOver S ↔ r.compHom Y.toBase = X.toBase.toRationalMap`, with explicit
object-specific `Over` instances.

The `Category (DenseOpenRationalSchemeOver S)` instance uses
`Scheme.RationalMap.id` and `compOfPullsDenseOpens`. The composition operation
uses the **first** arrow's pullback condition; proving its closure uses **both**
arrows' conditions. The required over-base preservation is the existing native
`Scheme.RationalMap.isOver_compOfPullsDenseOpens`, specialized with the three
**explicit** chosen structure maps so identical underlying schemes with
different maps do not pick an ambiguous inferred `Over` instance. Units and associativity reuse
the controlled-composition laws imported from the published
`SchemeProperties.DenseOpenRationalCategory` and
`SchemeProperties.DenseOpenCompositionOver` modules. The `@[simp]` projections
`toRationalMap_id` and `toRationalMap_comp` expose the quotient operations;
ordinary `Category.id_comp`, `Category.comp_id` and `Category.assoc` apply.

`DenseOpenRationalSchemeOver.forget S` is a functor to the **absolute**
`AlgebraicGeometry.DenseOpenRationalScheme` category. Its object and map
projections are `forget_obj_toScheme` and `forget_map_toRationalMap`, and its
`map_id`/`map_comp` laws are definitional after quotient-arrow extensionality.
The instance `(forget S).Faithful` is obtained from `hom_ext`; no fullness or
functor to the category of total scheme morphisms is asserted.

```lean
import SchemeProperties.DenseOpenRationalCategoryOver

open AlgebraicGeometry AlgebraicGeometry.DenseOpenRationalSchemeOver CategoryTheory

example {S : Scheme} {X Y Z : DenseOpenRationalSchemeOver S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRationalMap =
      f.toRationalMap.compOfPullsDenseOpens f.pullsDenseOpens g.toRationalMap :=
  toRationalMap_comp f g
```

The independent direct-import private client
`Test/DenseOpenRationalCategoryOverClient.lean` exercises arbitrary
bases and objects, both constructors, native over-base witnesses and composition,
quotient extensionality, all category laws, projections, the functor laws,
faithfulness and two potentially different maps on one underlying scheme. Its
parameterized tests are not claimed as concrete counterexamples. This module
does not implement integral restrictions/equivalences, base change, function
fields, all-reduced-source composition or source correspondence. In particular,
categorical `Over S` **in the rational-arrow category** would impose an
unwanted dense-open pullback condition on total structure maps and is not used.

The category uses original Formal Frontier rational-map interfaces and
imports mathlib native quotient/over-base APIs. See [Credits](CREDITS.md);
[README](../README.md#build) gives the pinned build instructions.
