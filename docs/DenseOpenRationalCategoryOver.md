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

## Provenance, reproduction and status

The isolated implementation and client at incubator commit
`dd5a565615cebfedda5782f81b031fa6f86426f6` were contributed by Formal
Frontier worker-b Hive Task `hive-request-6d6b2ce9689faeb78ffe46a43d9ee825f518a883`
(UID `f5a73c6c-7142-4861-9425-4f029a6c2531`) and independently reviewed
by worker-a Hive Task `hive-request-502dd6aec7bbea7778dfaccd1af6bab82ee21e81`
(UID `d96178c1-f41e-464d-8e83-eac2fb730a60`). The unchanged mathematical
implementation and adapted private client were transferred here by worker-b
Hive Task `hive-request-19a08a0a2be9ed8de115c36f507f890f64e5b1d2`
(UID `b91d3b22-1c39-4ca2-9613-cf1b2c871f09`). Native partial/rational-map
and relative semantics come from mathlib and existing Scheme Properties modules,
including work by Andrew Yang and Justus Springer. The category and client do
not encode an attribution or coverage claim for a particular source; see
[contributor and expression credits](CREDITS.md).

The destination pins `leanprover/lean4:v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. Its three direct
requirements are mathlib and the official private-GitHub releases of
`coherent-modules` (`fc30df937c7476f1c01f7cb39005f8cae37f8f34`) and
`finite-etale-algebras` (`79575f65c9edec560f27756917761eed78331a2a`),
resolved into 11 packages. Consult `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`; authorized private dependency access is required. Install
the pinned Lean toolchain and successfully fetch the matching mathlib cache
**before** any authorized build from the repository root:

```sh
lake exe cache get
LAKE_JOBS=2 lake --wfail build SchemeProperties.DenseOpenRationalCategoryOver Test.DenseOpenRationalCategoryOverClient
```

**Transfer-time history, before destination acceptance:**

**Status, September 30, 2026:** The isolated donor code has its own focused
build, complete private/generated-inclusive standard-axiom evidence, fresh
independent review and Atlas's code acceptance in the donor's owning
contribution record (incubator issue #273).
This destination transfer is a separate proposal; donor acceptance is not a
destination build or audit, destination review/acceptance, integration, official
release or source-coverage decision. Atlas owns those subsequent gates.

**Dated destination update, September 30, 2026, 02:25:15 UTC:** corrected
destination code `855d795b76b6a63b828c54253e69a75ffb60bda8` passed its
configured destination build and complete transitive standard-axiom audit,
including private and generated declarations. It received independent review
and maintainer acceptance and was integrated into development main. Those
destination gates are complete for that exact revision; the preceding proposal
status is retained as transfer-time history. Its separate official release and
verified publication were still pending at this update. Neither this status
record nor the main integration asserts official publication or source coverage.
