# Single-cover density and descent

See the [overview](../README.md), [reader guide](Guide.md) and
[documentation index](README.md) for navigation and imports. Mathematical
[references](../README.md#references) and [credits](CREDITS.md) apply throughout.

## Single-cover subfunctors

- [Single-cover extension](../SchemeProperties/SingleCoverExtension.lean): in an
  arbitrary category, let `W` admit pullbacks along its morphisms and be stable
  under base change. If a subfunctor `D` of `F` is one-cover dense and `Y`
  satisfies descent for each singleton `W`-cover, restriction is an equivalence
  between natural transformations `F ⟶ Y` and `D ⟶ Y`. Neither identities nor
  composition stability in `W` nor a sheaf condition on `F` or `D` is required.
  If both ambient presheaves satisfy singleton descent, an isomorphism of two
  one-cover dense subfunctors extends uniquely to an ambient isomorphism;
  extension preserves the prescribed restrictions, identity, inverses and
  composition. Neither subfunctor needs descent.
  Direct import: `SchemeProperties.SingleCoverExtension`.
- [Change of test category](../SchemeProperties/SingleCoverTransport.lean): for a
  full, essentially surjective functor `J` and a morphism class `W` respecting
  isomorphisms, a subfunctor is one-cover dense exactly when its precomposition
  is dense for `W.inverseImage J`. Reflection needs only essential surjectivity,
  not fullness; in particular density is invariant under equivalences of test
  categories. No faithfulness, sheaf condition, pullbacks, identity covers or
  composition stability is required. The witnesses use a single covering
  arrow, not a covering family. Direct import:
  `SchemeProperties.SingleCoverTransport`.
- [Group objects from one-cover-dense subfunctors](../SchemeProperties/SingleCoverGroup.lean):
  if a group-valued subfunctor `D ⊆ F` is one-cover dense for a morphism class
  with relative pullbacks and stability under base change and composition, and
  the target presheaf `F` satisfies singleton-cover descent, its multiplication,
  unit and inversion extend to a group-object law on the **exact given** `F`.
  This is the unique such law making inclusion a monoid homomorphism. No ambient
  group law, descent for `D`, topology, or arbitrary finite limits on test
  objects are assumed. A proper dense `Bool` example recovers an independently
  specified group law and computes nonunit operations. This does not establish
  the corresponding represented finite-type group-scheme claim. Direct import:
  `SchemeProperties.SingleCoverGroup`.
- [Finite-type represented targets](../SchemeProperties/FiniteTypeSingleCover.lean):
  over a field `K`, for finite-type `K`-schemes `X` and `Y`, maps from a one-cover
  dense subfunctor of the restricted points of `X` into those of `Y` correspond
  to `K`-morphisms `X ⟶ Y`. Tests are finitely generated `K`-algebras and
  density is witnessed by one faithfully flat algebra map. Target descent uses
  Mathlib fpqc descent and pullback comparison, not a full induced-site
  equivalence or a translation of Milne's ring-level proof. Direct import:
  `SchemeProperties.FiniteTypeSingleCover`.
- [Finite-type isomorphism extension](../SchemeProperties/FiniteTypeSingleCover.lean):
  over any field, an isomorphism of two one-cover dense subfunctors of restricted
  points of finite-type schemes extends uniquely to a scheme isomorphism,
  with both prescribed restriction triangles. Neither scheme needs affineness,
  separatedness or group structure. Tests and covers are as above; no transport
  to Milne's chosen small test category is asserted.
- [Faithfully flat image density](../SchemeProperties/FlatImageDensity.lean): a
  flat, surjective, locally finitely presented map of arbitrary schemes lifts
  every affine test after one faithfully flat *finitely presented* algebra
  map, with a commuting triangle. Over a field, flat surjections of locally
  finite-type schemes are one-cover dense on finitely generated algebra
  points; finite-type schemes specialize this result. Neither the schemes nor
  the morphism need be quasi-compact. The finite-type case extends Milne's
  Proposition 5.7 via Mathlib's finite affine refinement and coproduct.
  Direct import: `SchemeProperties.FlatImageDensity`.
- [Unit-power images and boundaries](../SchemeProperties/PowerImage.lean): over any
  commutative base ring, including the zero ring, the image of the power map on
  units is one-cover dense for `0 < n`, using one finite-free root algebra.
  Over a field and for `2 ≤ n`, the Laurent unit lies outside this image, which
  also fails singleton descent on its root cover. The zero additive subfunctor
  is not one-cover dense over a field. These distinguish density from pointwise
  fullness and from descent for the subfunctor. Direct import:
  `SchemeProperties.PowerImage`.
