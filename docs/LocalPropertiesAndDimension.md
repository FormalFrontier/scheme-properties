# Local properties and dimension

See the [overview](../README.md), [reader guide](Guide.md) and
[documentation index](README.md) for navigation and imports. Mathematical
[references](../README.md#references) and [credits](CREDITS.md) apply throughout.

## Flatness under source precomposition

For arbitrary morphisms `p : X ⟶ Y` and `f : Y ⟶ Z`,
`AlgebraicGeometry.Flat.of_comp p f` deduces flatness of `f` from flatness and
point-surjectivity of `p` and flatness of `p ≫ f`. No quasi-compactness,
Noetherianity, affineness or finiteness hypothesis is needed. The proof works
on full local stalk rings and includes empty schemes.

Its ring-theoretic input, `RingHom.Flat.of_comp_of_faithfullyFlat`, takes
commutative ring maps `a : A →+* B` and `b : B →+* C` in independent universes.
Faithful flatness of `b` and flatness of `b.comp a` imply flatness of `a`.
Faithful flatness of the composite is not assumed, and zero rings are allowed.
These theorems concern a source tower, rather than target base-change descent.
Direct imports: `SchemeProperties.FlatSourceCancellation` and
`SchemeProperties.RingTheory.FlatSourceCancellation`.

## Going down and flat stalk dimensions

- [Going down](../SchemeProperties/RingTheory/KrullDimension/GoingDown.lean) bounds
  the height of the contraction of **any** ideal by its height, including infinite
  heights. A generalizing local ring map with local target bounds the source
  dimension by the target dimension; flat local maps specialize this result.
- [Flat stalk dimensions](../SchemeProperties/FlatStalkDimension.lean): at any point
  where the canonical stalk map is flat, the full target-stalk dimension is at
  most the source-stalk dimension. Flat scheme morphisms satisfy this everywhere.
  Neither bound requires Noetherianity or finite dimension.

## Reduced local rings

- [Reduced-localization locus](../SchemeProperties/ReducedLocus.lean): over any
  commutative ring, a prime localization is reduced exactly when its prime is
  outside the **module** support of the nilradical. Consequently the nonreduced
  locus equals that support, and finite generation of the nilradical as a module
  suffices for the reduced locus to be open; this finiteness is not necessary.
  On any locally Noetherian scheme the locus of points with reduced stalks is
  open, without a quasi-compactness assumption. The proofs use Mathlib's
  localization of radicals, module support and affine stalk descriptions.
  Direct import: `SchemeProperties.ReducedLocus`.
- [Ring-equivalence reduced loci](../SchemeProperties/ReducedLocusEquiv.lean):
  an equivalence of commutative semirings with independent universes preserves
  reducedness of localizations at corresponding primes and openness of the
  **entire** reduced prime-localization locus. No finiteness or reducedness
  hypothesis is needed. Direct import: `SchemeProperties.ReducedLocusEquiv`.
- [Square-zero reduced localizations](../SchemeProperties/TrivSqZeroExtReducedLocus.lean):
  for any commutative ring `R`, any `R`-module `M` and a prime `p` of `R`, an
  arbitrary prime-localization model of the square-zero extension at the prime
  over `p` is reduced precisely when an arbitrary prime-localization model of
  `R` at `p` is reduced **and** `p` lies outside the module support of `M`.
  If `R` is reduced, the pullback of the reduced-localization locus is exactly
  the complement of that support; the full extension locus is open if and only
  if the support itself is closed. Neither finite generation nor a Noetherian
  hypothesis is required. The criterion uses Mathlib's prime-localization,
  support and square-zero projection-kernel APIs, together with Coherent Modules'
  canonical actions on the extension.
  Direct import: `SchemeProperties.TrivSqZeroExtReducedLocus`.
- [Polynomial point modules](../SchemeProperties/PolynomialPointReducedLocus.lean):
  for any family of points over a field, the support of the direct sum of
  evaluation quotients is exactly the image of their evaluation primes. This
  support is closed, and the full reduced prime-localization locus of its
  square-zero extension is open, precisely when the family has finite image.
  Even an infinite family constantly repeating one point satisfies the
  criterion. Direct imports: `SchemeProperties.PolynomialPointPrime` and
  `SchemeProperties.PolynomialPointReducedLocus`.
- [Polynomial point quotients](../SchemeProperties/PolynomialPointSquareZeroReducedLocus.lean):
  for an injective family of points over any field, the reduced-localization
  locus at **all** primes of its square-zero polynomial quotient is open exactly
  when the point family's image is finite. Injectivity supplies pairwise unit
  differences for the canonical quotient presentation; this does not classify
  nonseparated point families. The singleton quotient can be nonreduced while
  its reduced-localization locus is open. Direct import:
  `SchemeProperties.PolynomialPointSquareZeroReducedLocus`.

## Global dimension under flat surjections

- [Ring dimension](../SchemeProperties/RingTheory/KrullDimension/GeneralizingMap.lean):
  a ring homomorphism `R →+* S` whose prime contraction is **generalizing and
  surjective** satisfies `ringKrullDim R ≤ ringKrullDim S`. In particular,
  faithful flatness suffices; the commutative rings may have independent universes.
- [Scheme dimension](../SchemeProperties/FlatKrullDimension.lean): a **flat,
  point-surjective** morphism `f : X ⟶ Y` of schemes in a common universe gives
  `Order.krullDim Y ≤ Order.krullDim X`. This is a global bound, not equality
  of a chosen pair of stalk dimensions. No Noetherianity, quasi-compactness,
  finite-type or quasi-finiteness assumption is needed. Dimensions lie in
  `WithBot ℕ∞`, including `⊥` for zero rings/empty schemes and `∞`.
  The [private affine-line client](../SchemePropertiesTest/FlatKrullDimension.lean)
  applies all three bounds to `ℚ → ℚ[X]` and `Spec ℚ[X] → Spec ℚ`, with
  independent dimensions `0 < 1`; the flat fraction-ring map shows why
  surjectivity cannot simply be omitted. Direct imports:
  `SchemeProperties.RingTheory.KrullDimension.GeneralizingMap` and
  `SchemeProperties.FlatKrullDimension`.

## Dimension under extension of a field

- [Affine-field base change](../SchemeProperties/Dimension/FieldExtension.lean):
  for affine schemes `S` and `T` whose canonical global section rings are fields,
  any locally finite type `p : X ⟶ S` and any `q : T ⟶ S` satisfy
  `topologicalKrullDim (Limits.pullback p q) = topologicalKrullDim X`.
  The field assumptions are ordinary `IsField` witnesses, not chosen field
  structures on new rings. The field-spectrum corollary applies to every field
  extension `K → L` and every scheme locally of finite type over `K`.
  These are the canonical categorical pullbacks with the original Zariski
  topologies. Dimensions lie in `WithBot ℕ∞`, including `⊥` for empty schemes
  and `∞`. No quasi-compactness, quasi-separatedness, global Noetherianity or
  finite-type hypothesis on the global section ring of `X` is imposed.
  All schemes and fields in each statement share one universe; transport
  between differently sized scheme presentations is not provided.
  Direct import: `SchemeProperties.Dimension.FieldExtension`; the
  [private examples](../SchemePropertiesTest/Dimension/FieldExtension.lean) use
  zero-ring spectra, polynomial spectra and their countable coproduct.

## Quasi-finite dimension bounds and local preservation

- [Global ring bounds](../SchemeProperties/RingTheory/KrullDimension/QuasiFinite.lean):
  `RingHom.QuasiFinite.strictMono_comap hf` makes contraction strict on
  **comparable** primes, not globally injective on all primes.
  `RingHom.QuasiFinite.ringKrullDim_le hf` gives `ringKrullDim S ≤ ringKrullDim R`
  for `f : R →+* S`, with independent ring universes.
- [Global scheme bounds](../SchemeProperties/QuasiFiniteKrullDimension.lean):
  `AlgebraicGeometry.LocallyQuasiFinite.krullDim_le f` gives
  `Order.krullDim X ≤ Order.krullDim Y` for `f : X ⟶ Y` between schemes in
  a common universe. The scheme order reverses specialization. Both global
  bounds take values in `WithBot ℕ∞`, including empty spectra of dimension
  `⊥` and infinite dimension. They need no flatness, Noetherianity, local
  finite type or quasi-compactness: quasi-finiteness means Mathlib's
  finite-dimensional residue-field fibers. These are upper bounds for whole
  spaces, not equalities of stalk dimensions. The [closed-origin example](../SchemePropertiesTest/QuasiFiniteKrullDimension.lean)
  uses the finite, nonflat evaluation `ℚ[X] →+* ℚ` and its Spec map, with
  dimensions independently computed as `0 < 1`; the opposite coefficient
  inclusion and affine-line projection fail the respective quasi-finiteness
  hypotheses.

## Flat quasi-finite dimension preservation

- [Prime heights and local rings](../SchemeProperties/RingTheory/KrullDimension/QuasiFinite.lean):
  a quasi-finite algebra with going down preserves the height of each prime
  under contraction. A flat quasi-finite local homomorphism of commutative
  local rings therefore preserves Krull dimension, with independent ring
  universes. No Noetherian or finite-type hypothesis is required.
  Direct import: `SchemeProperties.RingTheory.KrullDimension.QuasiFinite`.
- [Full scheme stalks](../SchemeProperties/FlatQuasiFinite.lean): for a scheme
  morphism `f : X ⟶ Y` and a point `x`, flatness and quasi-finiteness of the
  stalk map imply equality of the Krull dimensions of the full stalks at
  `x` and `f x`. The assumptions are pointwise, not global morphism classes;
  these are not fibre-stalk dimensions.
  Direct import: `SchemeProperties.FlatQuasiFinite`.

## Integral neighborhoods

- [Integral neighborhoods](../SchemeProperties/Integral.lean): on a locally
  Noetherian scheme, every point with a domain local ring has an integral open
  neighborhood, and the locus of such points is open. No global reducedness or
  quasi-compactness assumption is required. In particular, a connected locally
  Noetherian scheme whose local rings are domains is integral.
  Direct import: `SchemeProperties.Integral`.

## Local normality

- [Normality under scheme morphisms](../SchemeProperties/NormalMorphisms.lean):
  for a morphism `f : X ⟶ Y` of schemes, a normal target and smooth `f`
  imply a normal source (`AlgebraicGeometry.isNormal_of_smooth`). A normal
  source and flat, point-surjective `f` imply a normal target
  (`AlgebraicGeometry.isNormal_of_surjective_of_flat`), without a
  quasi-compactness assumption. Étale ascent follows from étale ⇒ smooth.
  Direct import: `SchemeProperties.NormalMorphisms`.
- [Faithfully flat descent](../SchemeProperties/NormalFaithfullyFlat.lean): for
  commutative rings `R` and `S` in independent universes, an `R`-algebra `S`
  that is faithfully flat as its canonical `R`-module and locally normal
  implies that `R` is locally normal. Here local normality means that every
  prime localization is an integrally closed domain; disconnected and zero
  rings are allowed. No Noetherian, finite or global-domain hypothesis is
  needed. The entry point is `IsLocallyNormalRing.of_faithfullyFlat`, a theorem
  rather than an instance. Direct import: `SchemeProperties.NormalFaithfullyFlat`.

- [Sections and stalk images](../SchemeProperties/FunctionField/Sections.lean): on an
  integral scheme, a rational function comes from a section on a nonempty open set
  exactly when it lies in the image of every stalk over that open set, under the
  canonical maps to the function field. Normality is not required.
- [Integrally closed sections](../SchemeProperties/NormalSections.lean): the section
  ring on every open set of a normal integral scheme is integrally closed,
  including the zero ring on the empty open set. On nonempty opens, it is also
  integrally closed in the function field under the canonical embedding. No
  identification of the function field with the fraction ring of sections on an
  arbitrary open set is assumed.

## Local properties, components and modules

- [Local normality under étale algebras](../SchemeProperties/NormalEtale.lean):
  an étale algebra over a locally normal commutative ring is locally normal,
  with independent base and target universes. Neither module-finiteness nor
  Noetherianity is assumed; the algebra itself may be disconnected.
- [Geometric irreducibility implies geometric connectedness](../SchemeProperties/GeometricallyConnected.lean):
  every geometrically irreducible morphism of arbitrary same-universe schemes
  is geometrically connected, by typeclass synthesis. No finite-type or
  nonempty-target assumption is needed. Direct import:
  `SchemeProperties.GeometricallyConnected`.
- [Connectedness through closed points](../SchemeProperties/JacobsonConnectedness.lean):
  any Jacobson topological space is connected if and only if its induced subspace
  of closed points is connected, with no separation, Noetherianity, compactness
  or nonemptiness assumption. The [affine-line example](../SchemePropertiesTest/JacobsonConnectedness.lean)
  has a connected proper closed-point subspace. Direct import:
  `SchemeProperties.JacobsonConnectedness`.
- [Products of locally normal rings](../SchemeProperties/LocallyNormalRing/Pi.lean):
  local normality of an arbitrary product descends to each factor, and a finite
  product is locally normal if and only if all its factors are. The index and
  coefficient universes are independent; empty products and zero factors are
  included. The finite-product theorem is also available from
  `SchemeProperties.NormalEtale`.
- [Local normality at maximal ideals](../SchemeProperties/LocallyNormalRing/Maximal.lean):
  a commutative ring is locally normal exactly when its localizations at all
  maximal ideals are domains and integrally closed. This includes zero and
  disconnected rings, with no Noetherian or global-domain assumption.
  Direct import: `SchemeProperties.LocallyNormalRing.Maximal`.
- [Normality and factoriality](../SchemeProperties/FactorialNormal.lean) relates
  stalkwise factorial schemes to normal schemes. The
  [normality criteria](../SchemeProperties/Normal.lean) characterize normality of an
  affine scheme by local normality of its global sections, of an affine open by
  local normality of its ambient ring of sections, and of a scheme by local
  normality of every coordinate ring of any affine open cover. The cover's index
  universe may be independent of the scheme universe. The [local-normality
  interfaces](../SchemeProperties/NormalSeparableScheme.lean) also cover base
  change along transcendental-separable field extensions, not all extensions.
- [Locally normal binary products](../SchemeProperties/LocallyNormalRing/Product.lean):
  for commutative rings `R : Type u` and `S : Type v`, `R × S` is locally
  normal if and only if both factors are locally normal. The universes are
  independent, zero-ring factors are allowed, and no domain or Noetherian
  hypothesis is needed. Direct import: `SchemeProperties.LocallyNormalRing.Product`.
- [Finite-étale component schemes](../SchemeProperties/ComponentScheme.lean)
  give the universal factorization through finite-étale affine targets for a
  quasicompact scheme locally of finite type over a field; the construction
  includes empty and nonreduced schemes.
- [Module tensors](../SchemeProperties/ModuleTensor.lean) sheafify the tensor of
  arbitrary scheme modules, with a [principal-affine-open section
  comparison](../SchemeProperties/ModuleTensorLocalization.lean), not an
  arbitrary-open sections equivalence or a global monoidal instance.

- [Finite presentations](FinitePresentations.md): finite presentations of
  sheaves of modules restrict along open immersions, and locally finitely
  presented sheaves admit finite presentations on an affine open cover; the
  cover need not be finite. See [the adapted construction](../SchemeProperties/ModuleFinitePresentation.lean).
- [Components and quasicoherence](Guide.md): component schemes,
  coproduct sections, geometric connectedness, quasicoherent abelian structure
  and tensors have distinct hypotheses indexed in the reader guide.

## Dimension imports

The Mathlib-only algebra leaf
`SchemeProperties.RingTheory.KrullDimension.QuasiFinite` supplies global ring
dimension bounds, prime-height preservation and local-ring dimension preservation.
`SchemeProperties.QuasiFiniteKrullDimension` supplies the global scheme bound;
these two modules can be imported directly. The closed-origin use is in
`SchemePropertiesTest.QuasiFiniteKrullDimension`. `SchemeProperties.FlatQuasiFinite`
adds the distinct pointwise full-stalk equality application; the affine-line
double-cover use is maintained in `SchemePropertiesTest.FlatQuasiFinite`.

## Reducedness under localization

`SchemeProperties.Reduced` re-exports
`MinimalPrimes.RingTheory.Localization.Reduced`. Its theorem
`IsReduced.of_isLocalization` preserves reducedness under arbitrary localization
of commutative semirings in independent universes. The prime-localization and
scheme-stalk results use this theorem; `IsLocalization.isReduced` retains the
commutative-ring interface as a deprecated specialization.
