# Scheme Properties

Reusable Lean interfaces for local scheme properties, components, quasicoherent
modules, rational maps and function fields. These constructions complement,
but do not replace, Mathlib's scheme and rational-map APIs.

## Headline results

- [Faithful flatness of finite families](SchemeProperties/RingTheory/FaithfullyFlatPi.lean):
  a finite family of flat commutative-ring maps that is jointly surjective on
  prime spectra induces a faithfully flat map to the product. The spectrum
  implication also holds for arbitrary families of commutative semirings,
  without flatness. Empty index types and zero rings are included.
- [Flatness under source precomposition](SchemeProperties/FlatSourceCancellation.lean):
  for arbitrary scheme morphisms `p : X ⟶ Y` and `f : Y ⟶ Z`, flatness and
  point-surjectivity of `p`, together with flatness of `p ≫ f`, imply flatness
  of `f`, without quasi-compactness or finiteness assumptions. The
  [ring-tower theorem](SchemeProperties/RingTheory/FlatSourceCancellation.lean)
  cancels a faithfully flat second map from a flat composite of commutative
  ring maps in independent universes; the composite need not be faithfully flat.

- [Closed points of scheme pullbacks](SchemeProperties/ClosedPointProducts.lean):
  for specified locally finite-type arrows to the spectrum of any field, the
  original projections of any specified pullback give a surjection onto pairs
  of closed points. Over a separably closed field this is a canonical set
  equivalence, with pairing, projection, uniqueness, eta, diagonal and
  fixed-base naturality laws. No global finite-type, quasi-compactness,
  separation or reducedness assumption is imposed. This does not identify the
  Zariski closed-point topology with the ordinary product topology.

- [Locally closed points in continuous preimages](SchemeProperties/LocallyConstructiblePreimage.lean):
  for arbitrary topological spaces and a continuous map, every nonempty preimage
  of a locally constructible set has a member at which that same preimage is
  locally closed. No separation, compactness or Noetherian hypothesis is needed;
  the result does not assert preservation of constructibility by continuous maps.
  A [dense-preimage application](SchemePropertiesExamples/LocallyConstructiblePreimage.lean)
  shows that a dense such preimage in a nonempty source has nonempty interior.

- [Closedness through closed points](SchemeProperties/JacobsonClosedPoints.lean):
  in any Jacobson topological space, a locally closed subset is closed if and only
  if its trace in the closed-point subspace is closed. Local closedness is required
  for the full subset, not just its trace; no separation or finiteness hypothesis
  is imposed.

- [Cofinite closed-point topology](SchemeProperties/Topology/ClosedPointCofinite.lean):
  in any preirreducible Noetherian topological space of Krull dimension at most
  one, a subset of the closed-point subspace is closed exactly when it is the
  whole space or finite. Its given topology is therefore cofinite, without
  separation, sobriety or Jacobson hypotheses. The Zariski closed-point topology
  of `Spec K[X]` and the Zariski topology of `MaximalSpectrum K[X]` are cofinite
  over every field `K`.

- [Locally constructible closed-point traces](SchemeProperties/JacobsonClosedPoints.lean):
  in any Jacobson topological space, a subset satisfying Mathlib's
  `Topology.IsLocallyConstructible` has a dense closed-point trace, and is closed
  exactly when that trace is closed in the original closed-point subspace.
  Closed-point traces also detect inclusion and equality between such subsets,
  with no separation or Noetherian hypothesis. The proofs use density after
  intersection with arbitrary locally closed subsets, without assuming those
  subsets are locally constructible. A common density theorem for arbitrary
  unions of locally closed sets recovers Mathlib's locally closed density theorem
  by a singleton-index specialization; this union theorem does not assert trace
  conservativity.

- [Maximal-point locally ringed spaces](SchemeProperties/MaximalPointSpace.lean):
  for any commutative Jacobson ring `R`, construct a locally ringed space on the
  closed-point subspace of `Spec R`. Its inclusion induces an isomorphism of
  full sheaves after pushforward, principal-open rings are `R_f`, stalks are
  `R_m`, and global sections recover `R`, with nilpotents and supplied scalars.
  [Localization-basis recognition](SchemeProperties/MaximalPointSheaf.lean)
  identifies any full sheaf with compatible coordinate actions and the same
  localization property. [Morphisms](SchemeProperties/MaximalPointMorphisms.lean)
  are contravariant for homomorphisms whose contractions preserve maximal
  ideals; this preservation is derived for finite-type homomorphisms from a
  Jacobson ring. [Full component uniqueness](SchemeProperties/MaximalPointSheafMaps.lean)
  identifies a supplied sheaf component from its global coordinates, without
  assuming that component is already local. The inclusion need not be an
  isomorphism of spaces, and no general Scheme structure is asserted for the
  maximal-point space.

- [Lifts to closed-point targets](SchemeProperties/ClosedPointLifts.lean):
  for a Jacobson locally ringed target `Y` and an arbitrary locally ringed source
  `X`, `closedPointInclusionHomEquiv` identifies maps `X ⟶ C(Y)` with original
  morphisms `X ⟶ Y` whose every image point is closed. The inverse is the unique
  full locally ringed-space lift through the given inclusion. Its section,
  stalk and global-section maps read back the original maps through the given
  comparisons. It is natural in every source morphism and in closed-point-preserving
  morphisms between Jacobson targets, and retains supplied structure-map triangles.
  Its [affine specialization](SchemeProperties/MaximalPointLifts.lean)
  identifies maps `X ⟶ C(R)` with original maps `X ⟶ Spec R` whose image ideals
  are all maximal, for any commutative Jacobson ring `R`, and reads back the
  original homomorphism `R → Γ(X)`. No Jacobson hypothesis is imposed on `X`
  or its global-section ring.

- [Hom recovery for maximal-point spaces](SchemeProperties/MaximalPointHom.lean):
  for commutative Jacobson rings `R` and `S`, `maximalPointHomEquiv` identifies
  ring homomorphisms `R →+* S` preserving maximal ideals under contraction with
  all locally ringed space morphisms `C(S) ⟶ C(R)`, where
  `C(R) = Spec.maximalPointSpace R`. The inverse is
  `χS⁻¹ ∘ Γ(g) ∘ χR` for the original coordinate isomorphisms, so the full
  morphism is recovered from its global-section map. This equivalence restricts
  to supplied scalar maps. For given `K`-algebra actions in a common universe,
  it identifies maximal-contraction-preserving algebra homomorphisms with
  morphisms over `Spec K`; if `S` is finite type over `K`, every algebra
  homomorphism corresponds, with no finite-type assumption on `R`.

- [Locality of full ringed morphisms](SchemeProperties/MaximalPointRingedHom.lean):
  for commutative Jacobson rings `R,S`, a ringed morphism `g : C(S) ⟶ C(R)`
  is local if and only if its original global-coordinate homomorphism
  preserves maximal ideals under contraction. Under this condition the entire
  original morphism is the forgotten `maximalPointMap`, and its unique locally
  ringed lift retains all supplied components and respects composition.
  For given `K`-algebra structures over any commutative ring `K`, scalar
  compatibility and finite type of `S` over `K` imply locality, with no
  finite-type hypothesis on `R`. The full sheaves retain nilpotents and the
  zero ring is included.

- [The integers are Jacobson](SchemeProperties/RingTheory/Jacobson/Int.lean):
  the canonical integer ring is a Jacobson ring. A
  [polynomial evaluation example](SchemePropertiesExamples/IntegerMaximalPointEvaluation.lean)
  identifies the maximal-point morphism over `Spec ℤ` induced by evaluation at
  zero, `ℤ[X] →ₐ[ℤ] ℤ`, together with its recovered ring map and the value `X ↦ 0`.

- [Reduced projective spectra](SchemeProperties/ProjReduced.lean): for any
  `ℕ`-graded commutative ring `A` with grading `𝒜`, `Proj 𝒜` is reduced whenever
  `A` is reduced, with no nonemptiness or finiteness assumption.

- [Polynomial projective coordinate separation](SchemeProperties/PolynomialProjGeometry.lean):
  over any nontrivial commutative ring and any nontrivial variable type, the
  total-degree polynomial projective spectrum has at least two underlying points.
  Coordinate points over the same coefficient prime are distinct for distinct
  indices; each lies in exactly its own coordinate basic open. This includes the
  projective line over the two-element field, without a domain or field-size bound.

- [Local normality of polynomial rings](SchemeProperties/NormalPolynomial.lean):
  over any commutative locally normal base ring, multivariate polynomial rings
  with arbitrary variable types are locally normal.

- [Global sections under flat scalar extension](SchemeProperties/GlobalSectionsBaseChange.lean):
  for a quasicompact quasiseparated scheme over a commutative ring `k` and a flat
  commutative `k`-algebra `K`, the canonical equivalence identifies the global
  sections of the base change with `K ⊗[k] Γ(X, ⊤)`. Its scalar, section and pure
  tensor formulas retain the two pullback projections. Identity and tower
  coherence are also available for field extensions.
- [Global sections and affine targets](SchemeProperties/GlobalSections.lean): if
  `p : X ⟶ S` induces an isomorphism on global sections and `T` is affine,
  precomposition is a bijection `(S ⟶ T) → (X ⟶ T)`, for arbitrary `X` and
  `S`. A reduced connected scheme universally closed over a field has a
  field of global sections. For a reduced preconnected scheme universally
  closed over a field, a rational section identifies its global sections
  with the base field, so every morphism to an affine scheme is constant at
  that rational point. Direct import for the field criterion and the
  canonical global-sections isomorphism: `SchemeProperties.GlobalSections.Field`.

- [Proper affine point criterion](SchemeProperties/ProperAffineField.lean): for any
  field `K : Type u` and `X : Scheme.{u}`, a morphism
  `f : X ⟶ Spec (CommRingCat.of K)` with
  `[IsProper f] [IsAffine X] [PreconnectedSpace X]` gives `Subsingleton X`
  (`AlgebraicGeometry.Scheme.Hom.subsingleton_of_isProper_of_isAffine`).
  The underlying point set has at most one point; `X` may be empty or nonreduced.
  This does not assert a scheme isomorphism or uniqueness of scheme morphisms.
  Direct import: `SchemeProperties.ProperAffineField`.

- [Finite-variable polynomial Proj](SchemeProperties/PolynomialProjProper.lean) is proper over the original `Spec R` for every commutative ring `R : Type (max u v)` and finite `σ : Type v`, including zero rings and empty `σ`; see the [guide](docs/SpectraAndGlobalGeometry.md#polynomial-proj-properness).

- [Rigidity from a collapsed fibre](SchemeProperties/Rigidity.lean): for a
  field `K`, a proper integral `K`-scheme `X` whose structure map has a
  `K`-rational section, a preconnected `K`-scheme `Y` with an arbitrary chosen
  point `y₀`, and a `K`-scheme `Z` separated over `K`, a compatible `K`-morphism
  `h : X ×[K] Y ⟶ Z` factors uniquely as `h = snd ≫ g` for a `K`-morphism
  `g : Y ⟶ Z` if the topological image under `h` of the projection fibre over
  `y₀` is subsingleton. The factorization is equality of scheme morphisms.
  The parameter need not be reduced, and `y₀` need not be rational or closed.
  Direct import: `SchemeProperties.Rigidity`.

- [Real–complex residue degrees](SchemeProperties/RealComplexSpectrum.lean):
  the coproduct `Spec ℝ ⨿ Spec ℂ`, over `Spec ℝ` by the identity and the
  standard real-algebra map to `ℂ`, has two distinct closed points. Their
  original residue real algebras are canonically equivalent to `ℝ` and `ℂ`
  and have real dimensions one and two, respectively.

## Mathematical guides

The full statements, material hypotheses, API limitations and examples are
organized by topic:

- [Points and morphism criteria](docs/PointsAndMorphisms.md): affine tests,
  reduced-source and closed-point tests, lifting and finite point fibers.
- [Local properties and dimension](docs/LocalPropertiesAndDimension.md):
  reduced loci, normality, dimension bounds, components and modules.
- [Spectra and global geometry](docs/SpectraAndGlobalGeometry.md):
  projective spectra, global sections, rigidity and ring-pullback spectra.
- [Single-cover density and descent](docs/SingleCoverDescent.md):
  subfunctor extensions, represented targets, group objects and boundaries.
- [Rational maps and function fields](docs/RationalMapsAndFunctionFields.md):
  dense-open composition, relative categories and function-field comparisons.

## Using the library

`import SchemeProperties` loads the [aggregate](SchemeProperties.lean). For
focused imports use `SchemeProperties.<Module>` from the [reader guide's module
tables](docs/Guide.md); the [documentation index](docs/README.md) links focused
mathematical guides. Inspect direct-import [test clients](SchemePropertiesTest/) and concrete
[examples](SchemePropertiesExamples/) for use cases; the [module-name guide](docs/ModuleNames.md)
lists their import roots. For instance, import
`SchemeProperties.GenericPointFunctionField`,
`SchemeProperties.GenericPointRationalNoninvertibility`,
`SchemeProperties.RationalMapPartialIso` or
`SchemeProperties.ModuleFinitePresentation` directly. The ring-equivalence
reduced-locus theorems are in `SchemeProperties.ReducedLocusEquiv`; the
polynomial quotient theorem uses the released Multivariate Polynomials
presentation in `SchemeProperties.PolynomialPointSquareZeroReducedLocus`.

```lean
import SchemeProperties
```

[API.md](docs/API.md) and its [manifest](docs/api-manifest.json) are a **fixed
historical 73-module** API documentation snapshot, not a current declaration
census. The [API reproduction guide](docs/README.md) explains its immutable
input contract; later results are in focused guides and source files.

## Build

[Lean](lean-toolchain) is pinned to v4.34.0-rc2; mathlib and the project
dependencies have exact revisions in [Lake](lakefile.toml) and the
[manifest](lake-manifest.json). `coherent-modules`, `finite-etale-algebras`,
`multivariate-polynomials`, `minimal-primes` and
[`graded-rings`](https://github.com/FormalFrontier/graded-rings) use public GitHub
releases; `algebraic-direct-limits` is also pinned as an inherited dependency. Install
[elan](https://github.com/leanprover/elan), fetch the matching mathlib cache
successfully for this checkout (again after changing pins or `.lake`), then
build the library, tests and examples:

```sh
lake exe cache get
lake build SchemeProperties SchemePropertiesTest SchemePropertiesExamples
```

An optional `lake --wfail build ...` check makes warnings fatal. These targets
currently emit linter warnings, so that check can fail even when the normal
build succeeds.

## References

- A. Grothendieck, with J. Dieudonné, *Éléments de géométrie algébrique II:
  Étude globale élémentaire de quelques classes de morphismes*, Publications
  Mathématiques de l'IHÉS 8 (1961), Corollary 6.1.15 and its affine argument,
  p. 114: the rational-section formulation is compared with the canonical
  function-field-map criterion in
  [IntegralBirationalIsomorphism](SchemeProperties/IntegralBirationalIsomorphism.lean).
- Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*: Exercise
  5.3.C informs the integrality criterion; the aside to Exercise 5.4.M informs
  separable-base-change normality; the discussion of reduced local rings and
  their locus informs the reduced-stalk openness result; Definition 6.1.1,
  Theorem 6.1.2 and the opening of §6.3 inform affine-cover quasicoherence and
  its abelian structure.
- J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over
  a Field*: item 1.4/Appendix A.33 informs finite-type set-valued points;
  Propositions 1.29–1.31, the paragraph before 1.30 and Corollary 1.32(a)
  inform finite-étale components and their fibres. Appendix A.14 supplies the
  Noetherian finite/clopen-component antecedent. Definition 5.6, its following
  power-image example, Lemma 5.9 and Proposition 5.10 inform one-cover density
  and extension; Proposition 5.7 is the finite-type antecedent for flat-image
  density. Corollary 5.11 informs the isomorphism extension from two dense
  subfunctors, whose inverse laws follow from extension uniqueness. Proposition
  5.12 motivates the generic group-object extension, not a represented-scheme
  group-law theorem. Mathlib fpqc descent supplies the represented-target proof,
  while finite affine refinement supplies the flat-image lifting proof.
- J. S. Milne, *Abelian Varieties*, version 2.00, Conventions, p. v:
  motivation for the independent Jacobson-space comparison between
  closed-point and whole-space connectedness, not a named theorem of that text.
  Chapter I, Theorem 1.1 informs the rigidity problem and the
  proper-neighborhood/affine-target argument in
  [Rigidity](SchemeProperties/Rigidity.lean).
- Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter I, §5: motivation for affine finite-presentation work.
- [The Stacks Project](https://stacks.math.columbia.edu/), tags 037U, 0386,
  0385 and 0363: a proof route from field-extension geometric connectedness
  to connected schemes over separably closed fields.
- [Stacks Project, Tag 030A](https://stacks.math.columbia.edu/tag/030A), cited by
  Multivariate Polynomials for the normal-domain polynomial ingredient of
  [polynomial local normality](SchemeProperties/NormalPolynomial.lean), not the
  whole locally normal base and two-stage localization argument.
- [Mathlib](https://github.com/leanprover-community/mathlib4): reused scheme,
  rational-map, restricted-Yoneda, flat-sections, tensor, sheaf and descent
  methods, as well as adapted constructions detailed in
  [Credits](docs/CREDITS.md), with authentic upstream notices preserved.
- [Coherent Modules](https://github.com/FormalFrontier/coherent-modules),
  [Finite Étale Algebras](https://github.com/FormalFrontier/finite-etale-algebras)
  and [Multivariate Polynomials](https://github.com/FormalFrontier/multivariate-polynomials/tree/602ba00e0d71b83ecc78adebffef1a494b2a47b1):
  prior formalizations used for coherent-module localization, finite-étale
  component algebras and descent, the polynomial point-quotient presentation,
  and `MultivariatePolynomials.IntegrallyClosed`'s `MvPolynomial.isIntegrallyClosed`.
  Polynomial local normality extends this project's existing univariate
  coefficient-prime localization strategy to arbitrary variables.

- [Minimal Primes](https://github.com/FormalFrontier/minimal-primes) supplies
  `IsReduced.of_isLocalization`, the canonical independent-universe
  commutative-semiring theorem used for reducedness under localization. It
  generalizes Andrew Yang's Mathlib `isReduced_localizationPreserves` and the
  earlier commutative-ring formulation in `SchemeProperties.Reduced`; its proof
  uses Mathlib's radical-localization and nilradical APIs.
  Minimal Primes also supplies the tensor-field dimension theorem
  `Algebra.ringKrullDim_tensorProduct_of_finiteType` and the arbitrary open-cover
  supremum theorem `topologicalKrullDim_eq_iSup_of_isOpenEmbedding_cover`, used
  together in `SchemeProperties.Dimension.FieldExtension`.

- [Graded Rings](https://github.com/FormalFrontier/graded-rings) supplies
  [`HomogeneousLocalization.isReduced`](https://github.com/FormalFrontier/graded-rings/blob/cb0f2e43578783e926fe8b216d103496d3d93313/GradedRings/HomogeneousLocalizationReduced.lean),
  the homogeneous-localization reducedness API used for the stalks of
  [reduced projective spectra](SchemeProperties/ProjReduced.lean).

The [credits](docs/CREDITS.md) distinguish mathematical antecedents, followed
proof patterns, imported APIs, adapted expression and original project work.

## Credits and license

**Authors: Formal Frontier Agents.** Original project work is
[Apache-2.0 licensed](LICENSE). [Credits](docs/CREDITS.md) distinguish adapted
formal expression, original contributors, mathematical sources and upstream
notices. The [references](#references) identify the published arguments and
prior formalizations used throughout the library; the credits explain their
different roles in the Lean constructions. The group-object construction uses
the existing single-cover extension API and Mathlib's Cartesian group-object
infrastructure; Milne's Proposition 5.12 motivates its conditional presheaf form.
Formal Frontier maintainers and contributors developed Lean proofs, examples and
documentation with AI assistance and mathematical review.


## Closures of preirreducible powers

`IsPreirreducible.exists_closure_pow_eq` shows that the closures of the powers of a
preirreducible subset containing the identity eventually stabilize in a separately
continuous monoid, provided its order of irreducible closed subsets is
finite-dimensional. The result includes the zeroth power and requires neither
joint continuity nor a separation axiom. Import
`SchemeProperties.Topology.IrreduciblePowers` to use it.

## Generic flatness

A locally finite type, quasi-compact morphism to an integral scheme is flat over a
nonempty dense open of the target, on the whole preimage of that open. No
Noetherianity assumption on the target is needed. See
[`SchemeProperties/GenericFlatness/Uniform.lean`](SchemeProperties/GenericFlatness/Uniform.lean).

For a locally finite type morphism to an integral scheme, every point above the generic
point has an affine source neighborhood on which the morphism is flat. Surjectivity
therefore gives a genuinely nonempty such affine source open, without assuming
quasi-compactness; see
[`SchemeProperties/GenericFlatness/Pointed.lean`](SchemeProperties/GenericFlatness/Pointed.lean).

More generally, a surjective locally finite type morphism `f : X ⟶ Y` to a nonempty
reduced scheme with finitely many irreducible components has a nonempty affine open
`U : X.Opens` with `Flat (U.ι ≫ f)`, without assuming quasi-compactness. Its image
need not be dense in the whole target. See
[`SchemeProperties/GenericFlatness/Reduced.lean`](SchemeProperties/GenericFlatness/Reduced.lean).

The proofs use Mathlib's scheme, localization, and flatness APIs and the public
multivariate-polynomials generic-freeness theorem
`Algebra.FiniteType.exists_free_localizationAway`. For background on generic
flatness, see J. S. Milne, *Algebraic Groups* (2017).
