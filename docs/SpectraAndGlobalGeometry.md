# Spectra and global geometry

See the [overview](../README.md), [reader guide](Guide.md) and
[documentation index](README.md) for navigation and imports. Mathematical
[references](../README.md#references) and [credits](CREDITS.md) apply throughout.

## Open factorization for closed maps

- [Open factorization for closed maps](../SchemeProperties/KernImage.lean): for
  `π : E ⟶ B` with explicit `IsClosedMap π`, `f : E ⟶ Z` and opens `U ⊆ Z`,
  `V ⊆ B`, the bound `V ≤ π.kernImage hπ (f ⁻¹ᵁ U)` is equivalent to a unique
  scheme morphism `(π ⁻¹ᵁ V).toScheme ⟶ U.toScheme` factoring the restriction
  of `f`. `Scheme.Hom.le_kernImage_preimage_iff_existsUnique` uses Mathlib's
  `resLE`; no finiteness, reducedness or separatedness is assumed. This is an
  auxiliary open-factorization property, not a rigidity theorem. Direct import:
  `SchemeProperties.KernImage`; the [coproduct-square example](../SchemePropertiesTest/KernImage.lean)
  has a nonempty proper good-fibre open and a nonsaturated target preimage.

## Global sections and affine targets

- [Global sections and affine targets](../SchemeProperties/GlobalSections.lean): if
  `p : X ⟶ S` induces an isomorphism on global sections and `T` is affine,
  precomposition is a bijection `(S ⟶ T) → (X ⟶ T)`, for arbitrary `X` and
  `S`. A reduced connected scheme universally closed over a field has a
  field of global sections. For a reduced preconnected scheme universally
  closed over a field, a rational section identifies its global sections
  with the base field, so every morphism to an affine scheme is constant at
  that rational point. Direct import for the field criterion and the
  canonical global-sections isomorphism: `SchemeProperties.GlobalSections.Field`.

## Points of proper affine schemes over a field

- [Proper affine point criterion](../SchemeProperties/ProperAffineField.lean): for any
  field `K : Type u` and `X : Scheme.{u}`, a morphism
  `f : X ⟶ Spec (CommRingCat.of K)` with
  `[IsProper f] [IsAffine X] [PreconnectedSpace X]` gives `Subsingleton X`
  (`AlgebraicGeometry.Scheme.Hom.subsingleton_of_isProper_of_isAffine`).
  The underlying point set has at most one point; `X` may be empty or nonreduced.
  This does not assert a scheme isomorphism or uniqueness of scheme morphisms.
  Direct import: `SchemeProperties.ProperAffineField`.

## Projective spectra

- [Reducedness and integrality](../SchemeProperties/ProjectiveSpectrum.lean): for an
  `ℕ`-grading `𝒜` of a commutative ring `A`, `Proj 𝒜` is reduced if `A` is
  reduced, and preirreducible if `A` is a domain, including when it is empty.
  A nonempty projective spectrum of a domain is integral. No finite generation
  or generation in degree one is required.
  Direct import: `SchemeProperties.ProjectiveSpectrum`.

- [Polynomial projective space](../SchemeProperties/PolynomialProjectiveSpace.lean):
  for every commutative ring `R` and `n : ℕ`, `PolynomialProjectiveSpace R n`
  is `Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)`.
  The canonical `toSpec` and `coordinateSection R n i`, for every
  `i : Fin (n + 1)`, satisfy `coordinateSection R n i ≫ toSpec R n = 𝟙 _`
  as scheme morphisms, including `n = 0` and the zero ring.
  The model is nonempty for nontrivial `R` and integral for domain `R`.
  `Proj.nonempty_mvPolynomial` and `Proj.isIntegral_mvPolynomial` are
  theorem-only generalizations to any nonempty variable type in an
  independent universe, with the same respective ring hypotheses.
  [Coordinate evaluation](../SchemeProperties/PolynomialProjCoordinates.lean)
  restricts to the identity on coefficients through degree zero and homogeneous
  localization (`coordinateAwayEval_fromZeroRingHom` and
  `coordinateAwayEval_comp_fromZeroRingHom`).

## Rigidity

- [Rigidity from a collapsed fibre](../SchemeProperties/Rigidity.lean): for a
  field `K`, a proper integral `K`-scheme `X` whose structure map has a
  `K`-rational section, a preconnected `K`-scheme `Y` with an arbitrary chosen
  point `y₀`, and a `K`-scheme `Z` separated over `K`, a compatible `K`-morphism
  `h : X ×[K] Y ⟶ Z` factors uniquely as `h = snd ≫ g` for a `K`-morphism
  `g : Y ⟶ Z` if the topological image under `h` of the projection fibre over
  `y₀` is subsingleton. The factorization is equality of scheme morphisms.
  The parameter need not be reduced, and `y₀` need not be rational or closed.
  Direct import: `SchemeProperties.Rigidity`.

## Ring-pullback spectra

- [Whole prime-spectrum pushout of a surjective ring pullback](../SchemeProperties/PullbackSpectrumPushout.lean):
  for commutative rings `A → C ← B`, with only `A → C` surjective and
  `B → C` arbitrary, the whole `Spec (A ×_C B)` is the pushout of
  `Spec A ← Spec C → Spec B` as **topological spaces**, including the closed
  gluing locus and zero-ring cases. Ring carriers may live in independent
  universes. A subset of the pullback spectrum is open exactly when its
  preimages in `Spec A` and `Spec B` are open; continuous maps from these
  spectra that agree on `Spec C` descend uniquely to any target topological
  space, regardless of its universe. This does not assert a scheme pushout.
  Direct import: `SchemeProperties.PullbackSpectrumPushout`.

- [Open immersions on ring-pullback complements](PullbackOpenImmersion.md):
  for arbitrary commutative-ring maps `R → T ← S`, the actual maps from
  `Spec R \ V(ker f)` and `Spec S \ V(ker g)` to the spectrum of their ring
  pullback are open immersions. Their respective ranges are the complements
  of the *opposite* projection kernels; they are disjoint and cover the
  complement of the common-map kernel. These opens may be empty; no total
  Spec-map immersion or connected-component claim follows. Direct import:
  `SchemeProperties.PullbackOpenImmersion`; the [direct-import client](../SchemePropertiesTest/PullbackOpenImmersionClient.lean)
  is included.
