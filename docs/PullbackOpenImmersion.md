# Open immersions on ring-pullback complements

Import `SchemeProperties.PullbackOpenImmersion`. The API lives in the namespace
`AlgebraicGeometry.PullbackOpenImmersion`; it requires only commutative rings
`R`, `S`, `T` (in the same universe) and ring homomorphisms
`f : R →+* T`, `g : S →+* T`. There is no surjectivity, nontriviality,
field, finite-type or nonemptiness condition.

Let `P = f.pullback g`, `qR = f.pullbackFst g : P →+* R`,
`qS = f.pullbackSnd g : P →+* S`, and `h = toBase f g = f.comp qR`.
Write `U(q) = Spec(domain q) \ V(ker q)` for the open returned by
`kernelComplement q`. In particular, `fstSource f g = U(f)` and
`sndSource f g = U(g)`; these are scheme opens, not just point predicates.
The underlying arrows `fstMap f g : Spec R ⟶ Spec P` and
`sndMap f g : Spec S ⟶ Spec P` are the actual contravariant `Spec.map`
arrows induced by `qR` and `qS`. The restricted arrows are exactly

```text
fstOpenMap f g = (fstSource f g).ι ≫ fstMap f g : U(f) ⟶ Spec P
sndOpenMap f g = (sndSource f g).ι ≫ sndMap f g : U(g) ⟶ Spec P.
```

## Algebra and charts

`ker_fst_mul_ker_snd` proves `ker(qR) * ker(qS) = 0`: elements with
zero first and zero second coordinates annihilate each other in `P`.
`ker_toBase` proves `ker(h) = ker(qR) ⊔ ker(qS)`: if `h(r,s)=0`, the
pair decomposes into `(r,0)+(0,s)` in the opposite projection kernels.
Neither identity needs either original map to be onto.

For `b=(a,0) ∈ ker(qS)`, the pullback condition implies `f(a)=0`.
Multiplication by `b` kills every element of `ker(qR)`, giving the
localized projection's injectivity criterion with exponent **one**.
For every `r ∈ R`, the *actual numerator* `(a*r,0)` belongs to `P` and
has first projection `qR(b)^1*r`; this gives the corresponding
surjectivity criterion with exponent **one**, not an assumption that
`qR` is onto. `awayMap_fst_bijective` states the resulting bijectivity
of `Localization.awayMap qR b`; `awayMap_snd_bijective` exchanges the
coordinates. These arguments include `b=0` and zero localizations.

For each such `b`, mathlib's `SpecMapRestrictBasicOpenIso` identifies the
restriction of the actual projection-induced arrow over the basic open
`D_P(b)` with the spectrum of that localized ring map. Bijectivity above
makes the chart arrow an isomorphism. Its source chart lies in `U(f)`:
omitting `qR(b)=a ∈ ker f` prevents the source prime from containing
all of `ker f`. Every point of `U(f)` has a witness `a ∈ ker f` outside
its prime and hence a chart of this form. On a common chart, equality
of the image points forces equality of source points; the chart
isomorphisms and this injectivity give `isOpenImmersion_fstOpenMap`.
The argument for `isOpenImmersion_sndOpenMap` is symmetric. Both are
registered as `IsOpenImmersion` instances for the restricted arrows.

## Exact ranges and usage

The *opposite* projection kernels determine the target opens:

```text
fstTarget f g = U(qS) = Spec P \ V(ker qS)
sndTarget f g = U(qR) = Spec P \ V(ker qR)
commonTarget f g = U(h) = Spec P \ V(ker h).
```

`fstTarget_inf_sndTarget` proves their intersection is empty, and
`fstTarget_sup_sndTarget` proves their union is `commonTarget f g`.
`range_fstOpenMap` and `range_sndOpenMap` identify these opens with
the **exact set-theoretic ranges** of the respective restricted arrows.
For the reverse range inclusion, a target prime in `U(qS)` omits some
`b ∈ ker(qS)`; the isomorphism on `D_P(b)` supplies a preimage in
`U(f)`. `disjoint_ranges` and `union_ranges` restate the intersection
and union identities for those actual arrow ranges.

For example, the focused [direct-import client](../Test/PullbackOpenImmersionClient.lean)
uses the module without the aggregate import:

```lean
import SchemeProperties.PullbackOpenImmersion

open AlgebraicGeometry
open AlgebraicGeometry.PullbackOpenImmersion

universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

example (f : R →+* T) (g : S →+* T) :
    IsOpenImmersion (fstOpenMap f g) ∧ IsOpenImmersion (sndOpenMap f g) :=
  ⟨isOpenImmersion_fstOpenMap f g, isOpenImmersion_sndOpenMap f g⟩

example (f : R →+* T) (g : S →+* T) :
    Set.range (fstOpenMap f g) ∪ Set.range (sndOpenMap f g) =
      (kernelComplement (toBase f g) : Set (Spec (.of (f.pullback g)))) :=
  union_ranges f g
```

Both opens may be empty, including degenerate/zero-ring cases; neither
is asserted to be a nonempty connected component. No equality between
`V(ker qR)` or `V(ker qS)` and the range of an **unrestricted** Spec map
is used or claimed without additional hypotheses. The module establishes
no immersion of the total `Spec R`/`Spec S` arrows, no source-specific
sheaf-section or localization theorem, no category equivalence, and no
selected-source correspondence or coverage.

## Reproduction

The [toolchain](../lean-toolchain), [Lake configuration](../lakefile.toml)
and [exact dependency manifest](../lake-manifest.json) pin Lean, mathlib and
the two official Scheme Properties dependencies. With authorized access to
the private dependency repositories and an installed `elan`, fetch the
matching precompiled mathlib cache **before** any build (and again after
changing pins or replacing `.lake`):

```sh
lake exe cache get
lake --wfail build SchemeProperties SchemePropertiesTest SchemePropertiesExamples
```

For original-expression credit, see [CREDITS.md](CREDITS.md); no source
research repository is needed to use this mathematical API.
