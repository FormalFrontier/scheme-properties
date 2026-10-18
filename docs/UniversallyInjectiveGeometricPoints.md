# Universal injectivity and algebraically closed field-valued points

For any scheme morphism `f : X ⟶ Y`, universal injectivity is equivalent to
injectivity of

\[
\operatorname{Hom}(\operatorname{Spec} K,X)\longrightarrow
\operatorname{Hom}(\operatorname{Spec} K,Y),\qquad g\longmapsto f\circ g
\]

for every algebraically closed field `K`. In Lean's source-first order,
postcomposition is `g ≫ f`. No local finite type, reducedness, separatedness,
properness, flatness, affineness, smoothness, Noetherianity or dimension
assumption is part of the criterion.

The declaration
`AlgebraicGeometry.universallyInjective_iff_injective_geometricPoints` in
[`SchemeProperties.UniversallyInjectiveGeometricPoints`](../SchemeProperties/UniversallyInjectiveGeometricPoints.lean)
uses the existing `UniversallyInjective` class and ordinary morphisms from
`Spec (.of K)`, with `[Field K] [IsAlgClosed K]`. The schemes and test fields
share an arbitrary universe `u`, as in Mathlib's all-field characterization.
No additional geometric-point carrier or class is needed.

## Proof via field extensions

Mathlib's all-field criterion immediately gives the forward implication.
For the converse, let `K` be any field and extend it to `AlgebraicClosure K`,
in the same universe. The canonical map
`Spec (AlgebraicClosure K) → Spec K` is flat and surjective, hence an
epimorphism by `Flat.epi_of_flat_of_surjective`. If two `K`-valued points
have equal composites with `f`, precompose them with this map. Injectivity
over the algebraic closure identifies the precomposed arrows; epimorphism
cancellation then identifies the original arrows. Applying the all-field
criterion gives universal injectivity. Flatness is used only for the
field-extension map, not assumed of `f`.

## Nonvacuity and boundaries

* For any field `k`, the origin `Spec k → Spec k[t] = A¹_k` is a closed
  immersion, hence a monomorphism and universally injective. Its image
  omits the generic point, so this is neither an identity nor a surjection.
  The [private origin application](../SchemePropertiesTest/UniversallyInjectiveGeometricPoints.lean)
  obtains geometric-point injectivity from the criterion, using
  `Polynomial.evalRingHom 0` and Mathlib's closed-immersion provider.
* Every identity satisfies the criterion. So does the unique map from
  the empty scheme to any scheme: its base changes have empty source,
  and no field spectrum maps to the empty scheme.
* `Spec ℂ → Spec ℝ` is injective on underlying topological spaces, since
  both spectra are singletons. But its `ℂ`-valued points given by the
  identity and complex conjugation are distinct and have the same
  composite to `Spec ℝ`. Conjugation fixes the reals but sends `i` to
  `-i`. Thus underlying injectivity does not imply universal injectivity.
* The criterion does not characterize monomorphisms. For a field `k`,
  let `D = k[ε]/(ε²)`. Every map from `D` to a field kills `ε`, so
  `Spec D → Spec k` satisfies the criterion. The identity of `Spec D`
  and the endomorphism induced by `ε ↦ 0` are nevertheless distinct
  and have the same composite to `Spec k`. Field-valued points need
  not detect nilpotents.

## Existing characterizations and credit

Mathlib's `AlgebraicGeometry.tfae_universallyInjective`, by Andrew Yang and
Justus Springer, gives the all-field criterion, the purely inseparable
residue-field characterization, and the surjective-diagonal criterion
([Stacks Project, Tag 01S4](https://stacks.math.columbia.edu/tag/01S4)).
The distinction here is solely the algebraically closed field quantifier.

Mathlib's `AlgebraicGeometry.Flat.epi_of_flat_of_surjective`, from the
flat-morphism development by Christian Merten and Andrew Yang, supplies
the epimorphism API for flat surjective maps, including field-extension
spectra ([Tag 02VW](https://stacks.math.columbia.edu/tag/02VW)). Its use
for a field-extension spectrum imposes no flatness assumption on `f`.
The proof uses Mathlib's algebraic closure construction by Kenny Lau.
The origin application uses the closed-immersion API by Amelia Livingston,
Christian Merten and Jonas van der Schaaf. These APIs are used rather than
copied; upstream notices remain in Mathlib. The new proof and prose are
original Formal Frontier contributions under Apache-2.0, developed with AI
assistance.
