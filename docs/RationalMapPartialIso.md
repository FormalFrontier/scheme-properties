# Exact rational inverses and partial isomorphisms

Import `SchemeProperties.RationalMapPartialIso` directly. The public
results live in `AlgebraicGeometry.Scheme.RationalMap` and
`AlgebraicGeometry.Scheme.PartialIso`. They require only mathlib's native
`Birational` and `Composition` modules, not a project-specific rational-map
category. A direct-import client is
`Test.RationalMapPartialIsoClient`; its declarations are
private.

## API and conventions

For same-universe integral schemes `X` and `Y`, independently supplied dominant
native quotients `forward : X ⤏ Y` and `reverse : Y ⤏ X`, and **both** native
equations

```lean
forward.comp reverse = Scheme.RationalMap.id X
reverse.comp forward = Scheme.RationalMap.id Y
```

`RationalMap.exists_partialIso_of_inverse` gives `partialIso : X.PartialIso Y`
with `partialIso.toRationalMap = forward` **and**
`partialIso.symm.toRationalMap = reverse`. `comp` is source-first: the first
equation is `reverse ∘ forward = id_X`. The exact quotients matter; the
conclusion is stronger than the existence of some unrelated birational witness.

`RationalMap.exists_partialIso_of_inverse_over` additionally accepts any
scheme `S`, independently chosen total maps `sX : X ⟶ S` and `sY : Y ⟶ S`,
and only the **one** base equation

```lean
forward.compHom sY = sX.toRationalMap
```

It returns those same two exact readbacks together with the literal equation
`partialIso.IsOver sX sY`, namely
`partialIso.iso.hom ≫ partialIso.target.ι ≫ sY =
 partialIso.source.ι ≫ sX`. The inverse's quotient base equation follows from
the other inverse law and associativity; it is not an extra hypothesis. The
same-carrier case permits two independently chosen maps `X ⟶ S`, conditional
only on the displayed base equation. There is **no** assumption of local finite
type, separatedness, integrality of `S`, or dominance of either total map.

Conversely, every `partialIso : X.PartialIso Y` has a dominant exact forward
quotient by the instance `PartialIso.toRationalMap_isDominant`; applying it to
`partialIso.symm` supplies the reverse dominance. For integral `X` and `Y`,
`PartialIso.toRationalMap_comp_symm` and
`PartialIso.symm_toRationalMap_comp` prove the two native inverse identities.
Without extra integrality assumptions, literal `partialIso.IsOver sX sY`
implies the forward and reverse quotient base equations via
`PartialIso.toRationalMap_compHom_of_isOver` and
`PartialIso.symm_toRationalMap_compHom_of_isOver`.

## Proof method and limits

Native `RationalMap.IsOver` gives an *existential* over-base partial-map
representative; an arbitrary representative need not preserve the base map.
Choose appropriate forward and reverse representatives, transfer quotient
dominance, and turn both quotient inverse equations into actual scheme-morphism
equalities on dense opens `A` and `B`. Shrink by the correctly typed inverse
images on each representative's domain: intersect `A` with the source-domain
image of the forward inverse image of `B`, and dually intersect `B` with the
reverse inverse image of `A`. Dominant composition proves these opens dense.
The two morphism equations put each restricted map's range in the other new
open. `IsOpenImmersion.lift` factors genuine scheme morphisms, and cancellation
of the mono open inclusions proves the two inverse **morphism** laws. Native
restriction preserves each exact quotient, while the over-base representative's
literal equality restricts to the resulting partial isomorphism. The converse
uses the iso inverse laws on the actual composition domain, not pointwise
agreement alone. No maximal-domain gluing, function-field inverse criterion,
categorical equivalence, reducible extension, or total isomorphism is asserted.

## Reproduction and provenance

The focused producer uses mathlib's native birational and composition APIs.
With authorized access to the pinned dependencies, fetch the matching mathlib
cache successfully from this repository before building:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build SchemeProperties.RationalMapPartialIso
lake build Test.RationalMapPartialIsoClient
```

The construction adapts native quotient and representative contracts by
Andrew Yang and the composition-domain expression by Justus Springer; his
authentic individual notice remains in the Lean source. See
[Credits](CREDITS.md) for its distinct original project proofs.
