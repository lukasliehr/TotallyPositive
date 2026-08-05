# Totally-Positive

This repository contains a Lean 4 formalization accompanying the paper
*Gabor Frames  of Totally Positive Functions: A Complete Characterization* by Jaume de Dios Pont, Karlheinz Gröchenig, Lukas Liehr, Irina Shafkulovska and Mitchell A. Taylor.
The following result is formalized in Lean.

**Theorem.** If $\alpha,\beta > 0$ satisfy $\alpha \cdot \beta < 1$ and if $g : \mathbb R \to \mathbb R$ is a continuous,
integrable, and totally positive function, then the Gabor system $\mathcal G(g,\alpha,\beta)$ is a frame for $L^2(\mathbb R)$.

## Lean entry points

- [Showcase.lean](Showcase.lean): a self-contained formulation of the main result in Lean, including the definition of a totally positive function and a Gabor system. It imports only Mathlib and uses `sorry` placeholders for
  proofs.
- [Showcase_WithProofs.lean](Showcase_WithProofs.lean): the sorry-free version
  with the identical statements as in [Showcase.lean](Showcase.lean). It imports the internal `LeanCode` library,
  where the statement is bridged to the assembled proof. The proof-backed result
  `Assembly.frameSetConjecture` is axiom-clean — `#print axioms` yields exactly
  `propext`, `Classical.choice`, `Quot.sound`.

## Repository layout

- `LeanCode/`: the internal Lean proof library. The seven proved ingredients of
  the argument are vendored under `LeanCode/Vendor/` and re-exported through the
  `LeanCode/Bridge_*.lean` files, so the library builds as a single self-contained
  package.

## Build

Use Lake from the repository root:

```bash
lake exe cache get
lake build Showcase
lake build Showcase_WithProofs
lake build
```

The default targets in `lakefile.toml` are `Showcase` and `Showcase_WithProofs`.
The internal library can also be built directly with:

```bash
lake build LeanCode
```
