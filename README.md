# The Wooden Idol — Turing Chamber × All Twelve

A Lean 4 construction of the Wooden Idol Turing Chamber with all twelve B-constraints certified together on one final system.

## The machine

The repository contains the complete formal machine:

- the 107-module Foundation Stone Turing Chamber;
- the Chamber interface;
- the B1–B12 coupling layer;
- the B5 proof layer;
- a genuine arithmetic B5 instance using IΣ₁ derivability and Foundation's formal Gödel-II theorem;
- one top-level all-twelve certificate.

## Final certificate

```lean
WoodenIdolTuringChamberFinal.wooden_idol_turing_chamber_all_twelve
```

This theorem certifies B1 through B12 simultaneously on the final coupled system, together with the productive proof-system condition.

## Pinned environment

- Lean: `leanprover/lean4:v4.35.0-rc2`
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`
- Foundation: `e72cfe981aa65166f37fa4e2584f4806bc48d72f`

## Build

```bash
cd B5Foundation
lake update
lake exe cache get
lake build TuringChamber_Coupled_AllTwelve
```

The GitHub Actions certification rejects Lean errors, `sorryAx`, and declarations using `sorry`.

## Formal scope

B5 is supplied by an explicitly attached arithmetic proof sector. The construction does not claim that the Chamber dynamics themselves derive Gödel II. The certificate makes no claim about the Riemann Hypothesis, P versus NP, consciousness, or physical law.
