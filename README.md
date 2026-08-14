# A Lean proof of the scalar-matrix Poisson n-Lie conjecture

This repository formalizes the scalar-matrix Poisson `n`-Lie conjecture from
[arXiv:2605.01785](https://arxiv.org/abs/2605.01785).  It proves the exact general target proposed
in [Formal Conjectures PR #4893](https://github.com/google-deepmind/formal-conjectures/pull/4893),
and first proves a stronger theorem with no lower-bound hypotheses on `n` or `m`.

The Formal Conjectures PR is not yet merged.  Accordingly, the files here reproduce its exact
definitions and target namespace using mathlib only; this repository does **not** clone or depend
on the full Formal Conjectures repository.

**Try it in Lean4Web:**
[open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fpoisson-n-lie-scalar-matrix%2Frefs%2Fheads%2Fmain%2Flean4web%2FPoissonNLieScalarMatrixLean4Web.lean)

## The two final theorems

The unrestricted theorem is stated first:

```lean
theorem poissonNLie_of_scalarMatrix_general (n m : ℕ)
    {F : Type*} [Field F]
    {A : Type*} [CommRing A] [Algebra F A]
    (d : Fin (n + m) → Derivation F A A)
    (hcomm : ∀ i j : Fin (n + m), ∀ a : A, d i (d j a) = d j (d i a))
    (M : Matrix (Fin (n + m)) (Fin m) F) :
    IsPoissonNLie (nLieBracket d M)
```

The exact target from PR #4893 is then an immediate corollary:

```lean
theorem poissonNLie_of_scalarMatrix (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (hm : 1 ≤ m)
    {F : Type*} [Field F]
    {A : Type*} [CommRing A] [Algebra F A]
    (d : Fin (n + m) → Derivation F A A)
    (hcomm : ∀ i j : Fin (n + m), ∀ a : A, d i (d j a) = d j (d i a))
    (M : Matrix (Fin (n + m)) (Fin m) F) :
    IsPoissonNLie (nLieBracket d M) := by
  exact poissonNLie_of_scalarMatrix_general n m d hcomm M
```

Thus the hypotheses `hn` and `hm` are not needed by the proof.

## Mathematical explanation (AI generated)

For commuting derivations `d₁, …, dₙ₊ₘ` and a scalar matrix `M`, the bracket is

```text
[x₁, …, xₙ] = det [ dᵢ(xⱼ) | M ].
```

Alternation follows by swapping derivative columns.  The Leibniz rule follows from the Leibniz
rule for each derivation and linearity of the determinant in one column.

For the Filippov identity, fix all but one Hamiltonian argument.  Cramer's rule expresses the
resulting Hamiltonian derivation as

```text
H(a) = Σᵣ cᵣ dᵣ(a),
```

where `cᵣ` is an entry of the adjugate matrix.  The proof establishes the Piola-type identity

```text
Σᵣ dᵣ(cᵣ) = 0.
```

After differentiating the determinant, the mixed second-derivative terms cancel because the
derivations commute while the corresponding two-column determinants are antisymmetric.  Terms
coming from the constant scalar columns vanish using
`adjugate X * X = det X • 1`.  The remaining trace identity shows that `H` acts as a derivation of
the bracket, which is precisely the Filippov identity.

The argument works over an arbitrary field `F` and an arbitrary commutative `F`-algebra `A`; no
characteristic-zero assumption is used.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.27.0` | Reproducible Lake project, pinned to mathlib commit `a3a10db0...` |
| `lean4web/` | `v4.27.0` | Standalone mathlib-only proof for Lean4Web |

Each directory contains one proof file, `lakefile.toml`, `lean-toolchain`, and a pinned
`lake-manifest.json`.

## Verification

Reproducible project:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone Lean4Web project:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

Both proof files finish with the same audit, in the order "unrestricted theorem, exact FC target":

```lean
#check Arxiv.«2605.01785».poissonNLie_of_scalarMatrix_general
#print axioms Arxiv.«2605.01785».poissonNLie_of_scalarMatrix_general

#check Arxiv.«2605.01785».poissonNLie_of_scalarMatrix
#print axioms Arxiv.«2605.01785».poissonNLie_of_scalarMatrix
```

Both axiom printouts contain only Lean's standard foundations:

```text
[propext, Classical.choice, Quot.sound]
```

The checked sources contain no `sorry`, `admit`, custom `axiom`, `native_decide`, or unsafe
theorem.

## Status boundary

What is solved here:

```text
The scalar-matrix bracket of pairwise commuting derivations is Poisson n-Lie.
This includes the exact general theorem proposed in Formal Conjectures PR #4893.
```

What remains open:

```text
Integrate the proof into Formal Conjectures, attach a fixed formal_proof permalink,
review the status change from research open to research solved, and merge the PR.
```

No claim is made here about variants in which the final matrix columns are arbitrary elements of
`A` rather than scalars from `F`.

## Sources

- [Formal Conjectures PR #4893](https://github.com/google-deepmind/formal-conjectures/pull/4893)
- [PR #4893 changes](https://github.com/google-deepmind/formal-conjectures/pull/4893/changes)
- [Cao–Normatov–Omirov, arXiv:2605.01785](https://arxiv.org/abs/2605.01785)
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-361-asymptotic)

## AI usage disclosure

This formalization was developed with assistance from OpenAI Codex, using GPT-5.6 sol.
