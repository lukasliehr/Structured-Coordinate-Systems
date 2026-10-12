# Structured coordinate systems in Lᵖ(ℝ)

This repository contains a Lean 4 formalization of the main results of the paper
*Structured coordinate systems in Lᵖ(ℝ)* by Daniel Freeman, Lukas Liehr and
Mitchell A. Taylor.

## Lean-verified statements

The following five statements are numbered in the order in which they appear in both the paper and in
[Showcase.lean](Showcase.lean). Their proofs are in
[Showcase_WithProofs.lean](Showcase_WithProofs.lean). In the following $L^p$ denotes the Banach space of p-integrable real or complex valued functions on the real line.

**Theorem 1 (Non-negative bases).** Let $1\le p<\infty$ and $\varepsilon>0$. There is a non-negative Schauder basis
$(f_n)$ of $L^p$ with
$K((f_n))<1+\varepsilon$. Moreover, no non-negative Schauder basis of
$L^p$ has basis constant $1$.

**Theorem 2 (Bases of translates).** Let $2\le p<\infty$. There are a real-valued
function $f\in L^p$ and an
ordered sequence of real numbers $(\lambda_n)$ such that $(T_{\lambda_n}f)$ is a
Schauder basis of $L^p$.

**Theorem 3 (Entire generators).** Let $2\le p<\infty$. There are a real-valued
function $f\in L^p$ extending to an entire function, and an ordered sequence of real numbers
$(\lambda_n)$ such that $(T_{\lambda_n}f)$ is a Schauder basis of
$L^p$.

**Theorem 4 (Almost monotone bases of translates in $L^2$).** Let $\varepsilon>0$.
There are a real-valued function $f\in L^2$ and an ordered sequence of real numbers
$(\lambda_n)$ such that $(T_{\lambda_n}f)$ is a Schauder basis of $L^2$ with
$K((T_{\lambda_n}f))<1+\varepsilon$.

**Theorem 5 (Non-negative entire generators with prescribed parameters).** Let
$2<p<\infty$ and let $S\subseteq\mathbb{R}$ be unbounded. There are a non-negative
function $f\in L^p$ extending to an entire function, and an ordered sequence of
pairwise distinct real numbers $(\lambda_n)$ in $S$ such that $(T_{\lambda_n}f)$
is a Schauder basis of $L^p$.

The correspondence with the Lean declarations is:

| Statement | Declaration in the namespace `SchauderLp` |
| --- | --- |
| Theorem 1 | `nonneg_basis` |
| Theorem 2 | `translate_basis` |
| Theorem 3 | `translate_basis_entire` |
| Theorem 4 | `translate_basis_almost_monotone` |
| Theorem 5 | `translate_basis_nonneg` |

The paper also obtains the entire extension in Theorem 3 and the bound in Theorem 4
simultaneously when $p=2$. This stronger conclusion is proved by
`StructuredBases.translate_basis_L2` in
[Lean_Code/Main/TranslatesL2.lean](Lean_Code/Main/TranslatesL2.lean); the fourth
showcase statement records only the basis-constant conclusion.

## Lean entry points

- [Showcase.lean](Showcase.lean): the five statements in Lean, with all definitions
  needed to read them. It imports only Mathlib and uses `sorry` in place of the proofs.
  The statements use Mathlib's `SchauderBasis` and its basis constant
  `SchauderBasis.nnnormProjBound`.
- [Showcase_WithProofs.lean](Showcase_WithProofs.lean): the same definitions and
  statements, with proofs supplied by the internal library `Lean_Code`. The five theorems
  depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
- [comparator.json](comparator.json): Comparator configuration pairing the two files.
- [Lean_Code.lean](Lean_Code.lean): umbrella module of the internal library.

Mathlib's `SchauderBasis` records the basis vectors together with continuous coordinate
functionals. That this agrees with the definition by unique norm-convergent expansions is
proved in `Lean_Code/Basis/UniqueExpansion.lean`
(`StructuredBases.schauderBasis_iff_existsUnique_expansion`).

## Repository layout

- `Lean_Code/Main/`: assembly of the five theorems from the parts below.
- `Lean_Code/Basis/`: general facts about Schauder bases in Mathlib's sense (the finite
  prefix criterion, transport, small perturbations, passage from complex to real scalars,
  equivalence with unique expansions).
- `Lean_Code/PositiveBiorthogonal/`: non-negative bases of $L^p(\mathbb{R})$ for
  $1<p<\infty$.
- `Lean_Code/PositiveL1/`: non-negative bases of $L^1(\mathbb{R})$, and the proof that
  none of them is monotone.
- `Lean_Code/SchauderTranslates/`: the weighted exponential construction behind the
  translates in $L^2(\mathbb{R})$; the estimates giving basis constant $<1+\varepsilon$
  are in `Lean_Code/SchauderTranslates/Sharp/`.
- `Lean_Code/PositiveTranslates/`: translates of a non-negative entire generator for
  $p>2$.

## Build

The project uses Lean `v4.33.0` and a pinned Mathlib commit (see `lake-manifest.json`).

```bash
lake exe cache get
lake build
```

The default targets are `Lean_Code`, `Showcase` and `Showcase_WithProofs`. Building
`Showcase` reports five uses of `sorry`; these are the intended placeholders.
