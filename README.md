# Structured coordinate systems in Lᵖ(ℝ)

This repository contains a Lean 4 formalization of the main results of the paper [*Structured coordinate systems in Lᵖ(ℝ)*](https://arxiv.org/abs/2610.18709) by Daniel Freeman, Lukas Liehr and Mitchell A. Taylor. The Lean project formalizes Theorems 1.1, 1.3 and 1.4 of this paper, which read as follows.

**Theorem 1.1.** Let $1\leq p<\infty$ and $\varepsilon>0$. There is a non-negative Schauder basis $(f_n)$ of $L^p(\mathbb{R})$ with basis constant $K((f_n))<1+\varepsilon$. Moreover, no non-negative Schauder basis $(g_n)$ of $L^p(\mathbb{R})$ has $K((g_n))=1$.

**Theorem 1.3.** Let $2\leq p<\infty$. Then there exist a nonzero real-valued function $f\in L^p(\mathbb{R})$ and a sequence of real numbers $(\lambda_n)$ such that $(T_{\lambda_n}f)$ is a Schauder basis of $L^p(\mathbb{R})$ over either scalar field.

**Theorem 1.4.** The Schauder basis of translates $(T_{\lambda_n}f)$ in Theorem 1.3 can be chosen with the following additional regularity and structural properties.

(i) If $p=2$, then for every $\varepsilon>0$, the function $f$ and the sequence $(\lambda_n)$ can be chosen such that $f$ extends to an entire function that is real-valued on $\mathbb{R}$ and the basis constant satisfies $K((T_{\lambda_n}f))<1+\varepsilon$.

(ii) If $p>2$ and $S\subset\mathbb{R}$ is unbounded, then there exists a sequence $(\lambda_n)\subset S$ and a non-negative function $f\in L^p(\mathbb{R})$ extending to an entire function such that $(T_{\lambda_n}f)$ is a Schauder basis of $L^p(\mathbb{R})$.

Here, $T_\lambda f=f(\cdot-\lambda)$ is the translation of $f$ by $\lambda$. A basis is non-negative if each of its elements is non-negative almost everywhere, and the basis constant $K$ is the supremum of the norms of the partial sum projections.

## Lean entry points

- [Showcase.lean](Showcase.lean): the statements of the theorems above in Lean, together with the definitions needed to read them. It imports only Mathlib and uses `sorry` in place of the proofs.
- [Showcase_WithProofs.lean](Showcase_WithProofs.lean): the same definitions and statements, with every `sorry` replaced by a proof.
- [Lean_Code/](Lean_Code): the Lean library that contains the proofs.
- [comparator.json](comparator.json): Comparator configuration pairing the two Showcase files.

The declarations in `Showcase.lean` correspond to the paper as follows.

| Paper | `Showcase.lean` |
| --- | --- |
| Theorem 1.1 | `nonneg_basis` |
| Theorem 1.3 | `translate_basis` |
| Theorem 1.4 (i) | `translate_basis_L2` |
| Theorem 1.4 (ii) | `translate_basis_nonneg` |

The statements use the structure `SchauderBasis` of Mathlib. This notion agrees with the definition by unique norm-convergent expansions, which is proved in [Lean_Code/Basis/UniqueExpansion.lean](Lean_Code/Basis/UniqueExpansion.lean). The proofs depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Repository layout

- `Lean_Code/Main/`: assembly of the theorems from the parts below
- `Lean_Code/Basis/`: general facts about Schauder bases
- `Lean_Code/PositiveBiorthogonal/`: non-negative bases of $L^p(\mathbb{R})$ for $1<p<\infty$
- `Lean_Code/PositiveL1/`: non-negative bases of $L^1(\mathbb{R})$
- `Lean_Code/SchauderTranslates/`: bases of translates in $L^2(\mathbb{R})$, and in the subfolder `Lp/` tools for $L^p(\mathbb{R})$ used for $p>2$
- `Lean_Code/PositiveTranslates/`: bases of translates in $L^p(\mathbb{R})$ for $p>2$

## Build

The project uses Lean `v4.33.0` and the version of Mathlib pinned in `lake-manifest.json`. To compile it, run the following commands in the root of the repository.

```bash
lake exe cache get
lake build
```

The first command downloads the compiled Mathlib library. The second command builds `Lean_Code` and both Showcase files. For `Showcase.lean` it reports four uses of `sorry`, which stand for the omitted proofs.
