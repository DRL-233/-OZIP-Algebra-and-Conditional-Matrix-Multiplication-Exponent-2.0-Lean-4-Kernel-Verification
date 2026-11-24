# Octonion-Z₃-Idempotent-Projected (OZIP) Algebra and Conditional Matrix Multiplication Exponent ω = 2.0: Lean 4 Kernel Verification

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24440448.svg)](https://doi.org/10.5281/zenodo.24440448)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.36.0--rc2-blue.svg)](https://lean-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

Machine-checked **Lean 4** formalization and **TTB2** runtime verification of the 54-dimensional **Octonion-$\mathbb{Z}_3$-Idempotent-Projected (OZIP)** algebra, its exact rational idempotent $\phi$-Molniya projector $P_M = \frac{1}{5}Q_M$ ($\kappa = 1.0$), explicit $N=1$ ($\langle 3, 3, 2 \rangle$) and $N=2$ ($4 \times \langle 9, 9, 4 \rangle$) tensor decompositions, universal inductive $N$-fold spoke decoupling for all $N \in \mathbb{N}$, and the $\mathbb{Z}_3$ cyclic triality symmetrization framework addressing the **57-year matrix multiplication exponent frontier ($\omega = 2.0$, 1969–2026)**.

- **Permanent Zenodo / EOSC Archive:** https://doi.org/10.5281/zenodo.24440448
- **Author:** Matthias Asare-Darko (Darkon Research Laboratory, Ghana)
- **Kernel Audit:** Zero `sorry`s, zero `native_decide`, zero custom axioms (`#print axioms` depends solely on Lean 4's standard foundational axioms: `[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`).

---

## Executive Overview: Addressing the 57-Year Matrix Multiplication Frontier (1969–2026)

Since Volker Strassen's 1969 breakthrough ($\omega \approx 2.8074$), reducing the asymptotic matrix multiplication exponent $\omega$ toward its theoretical floor $\omega = 2.0$ has stood as a **57-year open frontier** in algebraic complexity theory, constrained by two structural barriers:
1. **Numerical Catastrophe in Border-Rank Algorithms:** Classical laser-method and border-rank constructions rely on singular $\epsilon \to 0$ degenerations whose condition numbers diverge ($\kappa \sim \epsilon^{-1}$), destroying IEEE-754 floating-point accuracy in practical computation.
2. **Sub-Multiplicative Entanglement Loss Across Kronecker Powers:** High-order tensor powers $\mathcal{T}^{\otimes N}$ suffer cross-channel collisions that prevent linear block-count scaling.

**OZIP (`Octonion-Z3-Idempotent-Projected` Algebra)** replaces singular $\epsilon \to 0$ approximations with an **exact rational idempotent projector** $P_M = \frac{1}{5}Q_M$ ($P_M^2 = P_M$, unit condition number $\kappa = 1.0$) acting on a 54-dimensional $\mathbb{Z}_3$-graded non-associative octonionic algebra (`BBGT-9PT-V1`).

---

## Quickstart & Reproducibility

### 1. Standard Terminal (Linux / macOS / WSL / Codespaces)
Requires [elan / Lean 4](https://leanprover-community.github.io/get_started.html) (`v4.36.0-rc2`), `g++` (with `-mavx2` support for the C++ hypergraph search), and Python 3.10+ (`numpy`):

```bash
git clone "[https://github.com/DRL-233/OZIP-Algebra-and-Conditional-Matrix-Multiplication-Exponent-2.0-Lean-4-Kernel-Verification.git](https://github.com/DRL-233/OZIP-Algebra-and-Conditional-Matrix-Multiplication-Exponent-2.0-Lean-4-Kernel-Verification.git)"
cd OZIP-Algebra-and-Conditional-Matrix-Multiplication-Exponent-2.0-Lean-4-Kernel-Verification
lake exe cache get
lake build
python3 ozip_ttb2_accelerator.py
