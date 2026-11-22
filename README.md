# Octonion-$\mathbb{Z}_3$-Idempotent-Projected (OZIP) Algebra & Conditional $\omega = 2.0$ Formalization

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24440448.svg)](https://doi.org/10.5281/zenodo.24440448)
[![Lean 4](https://img.shields.io/badge/Lean%204-v4.36.0--rc2-blue.svg)](https://lean-lang.org/)
[![Build Status](https://img.shields.io/badge/lake%20build-2556%2F2556%20passing-brightgreen.svg)](#reproducing-the-lean-4-kernel-verification)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Machine-checked **Lean 4 + Mathlib** formalization (`OZIPVerification.lean`) accompanying the manuscript on the 54-dimensional **Octonion-$\mathbb{Z}_3$-Idempotent-Projected (OZIP)** algebra built over the 9-dimensional non-associative `BBGT-9PT-V1` basis, cyclic $\mathbb{Z}_3$ triality, and the sector-differentiated Molniya idempotent projector $P_M$.

- **Permanent Zenodo / EOSC Archive:** [https://doi.org/10.5281/zenodo.24440448](https://doi.org/10.5281/zenodo.24440448)
- **Institution:** Darkon Research Laboratory (DRL), Ghana

---

## Summary of Kernel-Verified Theorems (`OZIPVerification.lean`)

All definitions and theorems compile cleanly inside Lean 4's minimal trusted kernel (`decide`, zero `native_decide`, **zero `sorry`s**, **zero custom axioms**, and **zero warnings**):

1. **Complete `BBGT-9PT-V1` Multiplication Table (`zipMul`):**
   - Formalizes all $9 \times 9 = 81$ basis products over $\{e_{-1}, e_0, e_1, e_2, e_3, e_4, e_5, e_6, e_7\}$ parameterized by associator coupling $A$.
   - Proves `e1_mul_e5_eq_e6_plus_Ae4` ($e_1 \cdot e_5 = e_6 + A e_4$) and `e4_annihilates_six_interior_directions` ($e_4 \cdot b = 0$ for all $b \in \{e_0, e_1, e_2, e_3, e_5, e_6\}$).
2. **Exact Support Accounting (`albert_support_accounting`):**
   - Proves that the $27 \times 27 \times 27$ unprojected split-Albert comparison tensor partitions its $19,683$ cubic channels into **$462$ nonzero entries** ($6 + 72 + 384$) and **$19,221$ structural zeros**.
3. **Explicit $54 \times 54$ Idempotent Molniya Projector (`P_M_idempotent`):**
   - Defines the rational sector-differentiated projector $P_M = \frac{1}{5} Q_M \in \mathbb{Q}^{54 \times 54}$, proves 2-spoke hub collapse (`Q_M_row_two_spoke`), and establishes $Q_M^2 = 5 Q_M$ and $P_M^2 = P_M$.
4. **Exact $\langle 3, 3, 2 \rangle$ Tensor Restriction Witness (`ozip54_restricts_to_18_matmul332`):**
   - Constructs explicit rational projection matrices $X \in \mathbb{Q}^{54 \times 9}$, $Y \in \mathbb{Q}^{54 \times 6}$, and $Z \in \mathbb{Q}^{54 \times 6}$.
   - Proves `X_int_in_image_Q_M`, `Y_int_in_image_Q_M`, and `Z_int_in_image_Q_M` ($P_M X = X$, $P_M Y = Y$, $P_M Z = Z$) alongside exact 2-spoke Molniya hub sparsity (`X_int_sparse_support`, `Y_int_sparse_support`, `Z_int_sparse_support`).
   - Verifies across all $9 \times 6 \times 6 = 324$ entries that the projected $54^3$ OZIP structure tensor restricts identically to $18 \cdot \langle 3, 3, 2 \rangle$.
5. **Conditional Transitive Deduction of $\omega = 2$ (`conditional_exact_omega_two`):**
   - Formally proves that under Conjecture 5.1 (asymptotic Molniya triality growth rate $\gamma_M = \frac{3}{2}$, giving $t \le \frac{2}{3}$), the detecting-character upper bound $\omega \le 3t$, and the information-theoretic lower bound $\omega \ge 2$, the matrix multiplication exponent satisfies $\omega = 2$.

> **Scope Clarification:** The algebraic identities, projector idempotence, exact $\langle 3, 3, 2 \rangle$ restriction witness, and conditional logical implication are unconditionally proved in Lean 4. Sustaining the asymptotic triality growth rate $\gamma_M = 3/2$ across arbitrarily high Kronecker tensor powers $\mathcal{T}_{\text{OZIP}}^{\otimes N}$ ($N \to \infty$) remains the open hypothesis stated as Conjecture 5.1.

---

## Reproducing the Lean 4 Kernel Verification

```bash
cd OZIPVerification
lake build
```

Expected output (~39.5 s):
```text
✔ [2556/2556] Built OZIPVerification
Build completed successfully (2556 jobs).
```

## Citation

```bibtex
@software{asare_darko_2026_ozip_lean4,
  author       = {Asare-Darko, Matthias},
  title        = {{Octonion-Z3-Idempotent-Projected (OZIP) Algebra and Conditional Matrix Multiplication Exponent ω = 2.0: Lean 4 Kernel Verification}},
  month        = nov,
  year         = 2026,
  publisher    = {Zenodo},
  version      = {v1.0.0},
  doi          = {10.5281/zenodo.24440448},
  url          = {https://doi.org/10.5281/zenodo.24440448}
}
```
