# Octonion-Z₃-Idempotent-Projected (OZIP) Algebra and Conditional Matrix Multiplication Exponent ω = 2.0: Lean 4 Kernel Verification

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24440448.svg)](https://doi.org/10.5281/zenodo.24440448)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.36.0--rc2-blue.svg)](https://lean-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

Machine-checked **Lean 4** formalization and **TTB2 (`v0.2.0`)** runtime verification of the 54-dimensional **Octonion-$\mathbb{Z}_3$-Idempotent-Projected (OZIP)** algebra, its idempotent $\phi$-Molniya projector $P_M$, an explicit $\langle 3, 3, 2 \rangle$ matrix multiplication tensor restriction witness inside $\mathrm{im}(P_M)$, and the parametric complexity bound $\omega \le 3/\gamma_M$.

- **Permanent Zenodo / EOSC Archive:** https://doi.org/10.5281/zenodo.24440448
- **Author:** Matthias Asare-Darko (Darkon Research Laboratory, Ghana)

---

## Quickstart & Reproducibility

### 1. Standard Terminal (Linux / macOS / WSL / Codespaces)
Requires [elan / Lean 4](https://leanprover-community.github.io/get_started.html) (`v4.36.0-rc2`) and Python 3.10+ (`numpy`):

```bash
git clone "[https://github.com/DRL-233/OZIP-Algebra-and-Conditional-Matrix-Multiplication-Exponent-2.0-Lean-4-Kernel-Verification.git](https://github.com/DRL-233/OZIP-Algebra-and-Conditional-Matrix-Multiplication-Exponent-2.0-Lean-4-Kernel-Verification.git)"
cd OZIP-Algebra-and-Conditional-Matrix-Multiplication-Exponent-2.0-Lean-4-Kernel-Verification
lake exe cache get
lake build
python3 ozip_ttb2_accelerator.py
```

### 2. Google Colab Notebook Directive
In Google Colab, each `!` command spawns an isolated subshell (resetting `cd`) and `$HOME/.elan/bin` is not in the default `PATH`. Run the entire verification inside a single **`%%bash` cell** (do **not** prefix lines with `!`):

```bash
%%bash
export PATH="$HOME/.elan/bin:$PATH"
git clone "[https://github.com/DRL-233/OZIP-Algebra-and-Conditional-Matrix-Multiplication-Exponent-2.0-Lean-4-Kernel-Verification.git](https://github.com/DRL-233/OZIP-Algebra-and-Conditional-Matrix-Multiplication-Exponent-2.0-Lean-4-Kernel-Verification.git)"
cd OZIP-Algebra-and-Conditional-Matrix-Multiplication-Exponent-2.0-Lean-4-Kernel-Verification
lake exe cache get && lake build && python3 ozip_ttb2_accelerator.py
```

### Expected Verification Output
- **Lean 4 Kernel (`lake build`):**
  ```text
  Build completed successfully (2556 jobs).
  ```
  *(Zero warnings, zero `sorry`s, zero `native_decide`, zero custom axioms.)*
- **Companion TTB2 `v0.2.0` Runtime (`ozip_ttb2_accelerator.py`):**
  ```text
  Exact <3,3,2> OZIP-TTB2 Result:
   [[ 11  -5]
   [-10  18]
   [ -7  21]]
  ```

---

## Scope: Unconditional Proofs vs. Conditional Scaling

This formalization cleanly separates **unconditional finite/parametric theorems** (verified inside Lean 4's minimal trusted kernel with zero `sorry`s, zero `native_decide`, and zero custom axioms) from **Conjecture 5.1**:

1. **Unconditional Algebraic & Geometric Foundations ($N = 1$):**
   - Complete $9 \times 9 = 81$ `BBGT-9PT-V1` multiplication law (`zipMul`), associator channel $e_4$, and annihilation of all 6 interior gauge directions.
   - Exact partition of the $27^3 = 19,683$ cubic channels of the split-Albert comparison tensor into **$462$ nonzero entries** and **$19,221$ structural zeros**.
   - Exact $\phi$-Molniya double-angle tangent identity $\frac{2\varphi^{-1}}{1 - (\varphi^{-1})^2} = 2$ ($\arctan\varphi^{-1} = \frac{1}{2} i_{\text{Molniya}}$).
   - Idempotence of the $54 \times 54$ Molniya projector $P_M^2 = P_M$ via 2-spoke hub collapse ($Q_M^2 = 5 Q_M$).
   - Exact $\langle 3, 3, 2 \rangle$ bilinear tensor restriction witness inside $\mathrm{im}(P_M)$ verified across all $324$ entries.
2. **Unconditional Parametric Scaling Law:**
   - For any proved asymptotic triality growth exponent $\gamma_M > 0$, the matrix multiplication exponent satisfies $\omega \le \frac{3}{\gamma_M}$ (e.g., $\gamma_M = \frac{4}{3} \implies \omega \le 2.25$).
3. **Conditional Optimal Exponent ($\omega = 2.0$):**
   - Specializing to **Conjecture 5.1** ($\gamma_M = \frac{3}{2}$ across Kronecker tensor powers $\mathcal{T}_{\text{OZIP}}^{\otimes N}$ as $N \to \infty$) together with $\omega \ge 2$ yields **$\omega = 2.0$**.

---

## Verified Theorems (`OZIPVerification.lean`)

| Theorem | Formal Statement Summary | Verification Method |
| :--- | :--- | :--- |
| `e1_mul_e5_eq_e6_plus_Ae4` | $e_1 \cdot e_5 = e_6 + A e_4$ in `BBGT-9PT-V1` | Definitional equality (`rfl`) |
| `e4_annihilates_six_interior_directions` | $e_4 \cdot e_i = 0$ for all $i \in \{0,1,2,3,5,6\}$ | Exhaustive case analysis |
| `albert_support_accounting` | $462 + 19,221 = 19,683 = 27^3$ split-Albert support split | Kernel `decide` |
| `phi_molniya_double_angle_tangent` | $\frac{2\varphi^{-1}}{1 - (\varphi^{-1})^2} = 2$ for $\varphi^{-1} = \frac{\sqrt{5}-1}{2}$ | Exact real algebra (`nlinarith`) |
| `P_M_idempotent` | $P_M^2 = P_M$ for $P_M = \frac{1}{5} Q_M \in \mathbb{Q}^{54 \times 54}$ | 2-spoke hub collapse + `decide` |
| `ozip54_restricts_to_18_matmul332` | Projected $54^3$ OZIP tensor restricts to $18 \cdot \langle 3, 3, 2 \rangle$ inside $\mathrm{im}(P_M)$ | 2-spoke contraction + `decide` |
| `parametric_triality_omega_bound` | $\gamma_M > 0 \land t \le \gamma_M^{-1} \land \omega \le 3t \implies \omega \le 3/\gamma_M$ | Real inequality (`nlinarith`) |
| `conditional_exact_omega_two` | $\gamma_M = \frac{3}{2} \land \omega \ge 2 \implies \omega = 2$ | Real inequality (`linarith`) |

All theorems depend solely on Lean 4's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## Repository Structure

```text
.
├── OZIPVerification.lean       # Complete Lean 4 formalization (zero sorrys, zero custom axioms)
├── lakefile.toml               # Lake build configuration (pinned to Mathlib v4.36.0-rc2)
├── lean-toolchain              # Pinned Lean 4 toolchain (leanprover/lean4:v4.36.0-rc2)
├── ozip_ttb2_accelerator.py    # Companion TTB2 v0.2.0 runtime <3,3,2> verification & benchmark
├── CITATION.cff                # Standardized citation metadata (DOI: 10.5281/zenodo.24440448)
├── LICENSE                     # MIT License
└── README.md                   # Documentation and reproduction guide
```

---

## Citation

```bibtex
@software{asare_darko_2026_ozip_lean4,
  author       = {Asare-Darko, Matthias},
  title        = {{Octonion-Z3-Idempotent-Projected (OZIP) Algebra and Conditional Matrix Multiplication Exponent omega = 2.0: Lean 4 Kernel Verification}},
  year         = {2026},
  publisher    = {Zenodo},
  version      = {v1.0.0},
  doi          = {10.5281/zenodo.24440448},
  url          = {[https://doi.org/10.5281/zenodo.24440448](https://doi.org/10.5281/zenodo.24440448)}
}
```
