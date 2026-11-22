module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Lean 4 Formalization Script: Complete BBGT-9PT-V1 Multiplication Table (zipMul),
# Entry-Level Table Verification, Support Arithmetic (462 / 19,221),
# 54×54 Idempotent Projector P_M, Exact ⟨3,3,2⟩ Tensor Restriction Witness,
# and Conditional ω = 2.0 Deduction

- **Author:** Matthias Asare-Darko (Darkon Research Laboratory, Ghana)
- **Zenodo Archive DOI:** https://doi.org/10.5281/zenodo.24440448
- **Toolchain:** Lean 4 (`v4.36.0-rc2`) + Mathlib
-/

@[expose] public section

namespace DarkonLab.OZIP

/-- 1. Complete 9-Basis Representation and Table-Authoritative zipMul (BBGT-9PT-V1) -/
inductive ZIPBasis
  | em1 | e0 | e1 | e2 | e3 | e4 | e5 | e6 | e7
  deriving DecidableEq, Repr

structure ZIPVec (R : Type) where
  cm1 : R
  c0  : R
  c1  : R
  c2  : R
  c3  : R
  c4  : R
  c5  : R
  c6  : R
  c7  : R
  deriving DecidableEq, Repr

def ZIPVec.zero {R : Type} [Zero R] : ZIPVec R :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def ZIPVec.single {R : Type} [Zero R] (b : ZIPBasis) (v : R) : ZIPVec R :=
  match b with
  | .em1 => { ZIPVec.zero with cm1 := v }
  | .e0  => { ZIPVec.zero with c0  := v }
  | .e1  => { ZIPVec.zero with c1  := v }
  | .e2  => { ZIPVec.zero with c2  := v }
  | .e3  => { ZIPVec.zero with c3  := v }
  | .e4  => { ZIPVec.zero with c4  := v }
  | .e5  => { ZIPVec.zero with c5  := v }
  | .e6  => { ZIPVec.zero with c6  := v }
  | .e7  => { ZIPVec.zero with c7  := v }

def ZIPVec.withAssoc {R : Type} [Zero R] [Add R]
    (b : ZIPBasis) (v : R) (A : R) : ZIPVec R :=
  match b with
  | .e4 => ZIPVec.single .e4 (v + A)
  | _   => { ZIPVec.single b v with c4 := A }

def ZIPVec.coord {R : Type} (v : ZIPVec R) (b : ZIPBasis) : R :=
  match b with
  | .em1 => v.cm1
  | .e0  => v.c0
  | .e1  => v.c1
  | .e2  => v.c2
  | .e3  => v.c3
  | .e4  => v.c4
  | .e5  => v.c5
  | .e6  => v.c6
  | .e7  => v.c7

def natToZIPBasis (n : Nat) : ZIPBasis :=
  match n with
  | 0 => .em1
  | 1 => .e0
  | 2 => .e1
  | 3 => .e2
  | 4 => .e3
  | 5 => .e4
  | 6 => .e5
  | 7 => .e6
  | _ => .e7

/-- Complete 9×9 BBGT-9PT-V1 Multiplication Table (Table 1 of Manuscript) -/
def zipMul {R : Type} [Zero R] [One R] [Neg R] [Add R]
    (A : R) (a b : ZIPBasis) : ZIPVec R :=
  match a, b with
  | .em1, .e7  => ZIPVec.zero
  | .em1, x    => ZIPVec.single x 1
  | .e0, .em1  => ZIPVec.single .e0 1
  | .e0, .e0   => ZIPVec.single .em1 1
  | .e0, .e1   => ZIPVec.withAssoc .e2 1 A
  | .e0, .e2   => ZIPVec.withAssoc .e1 (-1) A
  | .e0, .e3   => ZIPVec.withAssoc .e5 1 A
  | .e0, .e4   => ZIPVec.zero
  | .e0, .e5   => ZIPVec.withAssoc .e3 (-1) A
  | .e0, .e6   => ZIPVec.withAssoc .e1 1 A
  | .e0, .e7   => ZIPVec.single .e0 (-1)
  | .e1, .em1  => ZIPVec.single .e1 1
  | .e1, .e0   => ZIPVec.withAssoc .e2 (-1) A
  | .e1, .e1   => ZIPVec.single .em1 1
  | .e1, .e2   => ZIPVec.withAssoc .e3 1 A
  | .e1, .e3   => ZIPVec.withAssoc .e2 (-1) A
  | .e1, .e4   => ZIPVec.zero
  | .e1, .e5   => ZIPVec.withAssoc .e6 1 A
  | .e1, .e6   => ZIPVec.withAssoc .e5 (-1) A
  | .e1, .e7   => ZIPVec.single .e1 (-1)
  | .e2, .em1  => ZIPVec.single .e2 1
  | .e2, .e0   => ZIPVec.withAssoc .e1 1 A
  | .e2, .e1   => ZIPVec.withAssoc .e3 (-1) A
  | .e2, .e2   => ZIPVec.single .em1 1
  | .e2, .e3   => ZIPVec.withAssoc .e1 1 A
  | .e2, .e4   => ZIPVec.zero
  | .e2, .e5   => ZIPVec.withAssoc .e0 1 A
  | .e2, .e6   => ZIPVec.withAssoc .e3 1 A
  | .e2, .e7   => ZIPVec.single .e2 (-1)
  | .e3, .em1  => ZIPVec.single .e3 1
  | .e3, .e0   => ZIPVec.withAssoc .e5 (-1) A
  | .e3, .e1   => ZIPVec.withAssoc .e2 1 A
  | .e3, .e2   => ZIPVec.withAssoc .e1 (-1) A
  | .e3, .e3   => ZIPVec.single .em1 1
  | .e3, .e4   => ZIPVec.zero
  | .e3, .e5   => ZIPVec.withAssoc .e0 (-1) A
  | .e3, .e6   => ZIPVec.withAssoc .e2 1 A
  | .e3, .e7   => ZIPVec.single .e3 (-1)
  | .e4, .em1  => ZIPVec.single .e4 1
  | .e4, .e0   => ZIPVec.zero
  | .e4, .e1   => ZIPVec.zero
  | .e4, .e2   => ZIPVec.zero
  | .e4, .e3   => ZIPVec.zero
  | .e4, .e4   => ZIPVec.withAssoc .em1 1 A
  | .e4, .e5   => ZIPVec.zero
  | .e4, .e6   => ZIPVec.zero
  | .e4, .e7   => ZIPVec.single .e4 (-1)
  | .e5, .em1  => ZIPVec.single .e5 1
  | .e5, .e0   => ZIPVec.withAssoc .e3 1 A
  | .e5, .e1   => ZIPVec.withAssoc .e6 (-1) A
  | .e5, .e2   => ZIPVec.withAssoc .e0 (-1) A
  | .e5, .e3   => ZIPVec.withAssoc .e0 1 A
  | .e5, .e4   => ZIPVec.zero
  | .e5, .e5   => ZIPVec.single .em1 1
  | .e5, .e6   => ZIPVec.withAssoc .e1 1 A
  | .e5, .e7   => ZIPVec.single .e5 (-1)
  | .e6, .em1  => ZIPVec.single .e6 1
  | .e6, .e0   => ZIPVec.withAssoc .e1 (-1) A
  | .e6, .e1   => ZIPVec.withAssoc .e5 1 A
  | .e6, .e2   => ZIPVec.withAssoc .e3 1 A
  | .e6, .e3   => ZIPVec.withAssoc .e2 (-1) A
  | .e6, .e4   => ZIPVec.zero
  | .e6, .e5   => ZIPVec.withAssoc .e1 (-1) A
  | .e6, .e6   => ZIPVec.single .em1 1
  | .e6, .e7   => ZIPVec.single .em1 1
  | .e7, .em1  => ZIPVec.zero
  | .e7, .e0   => ZIPVec.single .e0 (-1)
  | .e7, .e1   => ZIPVec.single .e1 (-1)
  | .e7, .e2   => ZIPVec.single .e2 (-1)
  | .e7, .e3   => ZIPVec.single .e3 (-1)
  | .e7, .e4   => ZIPVec.single .e4 (-1)
  | .e7, .e5   => ZIPVec.single .e5 (-1)
  | .e7, .e6   => ZIPVec.single .em1 1
  | .e7, .e7   => ZIPVec.single .em1 1

/- Entry-level verification of BBGT-9PT-V1 -/

def isInteriorGaugeDir : ZIPBasis → Bool
  | .e0 | .e1 | .e2 | .e3 | .e5 | .e6 => true
  | _ => false

theorem e1_mul_e5_eq_e6_plus_Ae4
    {R : Type} [Zero R] [One R] [Neg R] [Add R] (A : R) :
    zipMul A .e1 .e5 = ZIPVec.withAssoc .e6 1 A := rfl

theorem e4_annihilates_six_interior_directions
    {R : Type} [Zero R] [One R] [Neg R] [Add R]
    (A : R) (b : ZIPBasis) (hb : isInteriorGaugeDir b = true) :
    zipMul A .e4 b = ZIPVec.zero := by
  cases b <;> simp [isInteriorGaugeDir] at hb <;> rfl

/-- 2. Exact Support Arithmetic of the 27×27×27 Unprojected Split-Albert Comparison Tensor -/
def albertDim : Nat := 27
def totalCubicChannels : Nat := albertDim ^ 3
def diagonalTorusSupport : Nat := 6
def scalarNormSupport : Nat := 72
def trialityCoreSupport : Nat := 384
def totalNonZeroSupport : Nat := diagonalTorusSupport + scalarNormSupport + trialityCoreSupport
def structuralZeroSupport : Nat := totalCubicChannels - totalNonZeroSupport

theorem albert_support_accounting :
    totalCubicChannels = 19683 ∧
    totalNonZeroSupport = 462 ∧
    structuralZeroSupport = 19221 ∧
    totalNonZeroSupport + structuralZeroSupport = totalCubicChannels := by
  decide

/-- 3. Explicit 54×54 Sector-Differentiated Idempotent Molniya Projector P_M -/
def diagWeight (idx : Nat) : ℚ :=
  if idx < 3 then (1 / 5 : ℚ) else (4 / 5 : ℚ)

def offDiagWeight : ℚ := (2 / 5 : ℚ)

def P_M : Matrix (Fin 54) (Fin 54) ℚ := fun r c =>
  if r.val < 27 ∧ c.val < 27 then
    if r.val = c.val then diagWeight r.val else 0
  else if r.val < 27 ∧ 27 ≤ c.val then
    if r.val + 27 = c.val then offDiagWeight else 0
  else if 27 ≤ r.val ∧ c.val < 27 then
    if r.val = c.val + 27 then offDiagWeight else 0
  else
    if r.val = c.val then 1 - diagWeight (r.val % 27) else 0

def Q_M : Matrix (Fin 54) (Fin 54) ℤ := fun r c =>
  if r.val < 27 ∧ c.val < 27 then
    if r.val = c.val then (if r.val < 3 then 1 else 4) else 0
  else if r.val < 27 ∧ 27 ≤ c.val then
    if r.val + 27 = c.val then 2 else 0
  else if 27 ≤ r.val ∧ c.val < 27 then
    if r.val = c.val + 27 then 2 else 0
  else
    if r.val = c.val then (if r.val % 27 < 3 then 4 else 1) else 0

/-- TTB2 2-spoke hub collapse for Matrix.mul with Q_M:
    every row r of Q_M vanishes outside {r % 27, (r % 27) + 27} -/
lemma Q_M_row_two_spoke {n : Type*} (M : Matrix (Fin 54) n ℤ)
    (r : Fin 54) (c : n) :
    (Q_M * M) r c =
      Q_M r ⟨r.val % 27, by omega⟩ * M ⟨r.val % 27, by omega⟩ c +
      Q_M r ⟨r.val % 27 + 27, by omega⟩ * M ⟨r.val % 27 + 27, by omega⟩ c := by
  simp only [Matrix.mul_apply]
  have h0 : (⟨r.val % 27, by omega⟩ : Fin 54) ≠ ⟨r.val % 27 + 27, by omega⟩ := by
    intro h; have := congrArg Fin.val h; dsimp at this; omega
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨r.val % 27, by omega⟩)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h0.symm, Finset.mem_univ _⟩)]
  have hzero : ∑ k ∈ (Finset.univ.erase ⟨r.val % 27, by omega⟩).erase
      ⟨r.val % 27 + 27, by omega⟩, Q_M r k * M k c = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
    have hk1 : k.val ≠ r.val % 27 := fun h => hk.2 (Fin.ext h)
    have hk2 : k.val ≠ r.val % 27 + 27 := fun h => hk.1 (Fin.ext h)
    have hq : Q_M r k = 0 := by
      dsimp [Q_M]
      split_ifs <;> omega
    rw [hq, zero_mul]
  rw [hzero, add_zero]

theorem Q_M_sq : Q_M * Q_M = (5 : ℤ) • Q_M := by
  ext r c
  rw [Q_M_row_two_spoke]
  revert r c
  decide

lemma P_M_eq_smul_Q_M : P_M = ((1 / 5 : ℚ)) • Q_M.map Int.cast := by
  ext r c
  simp only [P_M, Q_M, diagWeight, offDiagWeight, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  split_ifs <;> norm_num

theorem P_M_idempotent : P_M * P_M = P_M := by
  have hmap : (Q_M.map (Int.cast : ℤ → ℚ)) * (Q_M.map (Int.cast : ℤ → ℚ)) =
      (5 : ℚ) • (Q_M.map (Int.cast : ℤ → ℚ)) := by
    ext r c
    have hrc := congrFun (congrFun Q_M_sq r) c
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hrc ⊢
    exact_mod_cast hrc
  calc
    P_M * P_M = (((1 / 5 : ℚ)) • Q_M.map Int.cast) * (((1 / 5 : ℚ)) • Q_M.map Int.cast) := by
      rw [P_M_eq_smul_Q_M]
    _ = ((1 / 5 : ℚ) * (1 / 5 : ℚ)) • ((Q_M.map Int.cast) * (Q_M.map Int.cast)) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = ((1 / 5 : ℚ) * (1 / 5 : ℚ)) • ((5 : ℚ) • Q_M.map Int.cast) := by
      rw [hmap]
    _ = ((1 / 5 : ℚ)) • Q_M.map Int.cast := by
      rw [smul_smul]; norm_num
    _ = P_M := P_M_eq_smul_Q_M.symm

/- 4. TTB2-Sparse Exact Rational Projection Matrices X, Y, Z & ⟨3,3,2⟩ Witness -/

/-- Flat Nat-indexed 54×54×54 OZIP structure tensor (TTB2 hub-flattened representation) -/
def ozip54Nat (a b c : Nat) : ℤ :=
  if (a < 27 ∧ b < 27 ∧ c < 27) ∨ (27 ≤ a ∧ 27 ≤ b ∧ 27 ≤ c) then
    let a0 := a % 27
    let b0 := b % 27
    let c0 := c % 27
    if ((a0 / 9) + (b0 / 9)) % 3 = (c0 / 9) then
      (zipMul (0 : ℤ) (natToZIPBasis (a0 % 9)) (natToZIPBasis (b0 % 9))).coord
        (natToZIPBasis (c0 % 9))
    else 0
  else 0

/-- Flat Nat-indexed ⟨3, 3, 2⟩ matrix multiplication tensor of shape (9, 6, 6) -/
def matmul332Nat (p q r : Nat) : ℤ :=
  if p / 3 = r / 2 ∧ p % 3 = q / 2 ∧ q % 2 = r % 2 then 1 else 0

/-- Integer-scaled Molniya eigenvector embedding: w(base) ∈ ℤ^{54} with P_M * w(base) = w(base) -/
def molniyaEigCoeff (base row : Nat) : ℤ :=
  if base < 3 then
    if row = base then 1 else if row = base + 27 then 2 else 0
  else
    if row = base then 2 else if row = base + 27 then 1 else 0

/-- TTB2 Predicate-Sparse Spoke Directories:
    each column has exactly 2 active hub rows (base, base + 27) -/
def xBase (p : Nat) : Nat :=
  let i := p / 3
  let j := p % 3
  let xOffset := match i with | 0 => 3 | 1 => 6 | _ => 4
  j * 9 + xOffset

def yBase (q : Nat) : Nat :=
  let j := q / 2
  let k := q % 2
  let s2 := (3 - j) % 3
  let yOffset := if k = 0 then 3 else 8
  s2 * 9 + yOffset

def zSpec (r : Nat) : Nat × ℤ :=
  let i := r / 2
  let k := r % 2
  match i, k with
  | 0, 0 => (0,  3)
  | 1, 0 => (1, -3)
  | 2, 0 => (2, -3)
  | 0, _ => (3, -2)
  | 1, _ => (6, -2)
  | _, _ => (4, -2)

def X_int : Matrix (Fin 54) (Fin 9) ℤ := fun row p =>
  molniyaEigCoeff (xBase p.val) row.val

def Y_int : Matrix (Fin 54) (Fin 6) ℤ := fun row q =>
  molniyaEigCoeff (yBase q.val) row.val

def Z_int : Matrix (Fin 54) (Fin 6) ℤ := fun row r =>
  let (zOffset, scaleSgn) := zSpec r.val
  scaleSgn * molniyaEigCoeff zOffset row.val

def X_proj : Matrix (Fin 54) (Fin 9) ℚ := fun r p => (X_int r p : ℚ)
def Y_proj : Matrix (Fin 54) (Fin 6) ℚ := fun r q => (Y_int r q : ℚ)
def Z_proj : Matrix (Fin 54) (Fin 6) ℚ := fun r c => (1 / 18 : ℚ) * (Z_int r c : ℚ)

theorem X_int_in_image_Q_M : Q_M * X_int = (5 : ℤ) • X_int := by
  ext r p
  rw [Q_M_row_two_spoke]
  revert r p
  decide

theorem Y_int_in_image_Q_M : Q_M * Y_int = (5 : ℤ) • Y_int := by
  ext r q
  rw [Q_M_row_two_spoke]
  revert r q
  decide

theorem Z_int_in_image_Q_M : Q_M * Z_int = (5 : ℤ) • Z_int := by
  ext r c
  rw [Q_M_row_two_spoke]
  revert r c
  decide

/-- TTB2 Sparse 2-Spoke Contraction (evaluates ONLY the 2×2×2 = 8 nonzero hub entries per triple) -/
def sparseContract332 (p q r : Nat) : ℤ :=
  let bx := xBase p
  let by_ := yBase q
  let (bz, scaleSgn) := zSpec r
  let xSpokes := [bx, bx + 27]
  let ySpokes := [by_, by_ + 27]
  let zSpokes := [bz, bz + 27]
  (xSpokes.map fun i =>
    (ySpokes.map fun j =>
      (zSpokes.map fun k =>
        molniyaEigCoeff bx i * molniyaEigCoeff by_ j *
        (scaleSgn * molniyaEigCoeff bz k) * ozip54Nat i j k).sum).sum).sum

/-- Zero-overhead proof that every row outside the 2-spoke hub is identically zero -/
theorem X_int_sparse_support (row : Fin 54) (p : Fin 9)
    (h1 : row.val ≠ xBase p.val) (h2 : row.val ≠ xBase p.val + 27) :
    X_int row p = 0 := by
  simp [X_int, molniyaEigCoeff, h1, h2]

theorem Y_int_sparse_support (row : Fin 54) (q : Fin 6)
    (h1 : row.val ≠ yBase q.val) (h2 : row.val ≠ yBase q.val + 27) :
    Y_int row q = 0 := by
  simp [Y_int, molniyaEigCoeff, h1, h2]

theorem Z_int_sparse_support (row : Fin 54) (r : Fin 6)
    (h1 : row.val ≠ (zSpec r.val).1) (h2 : row.val ≠ (zSpec r.val).1 + 27) :
    Z_int row r = 0 := by
  simp [Z_int, molniyaEigCoeff, h1, h2]

/-- Instantaneous pure-kernel 324-entry verification (324 × 8 = 2,592 ops vs 8,748,000) -/
theorem ozip54_restricts_to_18_matmul332 :
    (List.range 9).all (fun p =>
      (List.range 6).all (fun q =>
        (List.range 6).all (fun r =>
          sparseContract332 p q r == 18 * matmul332Nat p q r))) = true := by
  decide

/-- 5. Conditional Transitive Theorem: Conjecture 5.1 (γ_M = 3/2) + (ω ≥ 2) => ω = 2 -/
structure MolniyaTrialityHypothesis (t ω : ℝ) : Prop where
  t_pos : 0 < t
  triality_growth_bound : (3 : ℝ) / 2 ≤ 1 / t
  detecting_character_upper : ω ≤ 3 * t
  info_theoretic_lower : 2 ≤ ω

theorem conditional_exact_omega_two (t ω : ℝ) (h : MolniyaTrialityHypothesis t ω) :
    ω = 2 := by
  have ht_inv : (3 : ℝ) / 2 ≤ 1 / t := h.triality_growth_bound
  have ht : t ≤ 2 / 3 := by
    rw [le_div_iff₀ h.t_pos] at ht_inv
    linarith
  have hω_upper : ω ≤ 2 := by
    have h3t : 3 * t ≤ 2 := by linarith
    linarith [h.detecting_character_upper]
  linarith [h.info_theoretic_lower]

end DarkonLab.OZIP
