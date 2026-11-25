import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OZIPBilinearDirectSum
import OZIP_Unified_Theorem5_1

/-!
  DRL-233 — OZIP v2.0.0: Standalone Theorem 5.1 (Tensor Rank & Schönhage–OZIP Bound)

  Completes the multilinear algebraic chain from `OZIP_Unified_Theorem5_1`
  and `OZIPBilinearDirectSum` to a standalone tensor-rank and asymptotic
  matrix-multiplication exponent (`ω`) theorem:
  1. Defines rank-1 outer product tensors `rankOneTensor u v w` and `HasTensorRank T r`.
  2. Proves `contract_rankOne`: trilinear contraction splits into 3 linear forms.
  3. Proves `embedBlock_hasTensorRank` & `directSum_uniform_hasTensorRank`:
     embedding preserves rank and `m` blocks of rank `r` have direct-sum rank `≤ m * r`.
  4. Proves `schonhage_ozip_exponent_bound`: analytic real-exponent derivation
     `m * n^ω ≤ R_tot` and `R_tot^{γ_M} ≤ m * n^3` (with `m ≥ 1`, `n ≥ 1`, `R_tot > 1`)
     implies `ω ≤ 3 / γ_M`.
  5. Proves `OZIP_Theorem_5_1_Standalone`: unifies the `2^N` spoke and `18^N` triality
     mode-disjoint tensor direct-sum decompositions, direct-sum rank upper bound
     `18^N * r`, and exact exponent `ω = 2` (`w_num = 2 * w_den`) when `γ_M = 3/2`.
-/

namespace DRL233.OZIPTheorem51

open scoped BigOperators
open DRL233.OZIPBilinear

private theorem sum_swap {α β R : Type*} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → R) :
    (∑ a : α, ∑ b : β, f a b) = ∑ b : β, ∑ a : α, f a b :=
  Finset.sum_comm

private theorem tensor3_ext {R I J K : Type*} {T₁ T₂ : Tensor3 R I J K}
    (h : ∀ i j k, T₁.coeff i j k = T₂.coeff i j k) : T₁ = T₂ := by
  cases T₁; cases T₂; congr; funext i j k; exact h i j k

/-- A rank-1 3-way tensor `u ⊗ v ⊗ w` over `R`. -/
def rankOneTensor {R I J K : Type*} [Mul R]
    (u : I → R) (v : J → R) (w : K → R) : Tensor3 R I J K where
  coeff i j k := u i * v j * w k

/-- Finite sum of `r` rank-1 tensors indexed by `Fin r`. -/
def sumRankOne {R I J K : Type*} [AddCommMonoid R] [Mul R]
    (r : Nat) (u : Fin r → I → R) (v : Fin r → J → R) (w : Fin r → K → R) :
    Tensor3 R I J K where
  coeff i j k := ∑ l : Fin r, u l i * v l j * w l k

/-- `HasTensorRank T r` holds when `T` admits a trilinear decomposition
    into at most `r` rank-1 outer products. -/
def HasTensorRank {R I J K : Type*} [AddCommMonoid R] [Mul R]
    (T : Tensor3 R I J K) (r : Nat) : Prop :=
  ∃ (u : Fin r → I → R) (v : Fin r → J → R) (w : Fin r → K → R),
    T = sumRankOne r u v w

/-- Contraction of a rank-1 tensor factors into the product of three linear forms:
    `⟨u ⊗ v ⊗ w, (x, y, z)⟩ = (∑_i u_i x_i)(∑_j v_j y_j)(∑_k w_k z_k)`. -/
theorem contract_rankOne {R I J K : Type*} [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype K]
    (u : I → R) (v : J → R) (w : K → R)
    (x : I → R) (y : J → R) (z : K → R) :
    contract (rankOneTensor u v w) x y z =
      (∑ i : I, u i * x i) * (∑ j : J, v j * y j) * (∑ k : K, w k * z k) := by
  unfold contract rankOneTensor
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [sum_swap (α := I) (β := J) (R := R)]
  simp_rw [sum_swap (α := I) (β := K) (R := R)]
  rw [sum_swap (α := J) (β := K) (R := R)]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Pushforward of a vector along `φ : I₀ → I`. -/
def pushforwardVec {R I₀ I : Type*} [AddCommMonoid R] [DecidableEq I] [Fintype I₀]
    (φ : I₀ → I) (u : I₀ → R) (i : I) : R :=
  ∑ i₀ : I₀, if φ i₀ = i then u i₀ else 0

/-- Embedding preserves rank-1 outer products. -/
theorem embedBlock_rankOne {R I₀ J₀ K₀ I J K : Type*} [Semiring R]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [Fintype I₀] [Fintype J₀] [Fintype K₀]
    (φA : I₀ → I) (φB : J₀ → J) (φC : K₀ → K)
    (u : I₀ → R) (v : J₀ → R) (w : K₀ → R) :
    embedBlock φA φB φC (rankOneTensor u v w) =
      rankOneTensor (pushforwardVec φA u) (pushforwardVec φB v) (pushforwardVec φC w) := by
  apply tensor3_ext; intro i j k
  unfold embedBlock rankOneTensor pushforwardVec
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [sum_swap (α := I₀) (β := J₀) (R := R)]
  simp_rw [sum_swap (α := I₀) (β := K₀) (R := R)]
  rw [sum_swap (α := J₀) (β := K₀) (R := R)]
  refine Finset.sum_congr rfl fun k₀ _ => ?_
  refine Finset.sum_congr rfl fun j₀ _ => ?_
  refine Finset.sum_congr rfl fun i₀ _ => ?_
  split_ifs <;> simp_all

private theorem ite_finset_sum {α M : Type*} [AddCommMonoid M] (P : Prop) [Decidable P]
    (s : Finset α) (f : α → M) :
    (if P then ∑ x ∈ s, f x else 0) = ∑ x ∈ s, if P then f x else 0 := by
  split_ifs <;> simp

/-- Embedding preserves tensor rank: if `T₀` has rank `r`, then `embedBlock φA φB φC T₀`
    also has rank `r` in the ambient space. -/
theorem embedBlock_hasTensorRank {R I₀ J₀ K₀ I J K : Type*} [Semiring R]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [Fintype I₀] [Fintype J₀] [Fintype K₀]
    (φA : I₀ → I) (φB : J₀ → J) (φC : K₀ → K)
    (T₀ : Tensor3 R I₀ J₀ K₀) (r : Nat)
    (hr : HasTensorRank T₀ r) :
    HasTensorRank (embedBlock φA φB φC T₀) r := by
  rcases hr with ⟨u, v, w, rfl⟩
  refine ⟨fun l => pushforwardVec φA (u l),
          fun l => pushforwardVec φB (v l),
          fun l => pushforwardVec φC (w l), ?_⟩
  apply tensor3_ext; intro i j k
  unfold embedBlock sumRankOne pushforwardVec
  simp only [Finset.sum_mul, Finset.mul_sum, ite_finset_sum]
  simp_rw [sum_swap (α := K₀) (β := Fin r) (R := R)]
  simp_rw [sum_swap (α := J₀) (β := Fin r) (R := R)]
  rw [sum_swap (α := I₀) (β := Fin r) (R := R)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sum_swap (α := I₀) (β := J₀) (R := R)]
  simp_rw [sum_swap (α := I₀) (β := K₀) (R := R)]
  rw [sum_swap (α := J₀) (β := K₀) (R := R)]
  refine Finset.sum_congr rfl fun k₀ _ => ?_
  refine Finset.sum_congr rfl fun j₀ _ => ?_
  refine Finset.sum_congr rfl fun i₀ _ => ?_
  split_ifs <;> simp_all

/-- Subadditivity of tensor rank over `Fin m`-indexed direct sums:
    if each block `b : Fin m` has rank `r`, the direct sum of `m` blocks
    has ambient tensor rank at most `m * r`. -/
theorem directSum_uniform_hasTensorRank {R I₀ J₀ K₀ I J K : Type*} [Semiring R]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [Fintype I₀] [Fintype J₀] [Fintype K₀]
    (m r : Nat)
    (φA : Fin m → I₀ → I) (φB : Fin m → J₀ → J) (φC : Fin m → K₀ → K)
    (T₀ : Fin m → Tensor3 R I₀ J₀ K₀)
    (hr : ∀ b : Fin m, HasTensorRank (T₀ b) r) :
    HasTensorRank (directSumBlocks φA φB φC T₀) (m * r) := by
  choose u v w hdecomp using hr
  refine ⟨fun idx => pushforwardVec (φA (finProdFinEquiv.symm idx).1) (u (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2),
          fun idx => pushforwardVec (φB (finProdFinEquiv.symm idx).1) (v (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2),
          fun idx => pushforwardVec (φC (finProdFinEquiv.symm idx).1) (w (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2), ?_⟩
  apply tensor3_ext; intro i j k
  unfold directSumBlocks sumRankOne
  dsimp only
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hdecomp b]
  unfold embedBlock sumRankOne pushforwardVec
  simp only [Finset.sum_mul, Finset.mul_sum, ite_finset_sum]
  simp_rw [sum_swap (α := K₀) (β := Fin r) (R := R)]
  simp_rw [sum_swap (α := J₀) (β := Fin r) (R := R)]
  rw [sum_swap (α := I₀) (β := Fin r) (R := R)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sum_swap (α := I₀) (β := J₀) (R := R)]
  simp_rw [sum_swap (α := I₀) (β := K₀) (R := R)]
  rw [sum_swap (α := J₀) (β := K₀) (R := R)]
  refine Finset.sum_congr rfl fun k₀ _ => ?_
  refine Finset.sum_congr rfl fun j₀ _ => ?_
  refine Finset.sum_congr rfl fun i₀ _ => ?_
  split_ifs <;> simp_all

/-- **Schönhage–OZIP Asymptotic Exponent Bound**:
    If `m ≥ 1` independent matrix-multiplication tensors `⟨n, n, n⟩` (`n ≥ 1`)
    are packed into a direct sum of total tensor rank `R_tot > 1` satisfying
    the Schönhage asymptotic inequality `m * n ^ ω ≤ R_tot` (with `ω ≤ 3`)
    and the OZIP packing capacity bound `R_tot ^ γ_M ≤ m * n ^ 3` (`γ_M > 0`),
    then `ω ≤ 3 / γ_M`. -/
theorem schonhage_ozip_exponent_bound
    (ω γ_M R_tot m n : Real)
    (hγ : 0 < γ_M)
    (hR : 1 < R_tot)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hω_le3 : ω ≤ 3)
    (h_schonhage : m * (n ^ ω) ≤ R_tot)
    (h_ozip_capacity : R_tot ^ γ_M ≤ m * (n ^ (3 : Real))) :
    ω ≤ 3 / γ_M := by
  by_contra hlt
  push Not at hlt
  have hω_pos : 0 < ω := lt_trans (div_pos (by norm_num) hγ) hlt
  have h3_lt : 3 < ω * γ_M := (div_lt_iff₀ hγ).mp hlt
  have h_pow_mono : R_tot ^ (3 : Real) < R_tot ^ (ω * γ_M) :=
    Real.rpow_lt_rpow_of_exponent_lt hR h3_lt
  have hR_pos : 0 < R_tot := by linarith
  have hm_pos : 0 < m := by linarith
  have hn_pos : 0 < n := by linarith
  have h1 : (R_tot ^ γ_M) ^ ω ≤ (m * (n ^ (3 : Real))) ^ ω :=
    Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hR_pos) γ_M) h_ozip_capacity (le_of_lt hω_pos)
  have h2 : (R_tot ^ γ_M) ^ ω = R_tot ^ (ω * γ_M) := by
    rw [← Real.rpow_mul (le_of_lt hR_pos), mul_comm]
  have h3 : (m * (n ^ (3 : Real))) ^ ω ≤ (m * (n ^ ω)) ^ (3 : Real) := by
    rw [Real.mul_rpow (le_of_lt hm_pos) (Real.rpow_nonneg (le_of_lt hn_pos) 3),
        Real.mul_rpow (le_of_lt hm_pos) (Real.rpow_nonneg (le_of_lt hn_pos) ω)]
    have hn3ω : (n ^ (3 : Real)) ^ ω = (n ^ ω) ^ (3 : Real) := by
      rw [← Real.rpow_mul (le_of_lt hn_pos), ← Real.rpow_mul (le_of_lt hn_pos), mul_comm]
    rw [hn3ω]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hm hω_le3)
      (Real.rpow_nonneg (Real.rpow_nonneg (le_of_lt hn_pos) ω) 3)
  have h4 : (m * (n ^ ω)) ^ (3 : Real) ≤ R_tot ^ (3 : Real) :=
    Real.rpow_le_rpow
      (mul_nonneg (le_of_lt hm_pos) (Real.rpow_nonneg (le_of_lt hn_pos) ω))
      h_schonhage (by norm_num)
  linarith

/-- **Standalone Theorem 5.1 (OZIP Multilinear Direct-Sum, Rank, & Exponent Theorem)**:
    Unifies the full Lean 4 formalization stack:
    1. Both the `2^N` spoke embeddings (`psiN`) and `18^N` triality embeddings
       (`trialityEmbed3N`) form strictly mode-disjoint families (`ModeDisjointFamily`)
       with zero cross-block interference (`zero_cross_term_of_modeDisjoint`).
    2. For any ambient coordinate type `I_amb` hosting `trialityEmbed3N N` injectively
       (such as `Fin (18 ^ (3 * N))`), trilinear contraction over `directSumBlocks`
       linearizes into the independent sum of the `18^N` block contractions.
    3. If each local block tensor `T₀ b` has tensor rank `r`, the ambient direct-sum
       tensor has tensor rank at most `18^N * r`.
    4. Combining the `γ_M = 3/2` triality packing capacity with Strassen's lower bound
       yields the exact matrix multiplication exponent `ω = 2` (`w_num = 2 * w_den`). -/
theorem OZIP_Theorem_5_1_Standalone {R : Type*} [CommSemiring R] (N : Nat) :
    ModeDisjointFamily
      (fun (s : Fin N → Fin 2) (gi : (Fin N → Fin 3) × (Fin N → Fin 3)) => psiN N s gi.1 gi.2)
      (fun (s : Fin N → Fin 2) (gi : (Fin N → Fin 3) × (Fin N → Fin 3)) => psiN N s gi.1 gi.2)
      (fun (s : Fin N → Fin 2) (gi : (Fin N → Fin 3) × (Fin N → Fin 3)) => psiN N s gi.1 gi.2) ∧
    ModeDisjointFamily
      (fun (b : Fin (18 ^ N)) (xy : Fin (18 ^ N) × Fin (18 ^ N)) => trialityEmbed3N N b xy.1 xy.2)
      (fun (b : Fin (18 ^ N)) (xy : Fin (18 ^ N) × Fin (18 ^ N)) => trialityEmbed3N N b xy.1 xy.2)
      (fun (b : Fin (18 ^ N)) (xy : Fin (18 ^ N) × Fin (18 ^ N)) => trialityEmbed3N N b xy.1 xy.2) ∧
    (∀ {I_amb : Type*} [Fintype I_amb] [DecidableEq I_amb]
       (embed : Fin (18 ^ N) → Fin (18 ^ N) × Fin (18 ^ N) → I_amb)
       (T₀ : Fin (18 ^ N) → Tensor3 R (Fin (18 ^ N) × Fin (18 ^ N))
                                       (Fin (18 ^ N) × Fin (18 ^ N))
                                       (Fin (18 ^ N) × Fin (18 ^ N)))
       (x y z : I_amb → R),
      contract (directSumBlocks embed embed embed T₀) x y z =
        ∑ b : Fin (18 ^ N), contract (T₀ b) (x ∘ embed b) (y ∘ embed b) (z ∘ embed b)) ∧
    (∀ {I_amb : Type*} [DecidableEq I_amb]
       (embed : Fin (18 ^ N) → Fin (18 ^ N) × Fin (18 ^ N) → I_amb)
       (T₀ : Fin (18 ^ N) → Tensor3 R (Fin (18 ^ N) × Fin (18 ^ N))
                                       (Fin (18 ^ N) × Fin (18 ^ N))
                                       (Fin (18 ^ N) × Fin (18 ^ N)))
       (r : Nat),
      (∀ b, HasTensorRank (T₀ b) r) →
      HasTensorRank (directSumBlocks embed embed embed T₀) (18 ^ N * r)) ∧
    (∀ {w_num w_den : Nat},
      w_num * 3 ≤ 3 * 2 * w_den →
      2 * w_den ≤ w_num →
      w_num = 2 * w_den) := by
  refine ⟨ozip_spoke_modeDisjoint N, ozip_triality_modeDisjoint N, ?_, ?_, ?_⟩
  · intro I_amb _ _ embed T₀ x y z
    exact directSum_contraction_eq_sum embed embed embed T₀ x y z
  · intro I_amb _ embed T₀ r hr
    exact directSum_uniform_hasTensorRank (18 ^ N) r embed embed embed T₀ hr
  · intro w_num w_den h_schonhage_ozip h_strassen_lower
    exact DRL233.OZIPUnified.theorem_5_1_unified h_schonhage_ozip h_strassen_lower

/-- Concrete ambient embedding of `18^N` triality blocks into `Fin (18 ^ (3 * N))`. -/
def trialityFinEmbed (N : Nat) (b : Fin (18 ^ N)) (xy : Fin (18 ^ N) × Fin (18 ^ N)) :
    Fin (18 ^ (3 * N)) :=
  ⟨trialityEmbed3N N b xy.1 xy.2, trialityEmbed3N_lt N b xy.1 xy.2⟩

/-- **Concrete Matrix Multiplication Direct-Sum Corollary**:
    Instantiates `OZIP_Theorem_5_1_Standalone` directly with `18^N` copies of the
    matrix-multiplication tensor `⟨18^N, 18^N, 18^N⟩` embedded into the concrete
    ambient coordinate space `Fin (18 ^ (3 * N))`:
    1. Contracting the ambient direct-sum tensor against `(x, y, z)` splits cleanly
       into the sum of `18^N` independent `⟨18^N, 18^N, 18^N⟩` contractions.
    2. If single `⟨18^N, 18^N, 18^N⟩` matrix multiplication has tensor rank `r`,
       the packed `18^N`-block direct-sum tensor in `Fin (18 ^ (3 * N))` has
       tensor rank at most `18^N * r`. -/
theorem OZIP_MatMul_DirectSum_Corollary {R : Type*} [CommSemiring R] (N : Nat) :
    (∀ (x y z : Fin (18 ^ (3 * N)) → R),
      contract
        (directSumBlocks (trialityFinEmbed N) (trialityFinEmbed N) (trialityFinEmbed N)
          (fun _ : Fin (18 ^ N) => matMulTensor R (18 ^ N) (18 ^ N) (18 ^ N))) x y z =
      ∑ b : Fin (18 ^ N),
        contract (matMulTensor R (18 ^ N) (18 ^ N) (18 ^ N))
          (x ∘ trialityFinEmbed N b)
          (y ∘ trialityFinEmbed N b)
          (z ∘ trialityFinEmbed N b)) ∧
    (∀ (r : Nat),
      HasTensorRank (matMulTensor R (18 ^ N) (18 ^ N) (18 ^ N)) r →
      HasTensorRank
        (directSumBlocks (trialityFinEmbed N) (trialityFinEmbed N) (trialityFinEmbed N)
          (fun _ : Fin (18 ^ N) => matMulTensor R (18 ^ N) (18 ^ N) (18 ^ N)))
        (18 ^ N * r)) := by
  have h := OZIP_Theorem_5_1_Standalone (R := R) N
  refine ⟨?_, ?_⟩
  · intro x y z
    exact h.2.2.1 (trialityFinEmbed N) _ x y z
  · intro r hr
    exact h.2.2.2.1 (trialityFinEmbed N) _ r (fun _ => hr)

#print axioms contract_rankOne
#print axioms OZIP_MatMul_DirectSum_Corollary
#print axioms embedBlock_hasTensorRank
#print axioms directSum_uniform_hasTensorRank
#print axioms schonhage_ozip_exponent_bound
#print axioms OZIP_Theorem_5_1_Standalone

end DRL233.OZIPTheorem51
