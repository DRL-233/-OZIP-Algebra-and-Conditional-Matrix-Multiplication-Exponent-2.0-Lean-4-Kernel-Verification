import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import OZIPDecouplingInductive
import OZIPTrialitySymmetrization

/-!
  DRL-233 — OZIP v2.0-dev: Coordinate-to-Bilinear Direct-Sum Lift

  Formalizes the multilinear algebraic bridge lifting coordinate-level
  injectivity and block disjointness (`psiN_injective`,
  `spoke_blocks_strictly_disjoint`, `trialityEmbed3N_injective`) to a
  genuine direct sum of independent trilinear / matrix-multiplication
  tensors with zero cross-block interference.
-/

namespace DRL233.OZIPBilinear

open scoped BigOperators

private theorem sum_swap {α β R : Type*} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → R) :
    (∑ a : α, ∑ b : β, f a b) = ∑ b : β, ∑ a : α, f a b :=
  Finset.sum_comm

/-- A finite 3-way tensor over a semiring `R` indexed by finite coordinate types `I`, `J`, `K`. -/
structure Tensor3 (R : Type*) (I J K : Type*) where
  coeff : I → J → K → R

/-- Trilinear contraction ⟨T, (x, y, z)⟩ = ∑_{i,j,k} T(i,j,k) x(i) y(j) z(k). -/
def contract {R : Type*} {I J K : Type*} [CommSemiring R] [Fintype I] [Fintype J] [Fintype K]
    (T : Tensor3 R I J K) (x : I → R) (y : J → R) (z : K → R) : R :=
  ∑ i : I, ∑ j : J, ∑ k : K, T.coeff i j k * x i * y j * z k

/-- Embedding of a local block tensor `T₀` into ambient coordinates `(I, J, K)`
    along injective coordinate maps `(φA, φB, φC)`. -/
def embedBlock {R : Type*} {I₀ J₀ K₀ I J K : Type*} [AddCommMonoid R]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [Fintype I₀] [Fintype J₀] [Fintype K₀]
    (φA : I₀ → I) (φB : J₀ → J) (φC : K₀ → K)
    (T₀ : Tensor3 R I₀ J₀ K₀) : Tensor3 R I J K where
  coeff i j k :=
    ∑ i₀ : I₀, ∑ j₀ : J₀, ∑ k₀ : K₀,
      if φA i₀ = i ∧ φB j₀ = j ∧ φC k₀ = k then T₀.coeff i₀ j₀ k₀ else 0

/-- Direct sum of a finite family of embedded block tensors. -/
def directSumBlocks {R : Type*} {B I₀ J₀ K₀ I J K : Type*} [AddCommMonoid R]
    [Fintype B] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [Fintype I₀] [Fintype J₀] [Fintype K₀]
    (φA : B → I₀ → I) (φB : B → J₀ → J) (φC : B → K₀ → K)
    (T₀ : B → Tensor3 R I₀ J₀ K₀) : Tensor3 R I J K where
  coeff i j k :=
    ∑ b : B, (embedBlock (φA b) (φB b) (φC b) (T₀ b)).coeff i j k

/-- Single-block contraction identity: contracting an embedded tensor against
    ambient vectors `(x, y, z)` equals contracting `T₀` against the pulled-back
    vectors `(x ∘ φA, y ∘ φB, z ∘ φC)`. -/
theorem contract_embedBlock {R : Type*} {I₀ J₀ K₀ I J K : Type*} [CommSemiring R]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [Fintype I₀] [Fintype J₀] [Fintype K₀]
    [Fintype I] [Fintype J] [Fintype K]
    (φA : I₀ → I) (φB : J₀ → J) (φC : K₀ → K)
    (T₀ : Tensor3 R I₀ J₀ K₀) (x : I → R) (y : J → R) (z : K → R) :
    contract (embedBlock φA φB φC T₀) x y z =
      contract T₀ (x ∘ φA) (y ∘ φB) (z ∘ φC) := by
  unfold contract embedBlock
  simp only [Function.comp_apply]
  simp_rw [Finset.sum_mul]
  -- Collapse triple sums into single product sums over (I × J × K) and (I₀ × J₀ × K₀)
  have hL :
      (∑ i : I, ∑ j : J, ∑ k : K, ∑ i₀ : I₀, ∑ j₀ : J₀, ∑ k₀ : K₀,
        (if φA i₀ = i ∧ φB j₀ = j ∧ φC k₀ = k then T₀.coeff i₀ j₀ k₀ else 0) * x i * y j * z k) =
      ∑ p : I × J × K, ∑ q : I₀ × J₀ × K₀,
        if (φA q.1, φB q.2.1, φC q.2.2) = p
        then T₀.coeff q.1 q.2.1 q.2.2 * x p.1 * y p.2.1 * z p.2.2 else 0 := by
    simp only [Fintype.sum_prod_type, Prod.mk.injEq, ite_mul, zero_mul]
  have hR :
      (∑ i₀ : I₀, ∑ j₀ : J₀, ∑ k₀ : K₀,
        T₀.coeff i₀ j₀ k₀ * x (φA i₀) * y (φB j₀) * z (φC k₀)) =
      ∑ q : I₀ × J₀ × K₀,
        T₀.coeff q.1 q.2.1 q.2.2 * x (φA q.1) * y (φB q.2.1) * z (φC q.2.2) := by
    simp only [Fintype.sum_prod_type]
  rw [hL, hR, sum_swap]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- Mode-disjointness predicate: distinct blocks `b₁ ≠ b₂` never overlap
    on any of the three tensor factor supports. -/
def ModeDisjointFamily {B I₀ J₀ K₀ I J K : Type*}
    (φA : B → I₀ → I) (φB : B → J₀ → J) (φC : B → K₀ → K) : Prop :=
  (∀ b₁ b₂ i₁ i₂, b₁ ≠ b₂ → φA b₁ i₁ ≠ φA b₂ i₂) ∧
  (∀ b₁ b₂ j₁ j₂, b₁ ≠ b₂ → φB b₁ j₁ ≠ φB b₂ j₂) ∧
  (∀ b₁ b₂ k₁ k₂, b₁ ≠ b₂ → φC b₁ k₁ ≠ φC b₂ k₂)

/-- Zero cross-talk theorem: if blocks are mode-disjoint, two distinct blocks
    never share an active ambient coordinate triple `(i, j, k)`. -/
theorem zero_cross_term_of_modeDisjoint {R : Type*} {B I₀ J₀ K₀ I J K : Type*} [AddCommMonoid R]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [Fintype I₀] [Fintype J₀] [Fintype K₀]
    {φA : B → I₀ → I} {φB : B → J₀ → J} {φC : B → K₀ → K}
    (hdisj : ModeDisjointFamily φA φB φC)
    (T₀ : B → Tensor3 R I₀ J₀ K₀)
    {b₁ b₂ : B} (hb : b₁ ≠ b₂) (i : I) (j : J) (k : K) :
    (embedBlock (φA b₁) (φB b₁) (φC b₁) (T₀ b₁)).coeff i j k = 0 ∨
    (embedBlock (φA b₂) (φB b₂) (φC b₂) (T₀ b₂)).coeff i j k = 0 := by
  by_cases h1 : ∀ i₁ j₁ k₁, ¬(φA b₁ i₁ = i ∧ φB b₁ j₁ = j ∧ φC b₁ k₁ = k)
  · left
    unfold embedBlock
    apply Finset.sum_eq_zero
    intro i₁ _
    apply Finset.sum_eq_zero
    intro j₁ _
    apply Finset.sum_eq_zero
    intro k₁ _
    simp [h1 i₁ j₁ k₁]
  · right
    push Not at h1
    obtain ⟨i₁, j₁, k₁, hi₁, hj₁, hk₁⟩ := h1
    unfold embedBlock
    apply Finset.sum_eq_zero
    intro i₂ _
    apply Finset.sum_eq_zero
    intro j₂ _
    apply Finset.sum_eq_zero
    intro k₂ _
    have hne : ¬(φA b₂ i₂ = i ∧ φB b₂ j₂ = j ∧ φC b₂ k₂ = k) := by
      intro h2
      exact hdisj.1 b₁ b₂ i₁ i₂ hb (hi₁.trans h2.1.symm)
    simp [hne]

/-- Direct-sum decomposition theorem: contracting a mode-disjoint direct sum
    of embedded tensors splits cleanly into the sum of independent block
    contractions with zero cross-terms. -/
theorem directSum_contraction_eq_sum {R : Type*} {B I₀ J₀ K₀ I J K : Type*} [CommSemiring R]
    [Fintype B] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [Fintype I₀] [Fintype J₀] [Fintype K₀]
    [Fintype I] [Fintype J] [Fintype K]
    (φA : B → I₀ → I) (φB : B → J₀ → J) (φC : B → K₀ → K)
    (T₀ : B → Tensor3 R I₀ J₀ K₀) (x : I → R) (y : J → R) (z : K → R) :
    contract (directSumBlocks φA φB φC T₀) x y z =
      ∑ b : B, contract (T₀ b) (x ∘ φA b) (y ∘ φB b) (z ∘ φC b) := by
  unfold contract directSumBlocks
  simp_rw [Finset.sum_mul]
  simp_rw [sum_swap (α := K) (β := B) (R := R)]
  simp_rw [sum_swap (α := J) (β := B) (R := R)]
  rw [sum_swap (α := I) (β := B) (R := R)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hswap :
      (∑ i : I, ∑ j : J, ∑ k : K,
        (embedBlock (φA b) (φB b) (φC b) (T₀ b)).coeff i j k * x i * y j * z k) =
      contract (embedBlock (φA b) (φB b) (φC b) (T₀ b)) x y z := rfl
  rw [hswap, contract_embedBlock]
  rfl

/-- Matrix multiplication tensor ⟨m, n, p⟩ over `R`. -/
def matMulTensor (R : Type*) [Zero R] [One R] (m n p : Nat) [DecidableEq (Fin n)] :
    Tensor3 R (Fin m × Fin n) (Fin n × Fin p) (Fin p × Fin m) where
  coeff a b c :=
    if a.2 = b.1 ∧ b.2 = c.1 ∧ c.2 = a.1 then 1 else 0

/-- OZIP Spoke Direct-Sum Bridge: for every `N : Nat`, the `2^N` spoke tuples
    `s : Fin N → Fin 2` induce a mode-disjoint family of embeddings via `psiN`
    across all three tensor factors simultaneously. -/
theorem ozip_spoke_modeDisjoint (N : Nat) :
    ModeDisjointFamily
      (fun (s : Fin N → Fin 2) (gi : (Fin N → Fin 3) × (Fin N → Fin 3)) => psiN N s gi.1 gi.2)
      (fun (s : Fin N → Fin 2) (gi : (Fin N → Fin 3) × (Fin N → Fin 3)) => psiN N s gi.1 gi.2)
      (fun (s : Fin N → Fin 2) (gi : (Fin N → Fin 3) × (Fin N → Fin 3)) => psiN N s gi.1 gi.2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s₁ s₂ x₁ x₂ hne
    exact spoke_blocks_strictly_disjoint N hne x₁.1 x₂.1 x₁.2 x₂.2
  · intro s₁ s₂ x₁ x₂ hne
    exact spoke_blocks_strictly_disjoint N hne x₁.1 x₂.1 x₁.2 x₂.2
  · intro s₁ s₂ x₁ x₂ hne
    exact spoke_blocks_strictly_disjoint N hne x₁.1 x₂.1 x₁.2 x₂.2

/-- Triality Entangled One-Shot Direct-Sum Bridge: for every `N : Nat`,
    `trialityEmbed3N` embeds `18^N` diagonal triality blocks across all three
    factors in `Fin (18^(3N))` with strict mode-disjointness. -/
theorem ozip_triality_modeDisjoint (N : Nat) :
    ModeDisjointFamily
      (fun (b : Fin (18 ^ N)) (xy : Fin (18 ^ N) × Fin (18 ^ N)) => trialityEmbed3N N b xy.1 xy.2)
      (fun (b : Fin (18 ^ N)) (xy : Fin (18 ^ N) × Fin (18 ^ N)) => trialityEmbed3N N b xy.1 xy.2)
      (fun (b : Fin (18 ^ N)) (xy : Fin (18 ^ N) × Fin (18 ^ N)) => trialityEmbed3N N b xy.1 xy.2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b₁ b₂ x₁ x₂ hne heq
    exact hne (trialityEmbed3N_injective N heq).1
  · intro b₁ b₂ x₁ x₂ hne heq
    exact hne (trialityEmbed3N_injective N heq).1
  · intro b₁ b₂ x₁ x₂ hne heq
    exact hne (trialityEmbed3N_injective N heq).1

#print axioms contract_embedBlock
#print axioms zero_cross_term_of_modeDisjoint
#print axioms directSum_contraction_eq_sum
#print axioms ozip_spoke_modeDisjoint
#print axioms ozip_triality_modeDisjoint

end DRL233.OZIPBilinear
