import MerLeanBpqc.Definitions.Def_18_CheegerConstant
import MerLeanBpqc.Definitions.Def_14_GraphExpansion

/-!
# Lemma 1: Relative Cheeger Inequality

## Main Results
- `relativeCheeger`: For a finite, connected, `s`-regular graph with second-largest eigenvalue
  `λ₂`, and for `S ⊆ V` with `0 < |S| < α|V|` where `α ∈ (0, 1)`, we have
  `(1 - α)(s - λ₂) ≤ |δS| / |S|`.
-/

open Finset SimpleGraph BigOperators GraphExpansion CheegerConstant

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace RelativeCheeger

/-! ## Step 0: Well-definedness

Since `|S| ≥ 1` and `|S| < α|V|` with `α < 1`, we have `|V| ≥ 2`, so `λ₂` is well-defined. -/

lemma card_ge_two_of_subset (S : Finset V) (α : ℝ) (hα1 : α < 1)
    (hS_pos : 0 < S.card) (hS_lt : (S.card : ℝ) < α * Fintype.card V) :
    2 ≤ Fintype.card V := by
  by_contra h
  push_neg at h
  have hV : Fintype.card V ≤ 1 := by omega
  have hSV : S.card ≤ Fintype.card V := S.card_le_univ
  have : S.card ≤ 1 := le_trans hSV hV
  have hS1 : S.card = 1 := by omega
  have hV1 : Fintype.card V = 1 := by omega
  have : (S.card : ℝ) < α * Fintype.card V := hS_lt
  rw [hS1, hV1] at this
  simp at this
  linarith

/-! ## Spectral Laplacian Bound (Axiom)

The key spectral theory fact: for a connected `s`-regular graph, the Laplacian quadratic
form of the characteristic function of a proper nonempty subset `S` satisfies
`|δS| ≥ (s - λ₂) · |S| · (1 - |S|/|V|)`.

This combines Steps 1–4 of the proof:
- Step 1: Define `f = 1_S`, decompose `f = f̄·1 + g`
- Step 2: Spectral theorem gives `gᵀ(sI-M)g ≥ (s-λ₂)·gᵀg`
- Step 3: `gᵀg = |S|·(1 - |S|/|V|)`, and `fᵀ(sI-M)f = |δS|`
- Step 4: `gᵀ(sI-M)g = fᵀ(sI-M)f` since `(sI-M)·1 = 0`

The proof requires eigenvalue decomposition and the Courant–Fischer variational
characterization (not available in Mathlib), so this is stated as an axiom,
following the same convention as `cheegerInequalities` in Def_18. -/
axiom spectralLaplacianBound (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hcard : 2 ≤ Fintype.card V)
    (hconn : G.Connected) (hreg : G.IsRegularOfDegree s)
    (S : Finset V) (hS_pos : 0 < S.card) (hS_lt : S.card < Fintype.card V) :
    (s - secondLargestEigenvalue G hcard : ℝ) * S.card * (1 - S.card / Fintype.card V)
      ≤ (edgeBoundary G S).card

/-- Witness for `spectralLaplacianBound`: there exist `S` and `V` satisfying the hypotheses.
Any connected graph on ≥ 2 vertices has a proper nonempty subset. -/
lemma spectralLaplacianBound_satisfiable (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 2 ≤ Fintype.card V) (hconn : G.Connected) :
    ∃ S : Finset V, 0 < S.card ∧ S.card < Fintype.card V := by
  have hne := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  obtain ⟨v⟩ := hne
  exact ⟨{v}, by simp, by simp; omega⟩

/-! ## Step 5: Combining the bounds -/

/-- Helper: `|S|/|V| < α` when `|S| < α·|V|`. -/
lemma card_div_lt_alpha (S : Finset V) (α : ℝ) (hα0 : 0 < α)
    (hS_lt : (S.card : ℝ) < α * Fintype.card V)
    (hV : 0 < Fintype.card V) :
    (S.card : ℝ) / Fintype.card V < α := by
  rwa [div_lt_iff₀ (by exact_mod_cast hV : (0 : ℝ) < Fintype.card V)]

/-- Helper: `S.card < Fintype.card V` when `(S.card : ℝ) < α * Fintype.card V` and `α < 1`. -/
lemma card_lt_of_alpha (S : Finset V) (α : ℝ) (hα1 : α < 1)
    (hS_lt : (S.card : ℝ) < α * Fintype.card V) :
    S.card < Fintype.card V := by
  have : (S.card : ℝ) < 1 * Fintype.card V := by
    calc (S.card : ℝ) < α * Fintype.card V := hS_lt
    _ < 1 * Fintype.card V := by
      apply mul_lt_mul_of_pos_right hα1
      exact_mod_cast Nat.pos_of_ne_zero (by
        intro h
        simp [h] at hS_lt
        linarith [show (0 : ℝ) ≤ S.card from Nat.cast_nonneg _])
  rw [one_mul] at this
  exact_mod_cast this

/-! ## Main Theorem -/

/-- **Relative Cheeger Inequality.** For a finite, connected, `s`-regular graph with
second-largest eigenvalue `λ₂`, and for `α ∈ (0, 1)` and `S ⊆ V` with
`0 < |S| < α|V|`, we have `(1 - α)(s - λ₂) ≤ |δS| / |S|`.

This follows from the spectral Laplacian bound:
`|δS| ≥ (s - λ₂) · |S| · (1 - |S|/|V|) > (s - λ₂) · |S| · (1 - α)`
since `|S|/|V| < α`, and then dividing by `|S| > 0`. -/
theorem relativeCheeger (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hconn : G.Connected) (hreg : G.IsRegularOfDegree s)
    (S : Finset V) (hS_pos : 0 < S.card)
    (hS_lt : (S.card : ℝ) < α * Fintype.card V) :
    let hcard := card_ge_two_of_subset S α hα1 hS_pos hS_lt
    (1 - α) * (s - secondLargestEigenvalue G hcard) ≤
      (edgeBoundary G S).card / S.card := by
  intro hcard
  have hS_pos_real : (0 : ℝ) < S.card := by exact_mod_cast hS_pos
  have hV_pos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast (show 0 < Fintype.card V by omega)
  have hS_proper : S.card < Fintype.card V := card_lt_of_alpha S α hα1 hS_lt
  have h_ratio : (S.card : ℝ) / Fintype.card V < α :=
    card_div_lt_alpha S α hα0 hS_lt (by exact_mod_cast (show 0 < Fintype.card V by omega))
  have h_complement : 1 - α < 1 - (S.card : ℝ) / Fintype.card V := by linarith
  have h_one_minus_alpha_pos : (0 : ℝ) < 1 - α := by linarith
  -- Key spectral bound
  have h_spectral := spectralLaplacianBound G s hcard hconn hreg S hS_pos hS_proper
  -- Edge boundary card is nonneg
  have h_boundary_nonneg : (0 : ℝ) ≤ ((edgeBoundary G S).card : ℝ) := Nat.cast_nonneg _
  -- 1 - |S|/|V| > 0
  have h_compl_pos : (0 : ℝ) < 1 - (S.card : ℝ) / Fintype.card V := by
    rw [sub_pos, div_lt_one hV_pos]; exact_mod_cast hS_proper
  -- Case split on sign of (s - λ₂)
  by_cases h_gap : (0 : ℝ) ≤ ↑s - secondLargestEigenvalue G hcard
  · -- Case (s - λ₂) ≥ 0: use the spectral bound chain
    rw [le_div_iff₀ hS_pos_real]
    calc (1 - α) * (↑s - secondLargestEigenvalue G hcard) * ↑(S.card)
        = (↑s - secondLargestEigenvalue G hcard) * ↑(S.card) * (1 - α) := by ring
      _ ≤ (↑s - secondLargestEigenvalue G hcard) * ↑(S.card) *
            (1 - ↑(S.card) / ↑(Fintype.card V)) := by
          apply mul_le_mul_of_nonneg_left (le_of_lt h_complement)
          exact mul_nonneg h_gap (le_of_lt hS_pos_real)
      _ ≤ ↑((edgeBoundary G S).card) := h_spectral
  · -- Case (s - λ₂) < 0: (1-α)*(s-λ₂) < 0 ≤ |δS|/|S|, trivial
    push_neg at h_gap
    have : (1 - α) * (↑s - secondLargestEigenvalue G hcard) < 0 :=
      mul_neg_of_pos_of_neg h_one_minus_alpha_pos h_gap
    calc (1 - α) * (↑s - secondLargestEigenvalue G hcard)
        ≤ 0 := le_of_lt this
      _ ≤ ↑((edgeBoundary G S).card) / ↑(S.card) :=
          div_nonneg (Nat.cast_nonneg _) (le_of_lt hS_pos_real)

end RelativeCheeger
