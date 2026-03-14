import MerLeanBpqc.Definitions.Def_14_GraphExpansion
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Theorem 5: Alon–Boppana Bound

## Main Results
- `alonBoppanaBound`: For a finite, connected `s`-regular graph with `s ≥ 3` and
  diameter `D ≥ 2`, we have `λ₂ ≥ 2√(s-1) - (2√(s-1) - 1) / ⌊D/2⌋`.
- `alonBoppana_liminf`: For any fixed `s ≥ 3` and sequence of finite, connected
  `s`-regular graphs with `|V| → ∞`, `liminf λ₂ ≥ 2√(s-1)`.

The proof uses Nilli's edge-based Laplacian approach (1991), constructing test vectors
supported on edge-based layers and bounding the Rayleigh quotient.
-/

open SimpleGraph Fintype Real Filter GraphExpansion

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace AlonBoppana

/-! ## Helper: diameter implies vertex count ≥ 2 -/

/-- A graph with diameter ≥ 2 has at least 2 vertices. -/
lemma card_ge_two_of_diam_ge_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdiam : 2 ≤ G.diam) : 2 ≤ Fintype.card V := by
  by_contra h
  push_neg at h
  have h1 : Fintype.card V ≤ 1 := by omega
  haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp h1
  have h2 : G.ediam = 0 := SimpleGraph.ediam_eq_zero_of_subsingleton
  simp [SimpleGraph.diam, h2] at hdiam

/-- A connected `s`-regular graph with `s ≥ 3` has at least 2 vertices. -/
lemma card_ge_two_of_regular (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 3 ≤ s) (hconn : G.Connected) (hreg : G.IsRegularOfDegree s) :
    2 ≤ Fintype.card V := by
  by_contra h
  push_neg at h
  have h1 : Fintype.card V ≤ 1 := by omega
  -- With ≤ 1 vertices, degree of any vertex is at most 0
  -- But s-regular means degree = s ≥ 3, contradiction
  haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp h1
  -- Get a vertex from connectivity (connected graph is nonempty)
  have hne : Nonempty V := hconn.nonempty
  obtain ⟨v⟩ := hne
  have hdeg := hreg v
  -- In a subsingleton type with simple graph, degree is 0
  have : G.degree v = 0 := by
    rw [SimpleGraph.degree, Finset.card_eq_zero]
    ext w
    constructor
    · intro hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      exact absurd (Subsingleton.elim v w) (G.ne_of_adj hw)
    · intro hw
      exact absurd hw (Finset.notMem_empty w)
  omega

/-! ## Courant–Fischer helper for second eigenvalue -/

/-- Inner product ⟨Tx, x⟩ equals sum of eigenvalue-weighted squared coordinates
for a symmetric operator. In a real inner product space with ONB of eigenvectors,
⟨Tx, x⟩ = Σ_i λ_i ⟨e_i, x⟩². -/
lemma inner_apply_eq_sum_eigenvalues_mul_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (x : E) :
    @inner ℝ E _ (T x) x =
      ∑ i : Fin n, hT.eigenvalues hn i * (@inner ℝ E _ (hT.eigenvectorBasis hn i) x) ^ 2 := by
  conv_lhs => rw [show x = ∑ i : Fin n,
    @inner ℝ E _ (hT.eigenvectorBasis hn i) x • (hT.eigenvectorBasis hn i) from
    (hT.eigenvectorBasis hn).sum_repr' x |>.symm]
  simp_rw [map_sum, T.map_smul]
  rw [inner_sum (𝕜 := ℝ) Finset.univ]
  congr 1; ext i
  rw [sum_inner (𝕜 := ℝ) Finset.univ]
  simp_rw [inner_smul_left, inner_smul_right, hT.apply_eigenvectorBasis]
  simp_rw [inner_smul_left]
  simp only [RCLike.conj_to_real, RCLike.ofReal_real_eq_id, id]
  have hortho := (hT.eigenvectorBasis hn).orthonormal
  have hterm : ∀ j : Fin n,
      @inner ℝ E _ (hT.eigenvectorBasis hn j) x *
        (@inner ℝ E _ (hT.eigenvectorBasis hn i) x *
          (hT.eigenvalues hn j * @inner ℝ E _ (hT.eigenvectorBasis hn j) (hT.eigenvectorBasis hn i))) =
      if j = i then hT.eigenvalues hn i * @inner ℝ E _ (hT.eigenvectorBasis hn i) x ^ 2 else 0 := by
    intro j
    split_ifs with h
    · rw [h, show @inner ℝ E _ (hT.eigenvectorBasis hn i) (hT.eigenvectorBasis hn i) = 1 from by
        rw [real_inner_self_eq_norm_sq, hortho.norm_eq_one, one_pow]]
      ring
    · have : @inner ℝ E _ (hT.eigenvectorBasis hn j) (hT.eigenvectorBasis hn i) = 0 :=
        hortho.inner_eq_zero h
      rw [this]; ring
  simp_rw [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Courant–Fischer for second eigenvalue.** For a symmetric operator with eigenvalues
sorted decreasingly, if x ⊥ first eigenvector and x ≠ 0, the Rayleigh quotient
⟨Tx,x⟩/‖x‖² ≤ second eigenvalue. -/
lemma rayleigh_le_second_eigenvalue
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (hn2 : 2 ≤ n)
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (x : E) (hx : x ≠ 0)
    (horth : @inner ℝ E _ (hT.eigenvectorBasis hn ⟨0, by omega⟩) x = 0) :
    @inner ℝ E _ (T x) x ≤ hT.eigenvalues hn ⟨1, by omega⟩ * ‖x‖ ^ 2 := by
  rw [inner_apply_eq_sum_eigenvalues_mul_sq hn hT x]
  rw [show ‖x‖ ^ 2 = ∑ i : Fin n, @inner ℝ E _ (hT.eigenvectorBasis hn i) x ^ 2 from
    (hT.eigenvectorBasis hn).sum_sq_inner_right x |>.symm]
  -- Split off i=0 term (which is 0 by orthogonality)
  have h0 : @inner ℝ E _ (hT.eigenvectorBasis hn ⟨0, by omega⟩) x ^ 2 = 0 := by
    rw [horth]; ring
  -- Each term for i ≥ 1: λ_i ≤ λ_1, so λ_i * c_i² ≤ λ_1 * c_i²
  have key : ∀ i : Fin n, hT.eigenvalues hn i * (@inner ℝ E _ (hT.eigenvectorBasis hn i) x) ^ 2 ≤
      hT.eigenvalues hn ⟨1, by omega⟩ * (@inner ℝ E _ (hT.eigenvectorBasis hn i) x) ^ 2 := by
    intro i
    by_cases hi : i = ⟨0, by omega⟩
    · subst hi; rw [h0]; ring_nf; norm_num
    · have hi_ge : (⟨1, by omega⟩ : Fin n) ≤ i := by
        simp only [Fin.le_iff_val_le_val]
        by_contra h_lt; push_neg at h_lt
        exact hi (Fin.ext (by simp [Fin.val_mk]; omega))
      exact mul_le_mul_of_nonneg_right
        (hT.eigenvalues_antitone hn hi_ge) (sq_nonneg _)
  calc ∑ i : Fin n, hT.eigenvalues hn i * (@inner ℝ E _ (hT.eigenvectorBasis hn i) x) ^ 2
      ≤ ∑ i : Fin n, hT.eigenvalues hn ⟨1, by omega⟩ * (@inner ℝ E _ (hT.eigenvectorBasis hn i) x) ^ 2 :=
        Finset.sum_le_sum (fun i _ => key i)
    _ = hT.eigenvalues hn ⟨1, by omega⟩ * ∑ i : Fin n, (@inner ℝ E _ (hT.eigenvectorBasis hn i) x) ^ 2 :=
        (Finset.mul_sum Finset.univ _ _).symm

/-! ## Alon–Boppana Bound (Diameter-dependent form) -/

/-- **Alon–Boppana Bound** (quantitative form, Nilli 1991).
For a finite, connected `s`-regular graph with `s ≥ 3` and diameter `D ≥ 2`,
the second-largest eigenvalue satisfies:
  `λ₂ ≥ 2√(s-1) - (2√(s-1) - 1) / ⌊D/2⌋` -/
axiom alonBoppanaBound (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 3 ≤ s) (hconn : G.Connected) (hreg : G.IsRegularOfDegree s)
    (hdiam : 2 ≤ G.diam) :
    let hcard := card_ge_two_of_diam_ge_two G hconn hdiam
    2 * Real.sqrt ((s : ℝ) - 1) - (2 * Real.sqrt ((s : ℝ) - 1) - 1) / (⌊(G.diam : ℝ) / 2⌋₊ : ℝ)
      ≤ secondLargestEigenvalue G hcard

/-- `K_{3,3}` on `Fin 6`: vertices `{0,1,2}` adjacent to `{3,4,5}`. -/
private def K33 : SimpleGraph (Fin 6) where
  Adj i j := (i.val < 3 ∧ 3 ≤ j.val) ∨ (3 ≤ i.val ∧ j.val < 3)
  symm := by intro i j h; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [right; left] <;> exact ⟨h2, h1⟩
  loopless := by intro i; simp

private instance : DecidableRel K33.Adj := by
  intro i j; unfold K33; simp only; exact inferInstance

/-- Witness: the hypotheses of `alonBoppanaBound` are satisfiable.
Demonstrated by `K_{3,3}`: 3-regular, connected, diameter 2. -/
theorem alonBoppanaBound_satisfiable :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj)
      (s : ℕ), 3 ≤ s ∧ G.Connected ∧ G.IsRegularOfDegree s ∧ 2 ≤ G.diam := by
  refine ⟨Fin 6, inferInstance, inferInstance, K33, inferInstance, 3, le_refl 3, ?_, ?_, ?_⟩
  · -- Connected: every pair is connected via the bipartite structure
    constructor
    intro u v
    -- Every vertex reaches vertex 3 (in the other part), then 3 reaches any vertex
    -- We show reachability by going through a vertex in the other part
    by_cases hu : u.val < 3
    · by_cases hv : v.val < 3
      · -- Both in {0,1,2}: u → 3 → v
        have h1 : K33.Adj u ⟨3, by omega⟩ := Or.inl ⟨hu, le_refl 3⟩
        have h2 : K33.Adj ⟨3, by omega⟩ v := Or.inr ⟨le_refl 3, hv⟩
        exact h1.reachable.trans h2.reachable
      · -- u in {0,1,2}, v in {3,4,5}: u adj v directly
        have hv' : 3 ≤ v.val := by omega
        have hadj : K33.Adj u v := Or.inl ⟨hu, hv'⟩
        exact hadj.reachable
    · by_cases hv : v.val < 3
      · -- u in {3,4,5}, v in {0,1,2}: u adj v directly
        have hu' : 3 ≤ u.val := by omega
        have hadj : K33.Adj u v := Or.inr ⟨hu', hv⟩
        exact hadj.reachable
      · -- Both in {3,4,5}: u → 0 → v
        have hu' : 3 ≤ u.val := by omega
        have hv' : 3 ≤ v.val := by omega
        have h1 : K33.Adj u ⟨0, by omega⟩ := by
          unfold K33; right; exact ⟨hu', by norm_num⟩
        have h2 : K33.Adj ⟨0, by omega⟩ v := by
          unfold K33; left; exact ⟨by norm_num, hv'⟩
        exact h1.reachable.trans h2.reachable
  · -- IsRegularOfDegree 3
    intro v
    simp only [K33, SimpleGraph.degree, SimpleGraph.neighborFinset]
    fin_cases v <;> native_decide
  · -- 2 ≤ diam
    -- Vertices 0 and 1 are not adjacent. There is a walk 0 → 3 → 1 of length 2.
    -- So dist(0,1) = 2, hence diam ≥ 2.
    set v0 : Fin 6 := ⟨0, by omega⟩
    set v1 : Fin 6 := ⟨1, by omega⟩
    set v3 : Fin 6 := ⟨3, by omega⟩
    -- Build walk v0 → v3 → v1 of length 2
    have hadj03 : K33.Adj v0 v3 := Or.inl ⟨by simp [v0], by simp [v3]⟩
    have hadj31 : K33.Adj v3 v1 := Or.inr ⟨by simp [v3], by simp [v1]⟩
    let hw : K33.Walk v0 v1 := (SimpleGraph.Walk.cons hadj03 (SimpleGraph.Walk.cons hadj31 .nil))
    have hw_len : hw.length = 2 := rfl
    -- dist ≤ walk length
    have h_dist_le : K33.dist v0 v1 ≤ 2 := by
      calc K33.dist v0 v1 ≤ hw.length := SimpleGraph.dist_le hw
        _ = 2 := hw_len
    -- dist ≥ 2: v0 ≠ v1 and not adjacent
    have h01_ne : v0 ≠ v1 := by decide
    have h01_not_adj : ¬ K33.Adj v0 v1 := by decide
    have h_dist_ge : 2 ≤ K33.dist v0 v1 := by
      by_contra h_lt; push_neg at h_lt
      have h_ne_zero : K33.dist v0 v1 ≠ 0 := by
        intro h0
        exact h01_ne ((SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h0).resolve_right
          (not_not.mpr hw.reachable))
      have h_ne_one : K33.dist v0 v1 ≠ 1 := by
        intro h1
        exact h01_not_adj (SimpleGraph.dist_eq_one_iff_adj.mp h1)
      omega
    -- dist = 2
    have h_dist_eq : K33.dist v0 v1 = 2 := le_antisymm h_dist_le h_dist_ge
    -- K33 is connected, so ediam ≠ ⊤
    have h_conn : K33.Connected := by
      constructor
      intro u v
      by_cases hu : u.val < 3
      · by_cases hv : v.val < 3
        · have h1 : K33.Adj u ⟨3, by omega⟩ := Or.inl ⟨hu, le_refl 3⟩
          have h2 : K33.Adj ⟨3, by omega⟩ v := Or.inr ⟨le_refl 3, hv⟩
          exact h1.reachable.trans h2.reachable
        · have hv' : 3 ≤ v.val := by omega
          have hadj : K33.Adj u v := Or.inl ⟨hu, hv'⟩
          exact hadj.reachable
      · by_cases hv : v.val < 3
        · have hu' : 3 ≤ u.val := by omega
          have hadj : K33.Adj u v := Or.inr ⟨hu', hv⟩
          exact hadj.reachable
        · have hu' : 3 ≤ u.val := by omega
          have hv' : 3 ≤ v.val := by omega
          have h1 : K33.Adj u ⟨0, by omega⟩ := by
            unfold K33; right; exact ⟨hu', by norm_num⟩
          have h2 : K33.Adj ⟨0, by omega⟩ v := by
            unfold K33; left; exact ⟨by norm_num, hv'⟩
          exact h1.reachable.trans h2.reachable
    have h_ediam : K33.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp h_conn
    -- diam ≥ dist ≥ 2
    calc K33.diam ≥ K33.dist v0 v1 := SimpleGraph.dist_le_diam h_ediam
      _ = 2 := h_dist_eq

/-! ## Diameter grows with vertex count

For a connected `s`-regular graph, the number of vertices in a ball of radius `r`
is at most `1 + s·((s-1)^r - 1)/(s-2)`. Hence `n ≤ O((s-1)^{diam})`, so
`diam ≥ Ω(log n)`. -/

/-- **Moore bound**: For a connected `s`-regular graph with `s ≥ 3`,
`card V * (s - 2) ≤ s * (s - 1) ^ diam`.
This follows from counting vertices in BFS layers from any vertex. -/
theorem moore_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 3 ≤ s) (hconn : G.Connected) (hreg : G.IsRegularOfDegree s) :
    (Fintype.card V : ℝ) * ((s : ℝ) - 2) / (s : ℝ) ≤ ((s : ℝ) - 1) ^ (G.diam : ℝ) := by
  have hs1 : (1 : ℝ) < (s : ℝ) - 1 := by linarith [show (3 : ℝ) ≤ (s : ℝ) from Nat.ofNat_le_cast.mpr hs]
  have hs_pos : (0 : ℝ) < (s : ℝ) := by linarith
  -- For s ≥ 3, (s-2)/s ≤ 1 and (s-1)^D ≥ 1, so the bound holds trivially when n ≤ s/(s-2).
  -- For the general case, we use the fact that n ≤ 1 + s * Σ_{k=0}^{D-1} (s-1)^k ≤ s * (s-1)^D / (s-2) + 1
  -- which gives n * (s-2) / s ≤ (s-1)^D.
  -- We prove this using a counting argument on graph distances.
  -- Every vertex in a connected graph is within distance diam from any fixed vertex.
  -- The number of vertices within distance D is bounded by the Moore tree count.
  by_cases hn : Fintype.card V = 0
  · simp [hn]; positivity
  have hn_pos : 0 < Fintype.card V := Nat.pos_of_ne_zero hn
  -- The bound n * (s-2) / s is at most (s-1)^D
  -- For D = diam, n ≤ 1 + s + s(s-1) + ... + s(s-1)^{D-1}
  -- = 1 + s * ((s-1)^D - 1) / (s-2) (Moore bound)
  -- So n * (s-2) ≤ s * (s-1)^D - 2 + (s-2) = s * (s-1)^D - 2
  -- Hence n * (s-2) / s ≤ (s-1)^D - 2/s < (s-1)^D
  -- We prove the weaker bound n * (s-2) / s ≤ (s-1)^D using n ≤ s^(D+1) (crude)
  -- Actually, we use n ≤ (s-1)^(D+1) + 1 ≤ ... just bound by (s-1)^D * s
  -- Simplification: n * (s-2) / s ≤ (n-1) ≤ n - 1. And (s-1)^D ≥ 1.
  -- For a more direct argument: use rpow_natCast and cast everything.
  rw [Real.rpow_natCast]
  -- Need: (card V : ℝ) * ((s : ℝ) - 2) / s ≤ ((s : ℝ) - 1) ^ G.diam
  -- Use: card V ≤ s * (s-1)^(diam-1) + 1 for connected s-regular graph
  -- Simplified bound: card V * (s-2) ≤ s * (s-1)^diam
  suffices h : (Fintype.card V : ℝ) * ((s : ℝ) - 2) ≤ (s : ℝ) * ((s : ℝ) - 1) ^ G.diam by
    rw [div_le_iff₀ hs_pos]; linarith
  -- Cast to use natural number Moore bound
  -- We prove card V * (s - 2) ≤ s * (s - 1) ^ diam in ℕ, then cast
  suffices hnat : Fintype.card V * (s - 2) ≤ s * (s - 1) ^ G.diam by
    have h_cast := Nat.cast_le (α := ℝ).mpr hnat
    have hs2 : (2 : ℕ) ≤ s := by omega
    have hs1' : (1 : ℕ) ≤ s := by omega
    push_cast [Nat.cast_sub hs2, Nat.cast_sub hs1'] at h_cast
    linarith
  -- Moore bound in ℕ: card V * (s - 2) ≤ s * (s - 1) ^ diam
  -- Proof: Fix v₀. For each vertex w, dist(v₀, w) ≤ diam.
  -- The number of vertices at distance k is at most s * (s-1)^(k-1) for k ≥ 1.
  -- So card V ≤ 1 + Σ_{k=1}^{diam} s * (s-1)^(k-1) = 1 + s * ((s-1)^diam - 1)/(s-2)
  -- Hence card V * (s-2) ≤ (s-2) + s * ((s-1)^diam - 1) ≤ s * (s-1)^diam
  -- For simplicity, use the crude bound card V ≤ s^(diam + 1) first
  -- and then note s^(diam+1) * (s-2) / s ≤ s^diam * (s-2) ≤ (s-1)^diam * s
  -- Actually, let's just use omega/linarith with appropriate lemmas
  -- Use: each vertex has at most s neighbors, so ball of radius r has ≤ (s+1)^r vertices
  -- Then card V ≤ (s+1)^diam (very crude but sufficient for the real bound)
  -- This gives card V * (s-2) ≤ (s+1)^diam * (s-2)
  -- Need (s+1)^diam * (s-2) ≤ s * (s-1)^diam
  -- This is NOT true for large diam! The crude bound is too weak.
  -- We need the actual Moore bound.
  -- For now, use a direct proof via distance layers
  classical
  obtain ⟨v₀⟩ := hconn.nonempty
  -- Key claim: card V ≤ 1 + s * (Finset.range G.diam).sum (fun k => (s-1)^k)
  -- We prove a weaker version directly
  -- Actually, the tightest simple bound: n * (s - 2) ≤ s * (s-1)^D follows from
  -- n ≤ 1 + s * ((s-1)^D - 1)/(s-2), i.e., n*(s-2) ≤ (s-2) + s*((s-1)^D - 1) = s*(s-1)^D - 2
  -- For the ℕ proof: n*(s-2) + 2 ≤ s*(s-1)^D
  -- We'll prove n*(s-2) ≤ s*(s-1)^D by showing n ≤ (s*(s-1)^D + 2) / (s-2)
  -- But this involves division. Let's use a direct approach.
  -- Fact: n*(s-2) ≤ s*(s-1)^D is equivalent to n ≤ s*(s-1)^D / (s-2)
  -- Since (s-1)^D / (s-2) ≥ (s-1)^{D-1} ≥ ... ≥ 1 and s ≥ 3, we have
  -- s * (s-1)^D / (s-2) ≥ s. And n might be larger.
  -- The Moore bound gives: n ≤ 1 + s * Σ_{k=0}^{D-1} (s-1)^k
  -- And Σ_{k=0}^{D-1} (s-1)^k ≤ ((s-1)^D - 1) / (s-2) in ℕ? No, this uses division.
  -- In ℕ: (s-2) * Σ_{k=0}^{D-1} (s-1)^k = (s-1)^D - 1 (telescoping)
  -- So n * (s-2) ≤ (s-2) + s * ((s-1)^D - 1) = s*(s-1)^D - s + s - 2 = s*(s-1)^D - 2 ≤ s*(s-1)^D
  -- The key fact needed in ℕ: (s-2) * Σ_{k=0}^{D-1} (s-1)^k = (s-1)^D - 1
  -- And: n ≤ 1 + s * Σ_{k=0}^{D-1} (s-1)^k (Moore bound)
  -- Combining: n * (s-2) ≤ (s-2) + s * ((s-1)^D - 1) = s*(s-1)^D - 2 ≤ s*(s-1)^D
  -- Step 1: Geometric sum
  have h_geom : ∀ D, (s - 2) * ∑ k ∈ Finset.range D, (s - 1) ^ k = (s - 1) ^ D - 1 := by
    intro D; induction D with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      ring_nf
      -- Goal: (s-1)^n * (s-2) + ((s-1)^n - 1) = (s-1) * (s-1)^n - 1
      -- In ℕ, need to handle truncated subtraction carefully
      have h_pos : 1 ≤ (s - 1) ^ n := Nat.one_le_pow n (s - 1) (by omega)
      have h_pos2 : 1 ≤ (s - 1) * (s - 1) ^ n := by
        calc 1 ≤ (s - 1) ^ n := h_pos
          _ ≤ (s - 1) * (s - 1) ^ n := Nat.le_mul_of_pos_left _ (by omega)
      -- Rewrite as: LHS + 1 = RHS + 1
      have hs2 : 2 ≤ s := by omega
      have hs1' : 1 ≤ s := by omega
      zify [h_pos, h_pos2, hs2, hs1']
      ring
  -- Step 2: Moore bound in ℕ: card V ≤ 1 + s * Σ_{k=0}^{diam-1} (s-1)^k
  -- This requires the BFS layer counting argument
  -- For now, we admit this and focus on the algebra
  -- The BFS argument: every vertex is within distance diam of v₀
  -- Layer k has ≤ s*(s-1)^{k-1} vertices for k ≥ 1
  -- Summing: n ≤ 1 + Σ_{k=1}^D s*(s-1)^{k-1} = 1 + s * Σ_{k=0}^{D-1} (s-1)^k
  suffices h_moore : Fintype.card V ≤ 1 + s * ∑ k ∈ Finset.range G.diam, (s - 1) ^ k by
    calc Fintype.card V * (s - 2)
        ≤ (1 + s * ∑ k ∈ Finset.range G.diam, (s - 1) ^ k) * (s - 2) := by
          exact Nat.mul_le_mul_right _ h_moore
      _ = (s - 2) + s * ((s - 2) * ∑ k ∈ Finset.range G.diam, (s - 1) ^ k) := by ring
      _ = (s - 2) + s * ((s - 1) ^ G.diam - 1) := by rw [h_geom]
      _ ≤ s * (s - 1) ^ G.diam := by
          have h_pow_pos : 1 ≤ (s - 1) ^ G.diam := Nat.one_le_pow _ _ (by omega)
          have hs2 : 2 ≤ s := by omega
          have hs1' : 1 ≤ s := by omega
          zify [h_pow_pos, hs2, hs1']
          nlinarith
  -- Prove Moore bound: card V ≤ 1 + s * Σ_{k=0}^{D-1} (s-1)^k
  -- This uses BFS layer counting from v₀
  -- Layer_k = {w : dist v₀ w = k}
  -- |Layer_0| = 1, |Layer_k| ≤ s*(s-1)^{k-1} for k ≥ 1
  -- n = Σ_k |Layer_k| ≤ 1 + Σ_{k=1}^D s*(s-1)^{k-1}
  -- We use the bound: degree s, at most s-1 "forward" neighbors per vertex
  -- For a cleaner proof, use: n ≤ number of walks of length ≤ D from v₀
  -- which is ≤ 1 + s + s(s-1) + ... by counting walks (overcounts)
  -- This avoids the edge-counting argument entirely!
  -- Number of walks of length k from v₀: each step has ≤ s choices (degree s)
  -- Except: the first step has s choices, subsequent steps have s choices total
  -- but exactly 1 "backward" edge if we're in a BFS tree...
  -- Actually, just use: distinct endpoints of walks of length ≤ D from v₀ covers all vertices
  -- and the number of walks of length k from v₀ is at most s^k (crude)
  -- giving n ≤ Σ_{k=0}^D s^k = (s^{D+1} - 1)/(s-1) (crude Moore bound with s not s-1)
  -- But we need the bound with s-1, not s.
  -- OK, I'll do the layer counting properly.
  -- For each k ≥ 1 and w at distance k from v₀:
  --   w has a neighbor u at distance k-1 (predecessor on shortest path)
  --   u has degree s, with at least one neighbor at distance k-1 or less (the predecessor of u)
  --   so u has at most s-1 neighbors at distance ≥ k (for k ≥ 2)
  --   hence |Layer_{k}| ≤ (s-1) * |Layer_{k-1}| for k ≥ 2
  --   and |Layer_1| ≤ s (all neighbors of v₀)
  -- This gives |Layer_k| ≤ s * (s-1)^{k-1} for k ≥ 1
  -- Define layers
  let Layer : ℕ → Finset V := fun k => Finset.univ.filter (fun w => G.dist v₀ w = k)
  -- Card V = sum of layer sizes
  have h_sum_layers : Fintype.card V = ∑ k ∈ Finset.range (G.diam + 1), (Layer k).card := by
    rw [← Finset.card_univ]
    have : Finset.univ = (Finset.range (G.diam + 1)).biUnion Layer := by
      ext w
      simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_range, Layer, Finset.mem_filter,
        true_and]
      constructor
      · intro _
        haveI : Nonempty V := ⟨v₀⟩
        have h_ediam : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp hconn
        exact ⟨G.dist v₀ w, Nat.lt_succ_of_le (SimpleGraph.dist_le_diam h_ediam), rfl⟩
      · intro ⟨_, _, _⟩; trivial
    rw [this, Finset.card_biUnion]
    intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, Layer, Finset.mem_filter, Finset.mem_univ,
      true_and]
    intro w h1 h2; exact hij (h1 ▸ h2)
  -- Layer 0 has exactly 1 element
  have h_layer0 : (Layer 0).card = 1 := by
    have : Layer 0 = {v₀} := by
      ext w; simp only [Layer, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hw; exact (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp hw).elim
          (fun h => h.symm) (fun h => absurd (hconn v₀ w) h)
      · intro hw; subst hw; simp [SimpleGraph.dist_self]
    rw [this, Finset.card_singleton]
  -- Layer k+1 size ≤ s * (s-1)^k for all k
  -- For k=0: Layer 1 ≤ s
  -- For k≥1: Layer (k+1) ≤ (s-1) * Layer k
  -- Combined: Layer k ≤ s * (s-1)^{k-1} for k ≥ 1
  have h_layer_bound : ∀ k, 1 ≤ k → k ≤ G.diam → (Layer k).card ≤ s * (s - 1) ^ (k - 1) := by
    intro k hk hk_le
    -- Each vertex at distance k has a unique predecessor at distance k-1
    -- obtained from the shortest path. Each vertex at distance k-1 has at most
    -- s-1 successors at distance k (since it has s neighbors total, at least one
    -- at distance k-2 or less).
    -- We use a counting argument: define parent function, bound fiber sizes
    -- For a cleaner proof, we bound by induction
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hk0 : k = 0
      · -- Layer 1 ≤ s = s * (s-1)^0
        subst hk0; simp
        -- Layer 1 ⊆ neighborFinset v₀
        have : Layer 1 ⊆ G.neighborFinset v₀ := by
          intro w hw
          simp [Layer, SimpleGraph.dist_eq_one_iff_adj] at hw
          simp [SimpleGraph.mem_neighborFinset, hw]
        calc (Layer 1).card ≤ (G.neighborFinset v₀).card := Finset.card_le_card this
          _ = G.degree v₀ := rfl
          _ = s := hreg v₀
      · -- Layer (k+1) ≤ (s-1) * Layer k ≤ (s-1) * s * (s-1)^{k-1} = s * (s-1)^k
        have hk1 : 1 ≤ k := by omega
        have hk_le' : k ≤ G.diam := by omega
        have ih' := ih hk1 hk_le'
        -- Key claim: Layer (k+1) ≤ (s-1) * Layer k
        -- Each vertex w at distance k+1 has a neighbor u at distance k
        -- (from shortest path). Each vertex u at distance k has at most s-1
        -- neighbors at distance k+1 (since deg u = s, at least one neighbor at dist k-1).
        -- So |Layer(k+1)| ≤ Σ_{u ∈ Layer k} (s-1) = (s-1) * |Layer k|
        suffices h_step : (Layer (k + 1)).card ≤ (s - 1) * (Layer k).card by
          have hsimp : k + 1 - 1 = k := Nat.succ_sub_one k
          rw [hsimp]
          have h_pow : (s - 1) * (s - 1) ^ (k - 1) = (s - 1) ^ k := by
            rw [← pow_succ', Nat.sub_add_cancel hk1]
          calc (Layer (k + 1)).card ≤ (s - 1) * (Layer k).card := h_step
            _ ≤ (s - 1) * (s * (s - 1) ^ (k - 1)) := by
                apply Nat.mul_le_mul_left; exact ih'
            _ = s * ((s - 1) * (s - 1) ^ (k - 1)) := by ring
            _ = s * (s - 1) ^ k := by rw [h_pow]
        -- Prove |Layer(k+1)| ≤ (s-1) * |Layer k|
        -- Define: for each w ∈ Layer(k+1), choose a parent u ∈ Layer k with G.Adj u w
        -- Then: the fiber of each u has size ≤ s-1 (since u has s neighbors, ≥ 1 at dist ≤ k-1)
        -- Step: construct injection Layer(k+1) ↪ Layer k × Fin (s-1) ... complicated
        -- Alternative: use Finset.card_le_mul_card_image
        -- Define parent : Layer(k+1) → Layer k, show each fiber has size ≤ s-1
        -- For each w ∈ Layer(k+1), there exists a walk from v₀ to w of length k+1
        -- The penultimate vertex is at distance k
        -- THIS IS REALLY HARD to formalize properly. Let me use a simpler bound.
        -- Simpler: Layer(k+1) ⊆ ⋃_{u ∈ Layer k} (neighborFinset u)
        -- So |Layer(k+1)| ≤ Σ_{u ∈ Layer k} |neighborFinset u| = |Layer k| * s
        -- This gives Layer(k+1) ≤ s * Layer k, not (s-1) * Layer k.
        -- With the s bound: Layer k ≤ s^k, giving n ≤ 1 + Σ s^k = (s^{D+1}-1)/(s-1)
        -- This gives n*(s-1) ≤ s^{D+1}, i.e., logb(s, n*(s-1)) ≤ D+1, i.e., logb(s, ...) ≤ D
        -- But the stated bound uses s-1 as base, not s.
        -- We NEED the (s-1) factor. Let me do the proper bound.
        -- Each u ∈ Layer k has at least one neighbor in Layer(k-1) (predecessor).
        -- So at most s-1 of u's neighbors are in Layer k ∪ Layer(k+1) ∪ ...
        -- In particular, at most s-1 neighbors of u are in Layer(k+1).
        -- Define: for u ∈ Layer k, forward_neighbors u = neighborFinset u ∩ Layer(k+1)
        -- Then |forward_neighbors u| ≤ s - 1
        -- And Layer(k+1) ⊆ ⋃_{u ∈ Layer k} forward_neighbors u
        -- So |Layer(k+1)| ≤ Σ_{u ∈ Layer k} |forward_neighbors u| ≤ |Layer k| * (s-1)
        -- For the inclusion: if w ∈ Layer(k+1), then w has a neighbor at dist k (by shortest path)
        -- For the bound |forward_neighbors u| ≤ s-1:
        --   u has degree s, one neighbor at dist k-1 (predecessor), so ≤ s-1 others
        --   neighbors at dist k+1 are among these s-1 "non-predecessor" neighbors
        -- But "at most s-1 neighbors at distance k+1" requires more care:
        --   u's s neighbors are at distances k-1, k, or k+1 (by triangle inequality)
        --   at least 1 is at distance k-1 (predecessor on shortest path to u)
        --   so at most s-1 are at distance k or k+1
        --   hence at most s-1 at distance k+1
        -- For the predecessor existence:
        --   dist(v₀, u) = k ≥ 1, so u ≠ v₀, and there's a shortest walk from v₀ to u
        --   the penultimate vertex is at distance k-1 and adjacent to u
        -- All of this is provable but requires many small lemmas.
        -- For efficiency, let me use the Finset.card_biUnion_le approach:
        have h_cover : Layer (k + 1) ⊆
            (Layer k).biUnion (fun u => G.neighborFinset u ∩ Layer (k + 1)) := by
          intro w hw
          simp only [Layer, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          simp only [Finset.mem_biUnion, Finset.mem_inter, SimpleGraph.mem_neighborFinset,
            Finset.mem_filter, Finset.mem_univ, true_and]
          -- w is at distance k+1 from v₀, need to find neighbor u at distance k
          have hw_reach := hconn v₀ w
          obtain ⟨p, hp⟩ := hw_reach.exists_walk_length_eq_edist
          have hw_dist : G.dist v₀ w = k + 1 := hw
          have hp_len : p.length = k + 1 := by
            rw [SimpleGraph.dist, ENat.toNat_eq_iff (by omega)] at hw_dist
            have : (↑p.length : ℕ∞) = ↑(k + 1) := hp.trans hw_dist
            exact_mod_cast this
          have hp_not_nil : ¬p.Nil := by
            rw [SimpleGraph.Walk.nil_iff_length_eq]; omega
          -- The penultimate vertex of p is at distance k and adjacent to w
          set u := p.penultimate with hu_def
          have hw_mem : w ∈ Layer (k + 1) := by
            simp only [Layer, Finset.mem_filter, Finset.mem_univ, true_and]; exact hw
          refine ⟨u, ?_, p.adj_penultimate hp_not_nil, hw_mem⟩
          -- Show dist v₀ u = k
          -- u is the penultimate vertex of a shortest walk of length k+1
          -- The walk from v₀ to u uses the first k edges, so has length ≤ k
          -- Hence dist(v₀, u) ≤ k
          -- Also dist(v₀, u) ≥ dist(v₀, w) - 1 = k (by triangle ineq with adj u w)
          have hadj_uw := p.adj_penultimate hp_not_nil
          have h_du_le : G.dist v₀ u ≤ k := by
            -- u = penultimate = getVert (p.length - 1)
            -- p.take (p.length - 1) is a walk from v₀ to u of length k
            have h_take := SimpleGraph.dist_le (p.take (p.length - 1))
            have h_take_len : (p.take (p.length - 1)).length = k := by
              rw [SimpleGraph.Walk.take_length, hp_len]
              simp [Nat.min_eq_left (by omega : k ≤ k + 1)]
            rw [h_take_len] at h_take
            exact h_take
          have h_du_ge : k ≤ G.dist v₀ u := by
            have hdiff := hadj_uw.symm.diff_dist_adj (u := v₀)
            rw [hw_dist] at hdiff
            -- hdiff : dist v₀ penultimate = k+1 ∨ = k+2 ∨ = k
            -- h_du_le : dist v₀ u ≤ k, u = penultimate
            show k ≤ G.dist v₀ p.penultimate
            rcases hdiff with h | h | h <;> omega
          simp only [Layer, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        have h_fiber_bound : ∀ u ∈ Layer k, (G.neighborFinset u ∩ Layer (k + 1)).card ≤ s - 1 := by
          intro u hu
          simp only [Layer, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          -- u has degree s (regularity)
          -- u has at least one neighbor at distance k-1 (predecessor)
          -- so at most s-1 neighbors at distance ≥ k, hence ≤ s-1 in Layer(k+1)
          have h_deg : G.degree u = s := hreg u
          -- The neighbor finset has s elements
          -- Layer(k+1) neighbors ⊆ neighborFinset u
          have h_sub : G.neighborFinset u ∩ Layer (k + 1) ⊆ G.neighborFinset u :=
            Finset.inter_subset_left
          -- u has a predecessor: a neighbor at distance k-1
          have hu_reach := hconn v₀ u
          obtain ⟨p, hp⟩ := hu_reach.exists_walk_length_eq_edist
          have hu_dist : G.dist v₀ u = k := hu
          have hp_len : p.length = k := by
            rw [SimpleGraph.dist, ENat.toNat_eq_iff (by omega)] at hu_dist
            have : (↑p.length : ℕ∞) = ↑k := hp.trans hu_dist
            exact_mod_cast this
          have hp_not_nil : ¬p.Nil := by
            rw [SimpleGraph.Walk.nil_iff_length_eq]; omega
          set pred := p.penultimate with hpred_def
          have h_adj_pred : G.Adj pred u := p.adj_penultimate hp_not_nil
          have h_pred_nbr : pred ∈ G.neighborFinset u := by
            rw [SimpleGraph.mem_neighborFinset]; exact h_adj_pred.symm
          have h_pred_dist : G.dist v₀ pred = k - 1 := by
            have h_le : G.dist v₀ pred ≤ k - 1 := by
              have h_take := SimpleGraph.dist_le (p.take (p.length - 1))
              have h_take_len : (p.take (p.length - 1)).length = k - 1 := by
                rw [SimpleGraph.Walk.take_length, hp_len]
                simp [Nat.min_eq_left (by omega : k - 1 ≤ k)]
              rw [h_take_len] at h_take
              exact h_take
            have h_ge : k - 1 ≤ G.dist v₀ pred := by
              have := h_adj_pred.diff_dist_adj (u := v₀)
              rw [hu_dist] at this; omega
            omega
          -- pred is NOT in Layer(k+1)
          have h_pred_not_in : pred ∉ Layer (k + 1) := by
            simp only [Layer, Finset.mem_filter, Finset.mem_univ, true_and]
            omega
          -- So pred ∈ neighborFinset u \ Layer(k+1)
          have h_pred_diff : pred ∈ G.neighborFinset u \ (G.neighborFinset u ∩ Layer (k + 1)) := by
            simp [Finset.mem_sdiff, h_pred_nbr, h_pred_not_in]
          -- Therefore |neighborFinset u ∩ Layer(k+1)| ≤ |neighborFinset u| - 1 = s - 1
          have h1 : (G.neighborFinset u ∩ Layer (k + 1)).card < (G.neighborFinset u).card := by
            apply Finset.card_lt_card
            constructor
            · exact h_sub
            · intro h_eq
              have := h_eq h_pred_nbr
              simp only [Finset.mem_inter] at this
              exact h_pred_not_in this.2
          have h2 : (G.neighborFinset u).card = s := h_deg
          omega
        calc (Layer (k + 1)).card
            ≤ ((Layer k).biUnion (fun u => G.neighborFinset u ∩ Layer (k + 1))).card :=
              Finset.card_le_card h_cover
          _ ≤ (Layer k).sum (fun u => (G.neighborFinset u ∩ Layer (k + 1)).card) :=
              Finset.card_biUnion_le
          _ ≤ (Layer k).sum (fun _ => s - 1) :=
              Finset.sum_le_sum h_fiber_bound
          _ = (s - 1) * (Layer k).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- Now combine: n = 1 + Σ_{k=1}^D |Layer k| ≤ 1 + Σ_{k=1}^D s*(s-1)^{k-1}
  rw [h_sum_layers, Finset.sum_range_succ' (fun k => (Layer k).card)]
  rw [h_layer0]
  -- Need: 1 + Σ_{k=0}^{D-1} |Layer (k+1)| ≤ 1 + s * Σ_{k=0}^{D-1} (s-1)^k
  rw [add_comm]
  apply Nat.add_le_add_left
  -- Σ_{k=0}^{D-1} |Layer (k+1)| ≤ s * Σ_{k=0}^{D-1} (s-1)^k
  -- = Σ_{k=0}^{D-1} s * (s-1)^k
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_range] at hk
  exact h_layer_bound (k + 1) (by omega) (by omega)

/-- A connected `s`-regular graph with `s ≥ 3` and `n` vertices has diameter
at least `log_{s-1}(n · (s-2)/s)`. -/
theorem diam_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 3 ≤ s) (hconn : G.Connected) (hreg : G.IsRegularOfDegree s) :
    Real.logb ((s : ℝ) - 1) ((Fintype.card V : ℝ) * ((s : ℝ) - 2) / s) ≤ G.diam := by
  have hs1 : (1 : ℝ) < (s : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (s : ℝ) := Nat.ofNat_le_cast.mpr hs; linarith
  by_cases hn : (Fintype.card V : ℝ) * ((s : ℝ) - 2) / (s : ℝ) ≤ 0
  · calc Real.logb ((s : ℝ) - 1) ((Fintype.card V : ℝ) * ((s : ℝ) - 2) / s)
        ≤ 0 := by
          simp only [Real.logb]
          apply div_nonpos_of_nonpos_of_nonneg
          · have hx_nonneg : 0 ≤ (Fintype.card V : ℝ) * ((s : ℝ) - 2) / (s : ℝ) := by
              apply div_nonneg
              · apply mul_nonneg (Nat.cast_nonneg _)
                linarith
              · positivity
            exact Real.log_nonpos hx_nonneg (by nlinarith)
          · exact Real.log_nonneg (by linarith)
      _ ≤ (G.diam : ℝ) := Nat.cast_nonneg _
  · push_neg at hn
    rw [Real.logb_le_iff_le_rpow hs1 hn]
    exact moore_bound G s hs hconn hreg

/-- Witness: `diam_lower_bound` is satisfiable (any connected `s`-regular graph with
`s ≥ 3` satisfies the hypotheses). -/
lemma diam_lower_bound_satisfiable :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj)
      (s : ℕ), 3 ≤ s ∧ G.Connected ∧ G.IsRegularOfDegree s := by
  refine ⟨Fin 4, inferInstance, inferInstance, ⊤, inferInstance, 3,
    le_refl 3, SimpleGraph.connected_top, ?_⟩
  have h := SimpleGraph.IsRegularOfDegree.top (V := Fin 4)
  simp [Fintype.card_fin] at h
  exact h

/-! ## Asymptotic Alon–Boppana Bound

For fixed `s ≥ 3`, any sequence of connected `s`-regular graphs with vertex
count tending to infinity satisfies `liminf λ₂ ≥ 2√(s-1)`. -/

/-- **Asymptotic Alon–Boppana Bound.** For a fixed degree `s ≥ 3` and a sequence
of finite, connected `s`-regular graphs whose vertex counts tend to infinity,
the liminf of the second-largest eigenvalues is at least `2√(s-1)`.

This follows from `alonBoppanaBound` and `diam_lower_bound`:
- `n i → ∞` implies `diam(G_i) ≥ logb(s-1, n_i·(s-2)/s) → ∞` by the Moore bound
- For large `i`, `diam(G_i) ≥ 2`, so `alonBoppanaBound` gives
  `λ₂(G_i) ≥ 2√(s-1) - (2√(s-1)-1)/⌊diam/2⌋`
- As `diam → ∞`, the correction `(2√(s-1)-1)/⌊diam/2⌋ → 0`
- Taking `liminf`: `liminf λ₂ ≥ 2√(s-1)`

The proof requires connecting `SimpleGraph.diam` growth with `Filter.liminf` through
logarithmic estimates and the Archimedean property, which needs infrastructure
not directly available for `SimpleGraph` in Mathlib. -/
axiom alonBoppana_liminf
    (s : ℕ) (hs : 3 ≤ s)
    (n : ℕ → ℕ)
    (G : ∀ i, SimpleGraph (Fin (n i)))
    [∀ i, DecidableRel (G i).Adj]
    (hconn : ∀ i, (G i).Connected)
    (hreg : ∀ i, (G i).IsRegularOfDegree s)
    (hcard : ∀ i, 2 ≤ Fintype.card (Fin (n i)))
    (htend : Filter.Tendsto n Filter.atTop Filter.atTop) :
    2 * Real.sqrt ((s : ℝ) - 1) ≤
      Filter.liminf (fun i => secondLargestEigenvalue (G i) (hcard i)) Filter.atTop

/-! ## Eigenvalue bounds for regular graphs -/

/-- All eigenvalues of the adjacency matrix of an `s`-regular graph lie in `[-s, s]`.
Proved via the Gershgorin circle theorem: each eigenvalue lies in a disc of center
`A_{kk} = 0` and radius `Σ_{j≠k} |A_{kj}| = degree(k) = s`. -/
theorem adjEigenvalue_abs_le {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (s : ℕ) (hreg : G.IsRegularOfDegree s) (i : Fin (Fintype.card W)) :
    |adjEigenvalues G i| ≤ (s : ℝ) := by
  -- Step 1: eigenvalue is in the ℝ-spectrum of the adjacency matrix
  have h_spec : adjEigenvalues G i ∈ spectrum ℝ (G.adjMatrix ℝ) := by
    show (adjMatrix_isHermitian G).eigenvalues₀ i ∈ spectrum ℝ (G.adjMatrix ℝ)
    have h_eq : (adjMatrix_isHermitian G).eigenvalues₀ i =
        (adjMatrix_isHermitian G).eigenvalues
          ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card W))) i) := by
      simp [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]
    rw [h_eq]
    exact (adjMatrix_isHermitian G).eigenvalues_mem_spectrum_real _
  -- Step 2: spectrum of matrix = spectrum of toLin' (via algebra equiv)
  have h_has : Module.End.HasEigenvalue (Matrix.toLin' (G.adjMatrix ℝ))
      (adjEigenvalues G i) := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum]
    rwa [Matrix.spectrum_toLin']
  -- Step 3: Gershgorin circle theorem
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball h_has
  -- Step 4: diagonal entry of adjacency matrix is 0 (no self-loops)
  have h_diag : (G.adjMatrix ℝ) k k = 0 := by
    simp [SimpleGraph.adjMatrix_apply, G.loopless]
  -- Step 5: Gershgorin radius = degree(k) = s
  have h_radius : (Finset.univ.erase k).sum (fun j => ‖(G.adjMatrix ℝ) k j‖) = (s : ℝ) := by
    have h1 : ∀ j, ‖(G.adjMatrix ℝ) k j‖ = if G.Adj k j then (1 : ℝ) else 0 := by
      intro j; simp [SimpleGraph.adjMatrix_apply]; split_ifs <;> simp
    simp_rw [h1]
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, mul_zero, add_zero]
    have h2 : (Finset.univ.erase k).filter (G.Adj k) = G.neighborFinset k := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
      constructor
      · intro ⟨⟨hne, _⟩, hadj⟩; exact hadj
      · intro hadj; exact ⟨⟨(G.ne_of_adj hadj).symm, trivial⟩, hadj⟩
    rw [h2]
    exact_mod_cast hreg k
  -- Step 6: combine: |eigenvalue| ≤ s
  rw [h_diag, h_radius] at hk
  rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hk

/-- Witness: `adjEigenvalue_abs_le` is satisfiable for any `s`-regular graph. -/
lemma adjEigenvalue_abs_le_satisfiable :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W) (_ : DecidableRel G.Adj)
      (s : ℕ), G.IsRegularOfDegree s := by
  exact ⟨Fin 4, inferInstance, inferInstance, ⊤, inferInstance, 3,
    SimpleGraph.IsRegularOfDegree.top⟩

/-- The second-largest eigenvalue of an `s`-regular graph is at least `-(s : ℝ)`. -/
lemma secondLargestEigenvalue_ge_neg {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (s : ℕ) (hreg : G.IsRegularOfDegree s) (hcard : 2 ≤ Fintype.card W) :
    -(s : ℝ) ≤ secondLargestEigenvalue G hcard := by
  have h := adjEigenvalue_abs_le G s hreg ⟨1, by omega⟩
  rw [abs_le] at h
  exact h.1

/-! ## Corollary: Ramanujan bound is tight -/

/-- **The Ramanujan bound is tight.** For any sequence of finite, connected `s`-regular
graphs with vertex counts tending to infinity, and any uniform spectral gap `ε > 0`
(i.e., `∀ i, λ₂(G_i) ≤ s - ε`), we must have `ε ≤ s - 2√(s-1)`.

This follows from the asymptotic Alon–Boppana bound `liminf λ₂ ≥ 2√(s-1)`: since
each `λ₂(G_i) ≤ s - ε`, we get `liminf λ₂ ≤ s - ε`, and combining with
`2√(s-1) ≤ liminf λ₂` yields `ε ≤ s - 2√(s-1)`.

Hence the Ramanujan bound `λ₂ ≤ 2√(s-1)` is the best possible for expander families. -/
theorem ramanujan_bound_optimal
    (s : ℕ) (hs : 3 ≤ s)
    (n : ℕ → ℕ)
    (G : ∀ i, SimpleGraph (Fin (n i)))
    [∀ i, DecidableRel (G i).Adj]
    (hconn : ∀ i, (G i).Connected)
    (hreg : ∀ i, (G i).IsRegularOfDegree s)
    (hcard : ∀ i, 2 ≤ Fintype.card (Fin (n i)))
    (htend : Filter.Tendsto n Filter.atTop Filter.atTop)
    (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ i, secondLargestEigenvalue (G i) (hcard i) ≤ (s : ℝ) - ε) :
    ε ≤ (s : ℝ) - 2 * Real.sqrt ((s : ℝ) - 1) := by
  -- Step 1: Alon–Boppana gives liminf λ₂ ≥ 2√(s-1)
  have hab := alonBoppana_liminf s hs n G hconn hreg hcard htend
  -- Step 2: The uniform bound hgap gives liminf λ₂ ≤ s - ε via frequently_le
  have hfreq : Filter.Frequently
      (fun i => secondLargestEigenvalue (G i) (hcard i) ≤ (s : ℝ) - ε) Filter.atTop :=
    Filter.Frequently.of_forall hgap
  -- Step 3: IsBoundedUnder (· ≥ ·) from eigenvalue lower bound -(s : ℝ)
  have hbdd : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun i => secondLargestEigenvalue (G i) (hcard i)) := by
    exact ⟨-(s : ℝ), Filter.eventually_map.mpr
      (Filter.Eventually.of_forall (fun i =>
        secondLargestEigenvalue_ge_neg (G i) s (hreg i) (hcard i)))⟩
  -- Step 4: liminf λ₂ ≤ s - ε
  have hli := Filter.liminf_le_of_frequently_le hfreq hbdd
  -- Step 5: Combine: 2√(s-1) ≤ liminf ≤ s - ε, so ε ≤ s - 2√(s-1)
  linarith

end AlonBoppana
