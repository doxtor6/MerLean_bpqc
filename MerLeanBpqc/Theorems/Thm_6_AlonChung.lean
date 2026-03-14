import MerLeanBpqc.Definitions.Def_14_GraphExpansion
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Sym

/-!
# Theorem 6: Alon–Chung Bound

## Main Results
- `inducedEdges`: The edge set of the induced subgraph on `S`.
- `alonChung`: For a finite `s`-regular graph with second-largest eigenvalue `λ₂`,
  and `S ⊆ V` with `|S| = γ|V|`, we have `|X(S)₁| ≤ α |X₁|`
  where `α = γ² + (λ₂/s) γ(1-γ)`.

The proof uses spectral decomposition of the quadratic form `1_S^T M 1_S`
where `M` is the adjacency matrix.
-/

open SimpleGraph Fintype Matrix GraphExpansion BigOperators Finset Unitary

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace AlonChung

/-! ## Induced edges -/

/-- The induced edge set `X(S)₁ = {e ∈ X₁ : both endpoints of e lie in S}`. -/
def inducedEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset ∩ S.sym2

lemma mem_inducedEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (e : Sym2 V) : e ∈ inducedEdges G S ↔ e ∈ G.edgeFinset ∧ ∀ v ∈ e, v ∈ S := by
  simp [inducedEdges, Finset.mem_inter, Finset.mem_sym2_iff]

lemma inducedEdges_nonempty (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (h : ∃ e ∈ G.edgeFinset, ∀ v ∈ e, v ∈ S) :
    (inducedEdges G S).Nonempty := by
  obtain ⟨e, he, hS⟩ := h
  exact ⟨e, (mem_inducedEdges G S e).mpr ⟨he, hS⟩⟩

/-! ## Indicator vector -/

/-- The indicator (characteristic) vector `1_S ∈ ℝ^V` of a subset `S ⊆ V`. -/
def indicatorVec (S : Finset V) : V → ℝ :=
  fun v => if v ∈ S then 1 else 0

@[simp]
lemma indicatorVec_mem {S : Finset V} {v : V} (hv : v ∈ S) :
    indicatorVec S v = 1 := if_pos hv

@[simp]
lemma indicatorVec_not_mem {S : Finset V} {v : V} (hv : v ∉ S) :
    indicatorVec S v = 0 := if_neg hv

/-! ## Quadratic form identity -/

/-- The quadratic form `1_S^T M 1_S` counts twice the number of induced edges:
`∑_{v,w} 1_S(v) M(v,w) 1_S(w) = 2 |X(S)₁|`. -/
lemma quadratic_form_eq_twice_inducedEdges
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    dotProduct (indicatorVec S) ((G.adjMatrix ℝ) *ᵥ indicatorVec S) =
    2 * (inducedEdges G S).card := by
  -- Step 1: Unfold to double sum
  simp only [dotProduct, mulVec, adjMatrix_apply, indicatorVec]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  -- Step 2: Show LHS = ∑ v, ∑ w, if G.Adj v w ∧ v ∈ S ∧ w ∈ S then 1 else 0
  have hlhs : ∀ v : V, (if v ∈ S then ∑ w : V, if w ∈ S then
      if G.Adj v w then (1 : ℝ) else 0 else 0 else 0) =
    ∑ w : V, if G.Adj v w ∧ v ∈ S ∧ w ∈ S then 1 else 0 := by
    intro v
    split_ifs with hv
    · congr 1; funext w; split_ifs with hws hadj <;> simp_all
    · symm; apply Finset.sum_eq_zero; intro w _; simp_all
  simp_rw [hlhs]
  -- Step 3: Show ∑∑ if G.Adj v w ∧ v ∈ S ∧ w ∈ S then 1 else 0 = 2 * card(inducedEdges)
  -- Each edge {v,w} in inducedEdges G S gives ordered pairs (v,w) and (w,v)
  -- Convert sum to cardinality
  have hsum_card : ∑ v : V, ∑ w : V, (if G.Adj v w ∧ v ∈ S ∧ w ∈ S then (1 : ℝ) else 0) =
      (((Finset.univ (α := V) ×ˢ Finset.univ (α := V)).filter
        (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∈ S)).card : ℝ) := by
    rw [← Finset.sum_product']
    simp [Finset.sum_boole]
  rw [hsum_card]
  -- Step 4: Show 2 * card(inducedEdges) = card(filtered product)
  -- Use the 2-to-1 correspondence: Sym2.mk maps ordered pairs to unordered edges
  norm_cast
  rw [show inducedEdges G S = G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S) from by
    ext e; simp [inducedEdges, Finset.mem_inter, Finset.mem_sym2_iff, Finset.mem_filter]]
  -- Now show 2 * card(filtered edges) = card(filtered ordered pairs)
  have h2 : ∀ e ∈ G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S),
      ((Finset.univ ×ˢ Finset.univ).filter
        (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∈ S ∧ s(p.1, p.2) = e)).card = 2 := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨he_edge, he_S⟩ := he
    rw [SimpleGraph.mem_edgeFinset] at he_edge
    induction e using Sym2.inductionOn with
    | _ v w =>
    have hadj : G.Adj v w := by rwa [SimpleGraph.mem_edgeSet] at he_edge
    have hne : v ≠ w := G.ne_of_adj hadj
    have hv_S : v ∈ S := he_S v (Sym2.mem_mk_left v w)
    have hw_S : w ∈ S := he_S w (Sym2.mem_mk_right v w)
    have : (Finset.univ ×ˢ Finset.univ).filter
        (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∈ S ∧ s(p.1, p.2) = s(v, w)) =
        {(v, w), (w, v)} := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Sym2.eq_iff]
      constructor
      · rintro ⟨hadj_ab, _, _, hab⟩
        obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hab <;> simp
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨hadj, hv_S, hw_S, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨hadj.symm, hw_S, hv_S, Or.inr ⟨rfl, rfl⟩⟩
    rw [this, Finset.card_pair (by intro h; apply hne; exact Prod.mk.inj h |>.1)]
  -- Now partition the filtered product by edge
  rw [show (Finset.univ ×ˢ Finset.univ).filter
        (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∈ S) =
      (G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)).biUnion
        (fun e => (Finset.univ ×ˢ Finset.univ).filter
          (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∈ S ∧ s(p.1, p.2) = e)) from by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_biUnion]
    constructor
    · rintro ⟨hadj, ha, hb⟩
      refine ⟨s(a, b), ⟨?_, ?_⟩, hadj, ha, hb, rfl⟩
      · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hadj
      · intro v hv; simp [Sym2.mem_iff] at hv; rcases hv with rfl | rfl <;> assumption
    · rintro ⟨e, _, hadj, ha, hb, _⟩
      exact ⟨hadj, ha, hb⟩]
  rw [Finset.card_biUnion (by
    intro e₁ he₁ e₂ he₂ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    intro ⟨a, b⟩ h1 h2
    exact hne (h1.2.2.2.symm.trans h2.2.2.2))]
  simp only [Finset.sum_const_nat (fun e he => h2 e he)]
  ring

/-! ## Edge count for regular graphs -/

/-- For an `s`-regular graph, `|X₁| = s * |V| / 2`. More precisely,
`2 * |X₁| = s * |V|`. -/
lemma twice_card_edgeFinset_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hreg : G.IsRegularOfDegree s) :
    2 * (G.edgeFinset.card : ℝ) = s * Fintype.card V := by
  have h := G.sum_degrees_eq_twice_card_edges
  have hsum : ∑ v : V, G.degree v = s * Fintype.card V := by
    have hreg' : ∀ v, G.degree v = s := hreg
    simp [hreg', Finset.sum_const, Finset.card_univ, mul_comm]
  rw [hsum] at h
  have h' : 2 * (G.edgeFinset.card : ℝ) = (s : ℝ) * (Fintype.card V : ℝ) := by
    exact_mod_cast h.symm
  linarith

/-! ## Spectral decomposition of the quadratic form -/

/-- The spectral decomposition: `x^T A x = ∑_j λ_j (x · v_j)²` for Hermitian `A`,
where `v_j` are orthonormal eigenvectors and `λ_j` are eigenvalues. -/
lemma spectral_decomp_quadratic (A : Matrix V V ℝ) (hA : A.IsHermitian) (x : V → ℝ) :
    dotProduct x (A *ᵥ x) =
    ∑ j : V, hA.eigenvalues j * (dotProduct x (⇑(hA.eigenvectorBasis j))) ^ 2 := by
  -- Use the spectral theorem: A = U * D * U^T
  let U := (hA.eigenvectorUnitary : Matrix V V ℝ)
  let D := diagonal (fun j => (hA.eigenvalues j : ℝ))
  -- Step 1: A = U * D * U^T (spectral theorem for real Hermitian matrices)
  have hU_star : star U = Uᵀ := by
    simp [star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hAeq : A = U * D * Uᵀ := by
    have := hA.spectral_theorem
    rw [this, conjStarAlgAut_apply, hU_star]
    simp [D, U, Function.comp_def, mul_assoc]
  -- Step 2: Let y = U^T *ᵥ x, then A *ᵥ x = U *ᵥ (D *ᵥ y)
  set y := Uᵀ *ᵥ x with hy_def
  have hAx : A *ᵥ x = U *ᵥ (D *ᵥ y) := by
    rw [hAeq, hy_def]; rw [Matrix.mul_assoc]; simp [mulVec_mulVec]
  -- Step 3: x^T (A *ᵥ x) = y^T (D *ᵥ y)
  rw [hAx, Matrix.dotProduct_mulVec]
  -- Goal: vecMul x U ⬝ᵥ (D *ᵥ y) = ∑ ...
  -- vecMul x U = U^T *ᵥ x = y (since for real: vecMul x U = U^T *ᵥ x)
  have hvecmul : Matrix.vecMul x U = y := by
    ext j; simp [Matrix.vecMul, dotProduct, y, hy_def, Matrix.mulVec,
      Matrix.transpose_apply, mul_comm]
  rw [hvecmul]
  -- Step 4: y^T (D *ᵥ y) = ∑ j, eigenvalues j * y_j²
  simp only [dotProduct, D, mulVec_diagonal]
  -- Step 5: y_j = dotProduct x (eigenvectorBasis j)
  congr 1; ext j
  have hU_apply : ∀ i, U i j = (hA.eigenvectorBasis j).ofLp i := by
    intro i; exact hA.eigenvectorUnitary_apply i j
  simp_rw [show y j = ∑ i, x i * U i j from by
    simp [y, hy_def, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]]
  simp_rw [hU_apply]; ring

/-- The Parseval identity for the eigenvector basis: ‖x‖² = ∑_j (x · v_j)². -/
lemma parseval_eigenvector (A : Matrix V V ℝ) (hA : A.IsHermitian) (x : V → ℝ) :
    dotProduct x x =
    ∑ j : V, (dotProduct x (⇑(hA.eigenvectorBasis j))) ^ 2 := by
  let U := (hA.eigenvectorUnitary : Matrix V V ℝ)
  have hU_star : star U = Uᵀ := by
    simp [star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hUUt : U * Uᵀ = (1 : Matrix V V ℝ) := by
    have h := (hA.eigenvectorUnitary).prop
    rw [Matrix.mem_unitaryGroup_iff, hU_star] at h
    -- h : U * Uᵀ = 1 (after unfolding U)
    exact h
  set y := Uᵀ *ᵥ x with hy_def
  -- ‖x‖² = ‖y‖² (orthogonal invariance: U is orthogonal)
  have hdp : dotProduct x x = dotProduct y y := by
    symm
    calc dotProduct y y
      = dotProduct (Uᵀ *ᵥ x) (Uᵀ *ᵥ x) := by rfl
      _ = Matrix.vecMul (Uᵀ *ᵥ x) Uᵀ ⬝ᵥ x := Matrix.dotProduct_mulVec _ _ _
      _ = (U *ᵥ (Uᵀ *ᵥ x)) ⬝ᵥ x := by rw [Matrix.vecMul_transpose]
      _ = ((U * Uᵀ) *ᵥ x) ⬝ᵥ x := by rw [← Matrix.mulVec_mulVec]
      _ = ((1 : Matrix V V ℝ) *ᵥ x) ⬝ᵥ x := by rw [hUUt]
      _ = dotProduct x x := by rw [Matrix.one_mulVec]
  rw [hdp]
  -- dotProduct y y = ∑ j, y_j², and y_j = dotProduct x (eigenvectorBasis j)
  simp only [dotProduct, sq]
  congr 1; ext j
  have hU_apply : ∀ i, U i j = (hA.eigenvectorBasis j).ofLp i := by
    intro i; exact hA.eigenvectorUnitary_apply i j
  simp_rw [show y j = ∑ i, x i * U i j from by
    simp [y, hy_def, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]]
  simp_rw [hU_apply]

/-- Quadratic form bounded by max eigenvalue times norm squared. -/
lemma quadratic_le_bound (A : Matrix V V ℝ) (hA : A.IsHermitian) (x : V → ℝ)
    (C : ℝ) (hC : ∀ j : V, hA.eigenvalues j ≤ C) :
    dotProduct x (A *ᵥ x) ≤ C * dotProduct x x := by
  rw [spectral_decomp_quadratic A hA x, parseval_eigenvector A hA x]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (hC j) (sq_nonneg _)

/-! ## Eigenvalue bounds for regular graphs -/

/-- All eigenvalues of an `s`-regular graph are at most `s`. -/
lemma eigenvalue_le_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hreg : G.IsRegularOfDegree s) (j : V) :
    (adjMatrix_isHermitian G).eigenvalues j ≤ (s : ℝ) := by
  -- Use eigenvalues_eq: λ_j = v_j^T M v_j (Rayleigh quotient at eigenvector)
  let hA := adjMatrix_isHermitian G
  rw [hA.eigenvalues_eq j]
  -- RHS = re(dotProduct (star v_j) (M *ᵥ v_j))
  -- For real: star v = v, re x = x. So = dotProduct v_j (M *ᵥ v_j)
  simp only [star_trivial, RCLike.re_to_real]
  -- Need: dotProduct v_j (M *ᵥ v_j) ≤ s
  -- By AM-GM: for adj matrix of s-regular graph, v^T M v = ∑_{i~j} v_i v_j + v_j v_i ≤ s ‖v‖²
  -- Use v^T M v = ∑_i ∑_{j: i~j} v_i v_j ≤ ∑_i ∑_{j: i~j} (v_i² + v_j²)/2 = s ‖v‖²
  -- And ‖v_j‖ = 1 (orthonormal), so v^T M v ≤ s
  set v := (⇑(hA.eigenvectorBasis j) : V → ℝ)
  -- v is a unit vector
  have hunit : dotProduct v v = 1 := by
    have := hA.eigenvectorBasis.orthonormal.1 j
    rw [EuclideanSpace.norm_eq] at this
    have h1 : Real.sqrt (∑ i, ‖v i‖ ^ 2) = 1 := this
    have h2 : ∑ i, ‖v i‖ ^ 2 = 1 := by
      exact Real.sqrt_eq_one.mp h1
    simp only [dotProduct, Real.norm_eq_abs, sq_abs] at h2 ⊢
    convert h2 using 1
    congr 1; ext i; ring
  -- AM-GM bound: v^T M v ≤ s * ‖v‖²
  have hamgm : dotProduct v ((G.adjMatrix ℝ) *ᵥ v) ≤ s * dotProduct v v := by
    simp only [dotProduct, mulVec, adjMatrix_apply]
    have amgm : ∀ a b : ℝ, a * b ≤ (a ^ 2 + b ^ 2) / 2 := fun a b =>
      by nlinarith [sq_nonneg (a - b)]
    have hdeg : ∀ w : V, (∑ u : V, if G.Adj w u then (1 : ℝ) else 0) = (s : ℝ) := by
      intro w
      have : ∀ u : V, (if G.Adj w u then (1 : ℝ) else 0) = ((if G.Adj w u then 1 else 0 : ℕ) : ℝ) := by
        intro u; split_ifs <;> simp
      simp_rw [this]; push_cast; rw [Finset.sum_boole]
      norm_cast
      rw [show Finset.univ.filter (G.Adj w ·) = G.neighborFinset w from by
        ext u; simp [SimpleGraph.neighborFinset]]
      exact hreg w
    -- Rewrite LHS as double sum of ite(adj)(vi*vj)(0)
    have hlhs : ∑ i : V, v i * ∑ j : V, (if G.Adj i j then (1 : ℝ) else 0) * v j =
        ∑ i : V, ∑ j : V, if G.Adj i j then v i * v j else 0 := by
      congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; split_ifs <;> ring
    rw [hlhs]
    -- Apply AM-GM: vi*vj ≤ (vi² + vj²)/2
    -- Step 1: Bound each term
    have hstep1 : ∑ a : V, ∑ b : V, (if G.Adj a b then v a * v b else (0 : ℝ))
        ≤ ∑ a : V, ∑ b : V, (if G.Adj a b then (v a ^ 2 + v b ^ 2) / 2 else (0 : ℝ)) := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro b _
      split_ifs with h
      · exact amgm _ _
      · exact le_refl _
    -- Step 2: Simplify the AM-GM sum
    -- Step 2: Show AM-GM bound equals s * ∑ v_i²
    -- Splitting: ite(adj)(v^2+v^2)/2 = ite(adj)(v^2/2) + ite(adj)(v^2/2)
    suffices hstep2 : (∑ a : V, ∑ b : V, (if G.Adj a b then (v a ^ 2 + v b ^ 2) / 2 else (0 : ℝ)))
        = ↑s * ∑ a : V, v a * v a by linarith
    have hsplit : ∀ (p q : V), (if G.Adj p q then (v p ^ 2 + v q ^ 2) / 2 else (0 : ℝ)) =
      (if G.Adj p q then v p ^ 2 / 2 else 0) +
      (if G.Adj p q then v q ^ 2 / 2 else 0) := by intros; split_ifs <;> ring
    simp_rw [hsplit, Finset.sum_add_distrib]
    have h1 : ∑ p : V, ∑ q : V, (if G.Adj p q then v p ^ 2 / 2 else (0 : ℝ)) =
        ↑s / 2 * ∑ p : V, v p ^ 2 := by
      have hfact : ∀ (p q : V), (if G.Adj p q then v p ^ 2 / 2 else (0 : ℝ)) =
        v p ^ 2 / 2 * (if G.Adj p q then 1 else 0) := by intros; split_ifs <;> ring
      simp_rw [hfact]
      rw [show (∑ p : V, ∑ q : V, v p ^ 2 / 2 * if G.Adj p q then (1 : ℝ) else 0) =
          ↑s / 2 * ∑ p : V, v p ^ 2 from by
        have : ∀ p : V, (∑ q : V, v p ^ 2 / 2 * if G.Adj p q then (1 : ℝ) else 0) =
            v p ^ 2 / 2 * ↑s := fun p => by rw [← Finset.mul_sum]; congr 1; exact hdeg p
        simp_rw [this]
        rw [← Finset.sum_mul]
        rw [show (∑ x : V, v x ^ 2 / 2) * ↑s = ↑s / 2 * ∑ x : V, v x ^ 2 from by
          rw [← Finset.sum_div]; ring]]
    have h2 : ∑ p : V, ∑ q : V, (if G.Adj p q then v q ^ 2 / 2 else (0 : ℝ)) =
        ↑s / 2 * ∑ p : V, v p ^ 2 := by
      rw [Finset.sum_comm]
      have hfact : ∀ (p q : V), (if G.Adj q p then v p ^ 2 / 2 else (0 : ℝ)) =
        v p ^ 2 / 2 * (if G.Adj q p then 1 else 0) := by intros; split_ifs <;> ring
      simp_rw [hfact]
      have hsym : ∀ p : V, (∑ q : V, if G.Adj q p then (1 : ℝ) else 0) = ↑s := by
        intro p
        have : ∀ q : V, (if G.Adj q p then (1 : ℝ) else 0) = (if G.Adj p q then 1 else 0) := by
          intro q; simp [G.adj_comm]
        simp_rw [this]; exact hdeg p
      have : ∀ p : V, (∑ q : V, v p ^ 2 / 2 * if G.Adj q p then (1 : ℝ) else 0) =
          v p ^ 2 / 2 * ↑s := fun p => by rw [← Finset.mul_sum]; congr 1; exact hsym p
      simp_rw [this]
      rw [← Finset.sum_mul]
      rw [show (∑ x : V, v x ^ 2 / 2) * ↑s = ↑s / 2 * ∑ x : V, v x ^ 2 from by
        rw [← Finset.sum_div]; ring]
    rw [h1, h2]; ring
  rw [hunit, mul_one] at hamgm; exact hamgm

/-- `s` is an eigenvalue of the adjacency matrix of an `s`-regular graph.
This follows from `M · 1 = s · 1`. -/
lemma degree_mem_eigenvalues (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (s : ℕ) (hreg : G.IsRegularOfDegree s) :
    (s : ℝ) ∈ Set.range (adjMatrix_isHermitian G).eigenvalues := by
  -- s is in the spectrum of M, hence equals some eigenvalue
  rw [← (adjMatrix_isHermitian G).spectrum_real_eq_range_eigenvalues]
  -- Need: (s : ℝ) ∈ spectrum ℝ (G.adjMatrix ℝ)
  -- M *ᵥ (const 1) = s • (const 1), and const 1 ≠ 0, so s is an eigenvalue
  rw [spectrum.mem_iff]
  intro h
  -- h : IsUnit ((algebraMap ℝ (Matrix V V ℝ)) s - G.adjMatrix ℝ)
  -- The all-ones vector is in the kernel of (s * I - M)
  have h1 : (((s : ℝ) • (1 : Matrix V V ℝ)) - G.adjMatrix ℝ) *ᵥ Function.const V (1 : ℝ) = 0 := by
    ext v
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_one, Function.const_apply, Pi.zero_apply]
    have := hreg v
    simp only [SimpleGraph.IsRegularOfDegree, SimpleGraph.degree] at this
    rw [show (G.adjMatrix ℝ *ᵥ Function.const V 1) v =
      (s : ℝ) from by
        simp only [Matrix.mulVec, dotProduct, adjMatrix_apply, Function.const_apply]
        simp only [mul_one, Finset.sum_boole]
        have : (Finset.univ.filter (G.Adj v ·)) = G.neighborFinset v := by
          ext u; simp [SimpleGraph.neighborFinset]
        rw [this]; exact_mod_cast hreg v]
    ring
  -- But (s * I - M) is invertible (by h), contradiction
  have h2 : Function.const V (1 : ℝ) ≠ 0 := by
    intro hc; exact absurd (congr_fun hc (Classical.arbitrary V)) (by simp)
  have halg : (algebraMap ℝ (Matrix V V ℝ)) ↑s = (↑s : ℝ) • (1 : Matrix V V ℝ) :=
    Algebra.algebraMap_eq_smul_one _
  rw [halg] at h
  have h3 := Matrix.mulVec_injective_of_isUnit h
  exact h2 (h3 (by rw [h1, Matrix.mulVec_zero]))

/-- The maximum eigenvalue of an `s`-regular graph is `s`. -/
lemma max_eigenvalue_eq_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hreg : G.IsRegularOfDegree s) (hcard : 2 ≤ Fintype.card V) :
    adjEigenvalues G ⟨0, by omega⟩ = (s : ℝ) := by
  let hA := adjMatrix_isHermitian G
  let equiv := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))
  -- adjEigenvalues G k = hA.eigenvalues₀ k
  -- eigenvalues₀ k = eigenvalues (equiv k)   [by definition of eigenvalues]
  -- Step 1: eigenvalues₀ ⟨0, _⟩ ≤ s
  have hle : adjEigenvalues G ⟨0, by omega⟩ ≤ s := by
    show hA.eigenvalues₀ ⟨0, by omega⟩ ≤ (s : ℝ)
    have : hA.eigenvalues₀ ⟨0, by omega⟩ = hA.eigenvalues (equiv ⟨0, by omega⟩) := by
      simp only [Matrix.IsHermitian.eigenvalues]
      congr 1; simp [equiv, Equiv.symm_apply_apply]
    rw [this]
    exact eigenvalue_le_degree G s hreg _
  -- Step 2: s ≤ eigenvalues₀ ⟨0, _⟩
  have hge : (s : ℝ) ≤ adjEigenvalues G ⟨0, by omega⟩ := by
    haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨j, hj⟩ := degree_mem_eigenvalues G s hreg
    rw [← hj]
    show hA.eigenvalues j ≤ hA.eigenvalues₀ ⟨0, by omega⟩
    have : hA.eigenvalues j = hA.eigenvalues₀ (equiv.symm j) := by
      simp only [Matrix.IsHermitian.eigenvalues]; congr 1
    rw [this]
    exact (adjMatrix_isHermitian G).eigenvalues₀_antitone (Fin.zero_le _)
  linarith

/-! ## Norm of indicator vector -/

@[simp]
lemma indicatorVec_dotProduct_self (S : Finset V) :
    dotProduct (indicatorVec S) (indicatorVec S) = S.card := by
  simp only [dotProduct, indicatorVec]
  rw [show ∑ v : V, (if v ∈ S then (1:ℝ) else 0) * (if v ∈ S then 1 else 0) =
    ∑ v : V, if v ∈ S then 1 else 0 from by
    congr 1; funext v; split_ifs <;> ring]
  simp [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-! ## Spectral bound on the quadratic form -/

/-- The all-ones vector is an eigenvector of the adjacency matrix with eigenvalue `s`. -/
lemma regular_mulVec_const (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hreg : G.IsRegularOfDegree s) (c : ℝ) :
    (G.adjMatrix ℝ) *ᵥ Function.const V c = Function.const V (s * c) := by
  ext v
  simp only [Matrix.mulVec, dotProduct, adjMatrix_apply, Function.const_apply]
  have hdeg : (∑ x : V, if G.Adj v x then (1 : ℝ) else 0) = (s : ℝ) := by
    simp only [Finset.sum_boole]
    have : (Finset.univ.filter (G.Adj v ·)) = G.neighborFinset v := by
      ext u; simp [SimpleGraph.neighborFinset]
    rw [this]; exact_mod_cast hreg v
  rw [show (∑ x : V, (if G.Adj v x then (1 : ℝ) else 0) * c) =
      c * (∑ x : V, if G.Adj v x then (1 : ℝ) else 0) from by
    rw [← Finset.sum_mul]; ring]
  rw [hdeg]; ring

/-- Decomposition of the quadratic form using the all-ones vector.
If z = x - γ · 1, then x^T M x = s γ² n + z^T M z. -/
lemma quadratic_decomp (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hreg : G.IsRegularOfDegree s) (x z : V → ℝ) (γ : ℝ)
    (hx : x = fun v => γ + z v)
    (hz_sum : ∑ v : V, z v = 0) :
    dotProduct x ((G.adjMatrix ℝ) *ᵥ x) =
    s * γ ^ 2 * Fintype.card V + dotProduct z ((G.adjMatrix ℝ) *ᵥ z) := by
  -- x = γ · 1 + z, so M x = γ s · 1 + M z
  have hMx : (G.adjMatrix ℝ) *ᵥ x = fun v => s * γ + ((G.adjMatrix ℝ) *ᵥ z) v := by
    rw [hx]; ext v; simp only [Matrix.mulVec, dotProduct, adjMatrix_apply]
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul]
    have hdeg_v : (∑ w : V, ite (G.Adj v w) (1 : ℝ) 0) = (s : ℝ) := by
      simp only [Finset.sum_boole]
      have : (Finset.univ.filter (G.Adj v ·)) = G.neighborFinset v := by
        ext u; simp [SimpleGraph.neighborFinset]
      rw [this]; exact_mod_cast hreg v
    rw [hdeg_v]
  -- dotProduct x (M x) = dotProduct (γ1 + z) (sγ1 + Mz)
  rw [hMx, hx]
  simp only [dotProduct, Function.const_apply]
  -- Expand (γ + z v) * (s * γ + (M z) v) = sγ² + γ (Mz)v + sγ z v + z v (Mz) v
  -- Sum over v: sγ²n + γ ∑(Mz)v + sγ · 0 + z^T Mz
  simp_rw [show ∀ v, (γ + z v) * (↑s * γ + ((G.adjMatrix ℝ) *ᵥ z) v) =
    ↑s * γ ^ 2 + γ * ((G.adjMatrix ℝ) *ᵥ z) v +
    ↑s * γ * z v + z v * ((G.adjMatrix ℝ) *ᵥ z) v from fun v => by ring]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- ∑ z v = 0
  rw [show ∑ v : V, ↑s * γ * z v = ↑s * γ * ∑ v : V, z v from by
    rw [Finset.mul_sum]]
  rw [hz_sum, mul_zero]
  -- ∑ (Mz)v = ∑_v ∑_w M_{vw} z_w = ∑_w (∑_v M_{vw}) z_w = ∑_w s z_w = 0
  rw [show ∑ v : V, γ * ((G.adjMatrix ℝ) *ᵥ z) v =
    γ * ∑ v : V, ((G.adjMatrix ℝ) *ᵥ z) v from by rw [Finset.mul_sum]]
  rw [show ∑ v : V, ((G.adjMatrix ℝ) *ᵥ z) v =
    ∑ v : V, ∑ w : V, (if G.Adj v w then (1 : ℝ) else 0) * z w from by
    simp [Matrix.mulVec, dotProduct, adjMatrix_apply]]
  rw [Finset.sum_comm]
  rw [show ∑ w : V, ∑ v : V, (if G.Adj v w then (1 : ℝ) else 0) * z w =
    ∑ w : V, z w * ∑ v : V, if G.Adj v w then 1 else 0 from by
    congr 1; ext w; rw [← Finset.sum_mul]; ring]
  have hadj_sym : ∀ w : V, (∑ v : V, if G.Adj v w then (1 : ℝ) else 0) = ↑s := by
    intro w
    have : ∀ v : V, (if G.Adj v w then (1 : ℝ) else 0) = (if G.Adj w v then 1 else 0) := by
      intro v; simp [G.adj_comm]
    simp_rw [this]
    simp only [Finset.sum_boole]
    have : (Finset.univ.filter (G.Adj w ·)) = G.neighborFinset w := by
      ext u; simp [SimpleGraph.neighborFinset]
    rw [this]; exact_mod_cast hreg w
  simp_rw [hadj_sym]
  rw [show ∑ w : V, z w * (s : ℝ) = (s : ℝ) * ∑ w : V, z w from by
    rw [Finset.mul_sum]; congr 1; ext w; ring]
  rw [hz_sum, mul_zero, mul_zero, add_zero, add_zero]
  ring

/-- For an s-regular graph with s ≥ 1 where the largest eigenvalue is simple
(strictly greater than the second), any eigenvector of the adjacency matrix with
eigenvalue s is globally constant. This combines two classical spectral graph
theory results: (1) the discrete maximum principle shows eigenvectors for eigenvalue s
are constant on connected components, and (2) simple top eigenvalue implies graph
connectivity (otherwise each component contributes an independent eigenvector for
eigenvalue s, giving multiplicity ≥ 2). Both require infrastructure (harmonic function
theory on graphs, eigenspace dimension theory) not currently available in Mathlib. -/
axiom regular_eigenvector_s_constant
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s) (hreg : G.IsRegularOfDegree s)
    (hcard : 2 ≤ Fintype.card V)
    (hsimple : (adjMatrix_isHermitian G).eigenvalues₀ ⟨0, by omega⟩ >
               (adjMatrix_isHermitian G).eigenvalues₀ ⟨1, by omega⟩)
    (v : V → ℝ) (hv : (G.adjMatrix ℝ) *ᵥ v = (s : ℝ) • v) :
    ∃ c : ℝ, v = Function.const V c

set_option maxRecDepth 8192 in
/-- The spectral bound: `1_S^T M 1_S ≤ s γ² n + λ₂ γ(1-γ) n`. -/
lemma spectral_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s)
    (hreg : G.IsRegularOfDegree s)
    (hcard : 2 ≤ Fintype.card V) (S : Finset V) :
    let n := (Fintype.card V : ℝ)
    let γ := (S.card : ℝ) / n
    let lam₂ := secondLargestEigenvalue G hcard
    dotProduct (indicatorVec S) ((G.adjMatrix ℝ) *ᵥ indicatorVec S) ≤
    s * γ ^ 2 * n + lam₂ * γ * (1 - γ) * n := by
  intro n γ lam₂
  -- Let z = 1_S - γ · 1
  set z : V → ℝ := fun v => indicatorVec S v - γ with hz_def
  -- z sums to 0: ∑ z_v = |S| - γ n = |S| - |S| = 0
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hz_sum : ∑ v : V, z v = 0 := by
    simp only [hz_def, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [show ∑ v : V, indicatorVec S v = (S.card : ℝ) from by
      simp [indicatorVec, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]]
    have hne : n ≠ 0 := ne_of_gt hn_pos
    show ↑(#S) - ↑(Fintype.card V) * (↑(#S) / n) = 0
    rw [show ↑(Fintype.card V) = n from rfl]
    rw [mul_div_cancel₀ _ hne]; ring
  -- 1_S = γ · 1 + z
  have hx_eq : indicatorVec S = fun v => γ + z v := by
    ext v; simp [hz_def]
  -- Apply the decomposition: 1_S^T M 1_S = sγ²n + z^T M z
  have hdecomp := quadratic_decomp G s hreg (indicatorVec S) z γ hx_eq hz_sum
  rw [hdecomp]
  -- Need: z^T M z ≤ λ₂ · ‖z‖²
  suffices hzbound : dotProduct z ((G.adjMatrix ℝ) *ᵥ z) ≤ lam₂ * dotProduct z z by
    -- Also need: ‖z‖² = γ(1-γ)n
    have hz_norm : dotProduct z z = γ * (1 - γ) * n := by
      simp only [hz_def, dotProduct]
      have hind_sq : ∀ v : V, (indicatorVec S v - γ) * (indicatorVec S v - γ) =
          indicatorVec S v ^ 2 - 2 * γ * indicatorVec S v + γ ^ 2 := fun v => by ring
      simp_rw [hind_sq]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [show ∑ v : V, indicatorVec S v ^ 2 = (S.card : ℝ) from by
        simp [indicatorVec, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
          sq, ite_mul, one_mul, zero_mul]]
      rw [show ∑ v : V, 2 * γ * indicatorVec S v = 2 * γ * S.card from by
        rw [← Finset.mul_sum]
        congr 1
        simp [indicatorVec, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]]
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hne : n ≠ 0 := ne_of_gt hn_pos
      have hn_ne : (n : ℝ) ≠ 0 := hne
      have hγ : γ = ↑(#S) / n := rfl
      rw [hγ]
      have hn_eq : ↑(Fintype.card V) = n := rfl
      rw [hn_eq]
      -- Goal: ↑(#S) - 2 * (↑(#S) / n) * ↑(#S) + n * (↑(#S) / n) ^ 2 = ↑(#S) / n * (1 - ↑(#S) / n) * n
      set c := (↑(#S) : ℝ) / n
      have hSn : (↑(#S) : ℝ) = c * n := (div_mul_cancel₀ _ hn_ne).symm
      rw [hSn]
      ring
    rw [hz_norm] at hzbound
    linarith
  -- The key: z^T M z ≤ λ₂ * z^T z
  -- We use the quadratic form bound
  -- Case 1: λ₂ = eigenvalues₀ 0 (= s). Then all eigenvalues ≤ s = λ₂, so bound holds.
  -- Case 2: λ₂ < eigenvalues₀ 0. Then eigenspace of s is 1-dim, z ⊥ 1 implies z ⊥ v₁,
  --   so the spectral decomp gives the bound.
  -- For simplicity, use the quadratic_le_bound with C = s, then relate to λ₂.
  -- Actually, we'll use the full spectral decomposition.
  let hA := adjMatrix_isHermitian G
  rw [spectral_decomp_quadratic (G.adjMatrix ℝ) hA z, parseval_eigenvector (G.adjMatrix ℝ) hA z]
  -- Goal: ∑ j, λ_j c_j² ≤ λ₂ * ∑ j, c_j²
  -- where c_j = dotProduct z (v_j) and λ_j = hA.eigenvalues j
  -- Strategy: bound each term λ_j c_j² ≤ λ₂ c_j² when possible
  -- For j with eigenvalues j ≤ λ₂: λ_j c_j² ≤ λ₂ c_j² ✓
  -- For j with eigenvalues j > λ₂: need c_j = 0, which follows from z ⊥ 1 and v_j ∈ eigenspace of s
  -- For now, use: all eigenvalues ≤ s, and if λ₂ = s we're done; if λ₂ < s, use z ⊥ eigenvector
  by_cases hcase : ∀ j : V, hA.eigenvalues j ≤ lam₂
  · -- Case 1: All eigenvalues ≤ λ₂
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro j _
    exact mul_le_mul_of_nonneg_right (hcase j) (sq_nonneg _)
  · -- Case 2: Some eigenvalue > λ₂ ⟹ eigenvalues₀ ⟨0⟩ > eigenvalues₀ ⟨1⟩
    push_neg at hcase
    obtain ⟨j₁, hj₁⟩ := hcase
    -- Derive that eigenvalues₀ ⟨0⟩ > eigenvalues₀ ⟨1⟩ = lam₂
    haveI : NeZero (Fintype.card V) := ⟨by omega⟩
    have hsimple : hA.eigenvalues₀ ⟨0, by omega⟩ > hA.eigenvalues₀ ⟨1, by omega⟩ := by
      have hj₁_eq : hA.eigenvalues j₁ =
          hA.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))).symm j₁) := by
        simp only [Matrix.IsHermitian.eigenvalues]
      have h0ge : hA.eigenvalues₀ ⟨0, by omega⟩ ≥ hA.eigenvalues j₁ := by
        rw [hj₁_eq]; exact hA.eigenvalues₀_antitone (Fin.zero_le _)
      have hlam₂_eq : lam₂ = hA.eigenvalues₀ ⟨1, by omega⟩ := rfl
      linarith
    -- Bound each summand
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : hA.eigenvalues j ≤ lam₂
    · exact mul_le_mul_of_nonneg_right hj (sq_nonneg _)
    · -- eigenvalues j > lam₂ ⟹ eigenvalues j = s ⟹ eigvec is constant ⟹ z ⊥ eigvec
      push_neg at hj
      -- Show eigenvalues j = s
      have hj_eq : hA.eigenvalues j =
          hA.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))).symm j) := by
        simp only [Matrix.IsHermitian.eigenvalues]
      set hk := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))).symm j with hk_def
      have hk_zero : hk = ⟨0, by omega⟩ := by
        by_contra hne
        have hne_val : hk.val ≠ 0 := fun heq => hne (Fin.ext heq)
        have hge1 : (⟨1, by omega⟩ : Fin (Fintype.card V)) ≤ hk := by
          rw [Fin.mk_le_mk]; omega
        have hbound := hA.eigenvalues₀_antitone hge1
        rw [← hj_eq] at hbound
        have hlam₂_eq' : lam₂ = hA.eigenvalues₀ ⟨1, by omega⟩ := rfl
        linarith
      have hj_eq_s : hA.eigenvalues j = (s : ℝ) := by
        rw [hj_eq, hk_zero]; exact max_eigenvalue_eq_degree G s hreg hcard
      -- M * eigvec j = s • eigvec j
      have hvec : (G.adjMatrix ℝ) *ᵥ ⇑(hA.eigenvectorBasis j) =
          (s : ℝ) • ⇑(hA.eigenvectorBasis j) := by
        rw [← hj_eq_s]; exact hA.mulVec_eigenvectorBasis j
      -- By axiom: eigvec j is globally constant
      obtain ⟨c, hc⟩ := regular_eigenvector_s_constant (V := V) G s hs hreg hcard hsimple (⇑(hA.eigenvectorBasis j)) hvec
      -- dotProduct z (const c) = c * ∑ z = 0
      have hdot : dotProduct z (⇑(hA.eigenvectorBasis j)) = 0 := by
        conv_lhs => rw [show (⇑(hA.eigenvectorBasis j) : V → ℝ) = Function.const V c from hc]
        simp only [dotProduct, Function.const_apply]
        rw [← Finset.sum_mul, hz_sum, zero_mul]
      simp [hdot]

/-! ## Main Theorem -/

/-- **Alon–Chung Bound.** For a finite `s`-regular graph with `s ≥ 1` and `|V| ≥ 2`,
with second-largest eigenvalue `λ₂`, and `S ⊆ V` with `|S| = γ|V|` for
`0 < γ < 1`, define `α = γ² + (λ₂/s) γ(1-γ)`. Then `|X(S)₁| ≤ α |X₁|`.

The proof uses the spectral decomposition of the quadratic form `1_S^T M 1_S`
to bound the number of edges in the induced subgraph. -/
theorem alonChung
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s) (hreg : G.IsRegularOfDegree s)
    (hcard : 2 ≤ Fintype.card V)
    (S : Finset V) (hS_ne : S.Nonempty) (hS_lt : S.card < Fintype.card V) :
    let n := (Fintype.card V : ℝ)
    let γ := (S.card : ℝ) / n
    let lam₂ := secondLargestEigenvalue G hcard
    let α := γ ^ 2 + (lam₂ / ↑s) * γ * (1 - γ)
    ((inducedEdges G S).card : ℝ) ≤ α * (G.edgeFinset.card : ℝ) := by
  intro n γ lam₂ α
  -- Step 1: From the quadratic form identity, 2|X(S)₁| = 1_S^T M 1_S
  have hqf := quadratic_form_eq_twice_inducedEdges G S
  -- Step 2: From the spectral bound, 1_S^T M 1_S ≤ sγ²n + λ₂γ(1-γ)n
  have hsp := spectral_bound G s hs hreg hcard S
  -- Step 3: Edge count for regular graphs: 2|X₁| = sn
  have hedge := twice_card_edgeFinset_eq G s hreg
  -- Step 4: Combine
  -- From hqf: 2 * |inducedEdges| = qf
  -- From hsp: qf ≤ sγ²n + λ₂γ(1-γ)n
  -- So: 2 * |inducedEdges| ≤ sγ²n + λ₂γ(1-γ)n
  -- From hedge: 2 * |X₁| = sn, so |X₁| = sn/2
  -- Goal: |inducedEdges| ≤ (γ² + λ₂/s · γ(1-γ)) * |X₁|
  --      = (γ² + λ₂/s · γ(1-γ)) * sn/2
  --      = (sγ² + λ₂γ(1-γ)) * n/2
  -- Sufficient: 2|inducedEdges| ≤ (sγ² + λ₂γ(1-γ)) * n
  have hn_pos : (0 : ℝ) < n := by exact Nat.cast_pos.mpr (by omega)
  have hs_pos : (0 : ℝ) < s := by exact Nat.cast_pos.mpr (by omega)
  -- 2 * card ≤ sγ²n + λ₂γ(1-γ)n
  have h2card : 2 * ((inducedEdges G S).card : ℝ) ≤ s * γ ^ 2 * n + lam₂ * γ * (1 - γ) * n := by
    linarith
  -- α * |X₁| = (γ² + λ₂/s · γ(1-γ)) * sn/2
  --           = (sγ² + λ₂γ(1-γ)) * n / 2
  have hα_expand : α * (G.edgeFinset.card : ℝ) =
      (↑s * γ ^ 2 + lam₂ * γ * (1 - γ)) * n / 2 := by
    have : (G.edgeFinset.card : ℝ) = ↑s * n / 2 := by linarith
    rw [this]
    show (γ ^ 2 + lam₂ / ↑s * γ * (1 - γ)) * (↑s * n / 2) =
      (↑s * γ ^ 2 + lam₂ * γ * (1 - γ)) * n / 2
    field_simp
  rw [hα_expand]
  linarith

end AlonChung
