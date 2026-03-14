import MerLeanBpqc.Lemmas.Lem_1_RelativeCheeger
import MerLeanBpqc.Definitions.Def_18_CheegerConstant

/-!
# Lemma 3: Relative Vertex-to-Edge Expansion

## Main Results
- `relativeVertexToEdgeExpansion`: For a finite, connected, `s`-regular graph with
  second-largest eigenvalue `λ₂`, parameter `α ∈ (0,1)`, subset `S` with `|S| ≤ α|V|`,
  and `0 < b ≤ s`, define `A = {v ∈ S | |(δS)_v| ≥ s - b}` and
  `β = ((b - λ₂) - α(s - λ₂))/b`. Then `|A| ≥ β|S|`.
-/

open Finset SimpleGraph BigOperators GraphExpansion CheegerConstant

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace RelativeVertexToEdgeExpansion

/-! ## Definitions -/

/-- The edges in the edge boundary `δS` incident to vertex `v` (for SimpleGraph). -/
noncomputable def edgeBoundaryAtVertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : Finset (Sym2 V) :=
  (edgeBoundary G S).filter fun e => v ∈ e

/-- The set `A = {v ∈ S | |(δS)_v| ≥ s - b}`: vertices in `S` with high boundary degree. -/
noncomputable def highExpansionVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (s : ℕ) (b : ℝ) : Finset V :=
  S.filter fun v => (s : ℝ) - b ≤ (edgeBoundaryAtVertex G S v).card

/-- `A ⊆ S`. -/
lemma highExpansionVertices_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (s : ℕ) (b : ℝ) :
    highExpansionVertices G S s b ⊆ S :=
  filter_subset _ _

/-- Witness: `highExpansionVertices` is nonempty when there exists a vertex in `S`
with high boundary degree. -/
lemma highExpansionVertices_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (s : ℕ) (b : ℝ)
    (h : ∃ v ∈ S, (s : ℝ) - b ≤ (edgeBoundaryAtVertex G S v).card) :
    (highExpansionVertices G S s b).Nonempty := by
  obtain ⟨v, hv, hvb⟩ := h
  exact ⟨v, Finset.mem_filter.mpr ⟨hv, hvb⟩⟩

/-! ## Partition of the edge boundary

Each edge in `δS` has exactly one endpoint in `S`, so `{(δS)_v}_{v ∈ S}` partitions `δS`.
This gives `|δS| = ∑_{v ∈ S} |(δS)_v|`. -/

/-- The biUnion of `edgeBoundaryAtVertex` over `S` equals the edge boundary. -/
private lemma edgeBoundary_eq_biUnion (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    edgeBoundary G S = S.biUnion (fun v => edgeBoundaryAtVertex G S v) := by
  ext e
  constructor
  · intro he
    rw [Finset.mem_biUnion]
    have he_mem := he
    rw [mem_edgeBoundary] at he
    obtain ⟨_, a, b, hab, ha, _⟩ := he
    subst hab
    exact ⟨a, ha, Finset.mem_filter.mpr ⟨he_mem, Sym2.mem_mk_left a b⟩⟩
  · intro he
    rw [Finset.mem_biUnion] at he
    obtain ⟨v, _, hv⟩ := he
    exact (Finset.mem_filter.mp hv).1

/-- The `edgeBoundaryAtVertex` sets for distinct vertices in `S` are disjoint.
A boundary edge has exactly one endpoint in `S`. -/
private lemma edgeBoundaryAtVertex_pairwiseDisjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    (S : Set V).PairwiseDisjoint (fun v => edgeBoundaryAtVertex G S v) := by
  intro v hv w hw hvw
  simp only [Function.onFun, edgeBoundaryAtVertex]
  rw [Finset.disjoint_filter]
  intro e he hve hwe
  -- e ∈ edgeBoundary G S, v ∈ e, w ∈ e, v ≠ w
  rw [mem_edgeBoundary] at he
  obtain ⟨_, a, b, hab, ha, hb⟩ := he
  subst hab
  -- v ∈ s(a, b) and w ∈ s(a, b) with v ≠ w
  simp only [Sym2.mem_iff] at hve hwe
  -- v = a or v = b, w = a or w = b
  rcases hve with rfl | rfl <;> rcases hwe with rfl | rfl
  · exact absurd rfl hvw
  · -- v = a ∈ S (✓), w = b ∉ S, but w ∈ S (from hw) — contradiction
    exact absurd (hw : w ∈ S) hb
  · -- v = b ∉ S, but v ∈ S (from hv) — contradiction
    exact absurd (hv : v ∈ S) hb
  · exact absurd rfl hvw

/-- The edge boundary card equals the sum of `edgeBoundaryAtVertex` cards over `S`. -/
lemma edgeBoundary_partition_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    (edgeBoundary G S).card = ∑ v ∈ S, (edgeBoundaryAtVertex G S v).card := by
  rw [edgeBoundary_eq_biUnion G S]
  exact Finset.card_biUnion (edgeBoundaryAtVertex_pairwiseDisjoint G S)

/-! ## Degree bound -/

/-- The boundary edges at `v` form a subset of the incidence finset of `v`. -/
private lemma edgeBoundaryAtVertex_subset_incidenceFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) :
    edgeBoundaryAtVertex G S v ⊆ G.incidenceFinset v := by
  intro e he
  simp only [edgeBoundaryAtVertex, Finset.mem_filter] at he
  rw [SimpleGraph.mem_incidenceFinset]
  exact ⟨G.mem_edgeFinset.mp (edgeBoundary_subset_edgeFinset G S he.1), he.2⟩

/-- The number of boundary edges incident to `v` is at most `s` (the degree). -/
lemma edgeBoundaryAtVertex_le_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hreg : G.IsRegularOfDegree s) (S : Finset V) (v : V) :
    (edgeBoundaryAtVertex G S v).card ≤ s := by
  calc (edgeBoundaryAtVertex G S v).card
      ≤ (G.incidenceFinset v).card := Finset.card_le_card (edgeBoundaryAtVertex_subset_incidenceFinset G S v)
    _ = G.degree v := G.card_incidenceFinset_eq_degree v
    _ = s := hreg v

/-! ## Helper: Relative Cheeger with `≤` -/

/-- The relative Cheeger bound with `|S| ≤ α|V|` (non-strict).
Derived from the `spectralLaplacianBound` axiom in Lem_1. -/
lemma relativeCheeger_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hconn : G.Connected) (hreg : G.IsRegularOfDegree s)
    (S : Finset V) (hS_pos : 0 < S.card)
    (hS_le : (S.card : ℝ) ≤ α * Fintype.card V)
    (hcard : 2 ≤ Fintype.card V) :
    (1 - α) * ((s : ℝ) - secondLargestEigenvalue G hcard) * S.card ≤
      (edgeBoundary G S).card := by
  have hS_pos_real : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS_pos
  have hV_pos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  -- |S| < |V| since |S| ≤ α|V| < |V|
  have hS_lt_V : S.card < Fintype.card V := by
    have : (S.card : ℝ) ≤ α * Fintype.card V := hS_le
    have : α * (Fintype.card V : ℝ) < 1 * Fintype.card V := by
      exact mul_lt_mul_of_pos_right hα1 hV_pos
    have : (S.card : ℝ) < Fintype.card V := by linarith
    exact_mod_cast this
  -- Case split on sign of (s - λ₂)
  by_cases h_gap : (0 : ℝ) ≤ (s : ℝ) - secondLargestEigenvalue G hcard
  · -- Case s ≥ λ₂: use spectral bound + |S|/|V| ≤ α
    have h_spectral := RelativeCheeger.spectralLaplacianBound G s hcard hconn hreg S hS_pos hS_lt_V
    have h_ratio : (S.card : ℝ) / Fintype.card V ≤ α := by
      rwa [div_le_iff₀ hV_pos]
    have h_compl : (1 : ℝ) - α ≤ 1 - S.card / Fintype.card V := by linarith
    calc (1 - α) * ((s : ℝ) - secondLargestEigenvalue G hcard) * S.card
        = ((s : ℝ) - secondLargestEigenvalue G hcard) * S.card * (1 - α) := by ring
      _ ≤ ((s : ℝ) - secondLargestEigenvalue G hcard) * S.card *
            (1 - S.card / Fintype.card V) := by
          apply mul_le_mul_of_nonneg_left h_compl
          exact mul_nonneg h_gap (le_of_lt hS_pos_real)
      _ ≤ (edgeBoundary G S).card := h_spectral
  · -- Case s < λ₂: LHS < 0 ≤ RHS
    push_neg at h_gap
    have h1a : (1 - α) * ((s : ℝ) - secondLargestEigenvalue G hcard) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) h_gap
    have h2a : (1 - α) * ((s : ℝ) - secondLargestEigenvalue G hcard) * S.card < 0 :=
      mul_neg_of_neg_of_pos h1a hS_pos_real
    linarith [Nat.cast_nonneg (α := ℝ) (edgeBoundary G S).card]

/-! ## Step 2: Upper bound on |δS| -/

/-- The upper bound `|δS| ≤ s|A| + (s-b)|B|` where `B = S \ A`. -/
lemma edgeBoundary_upper_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (b : ℝ) (hreg : G.IsRegularOfDegree s) (S : Finset V) :
    let A := highExpansionVertices G S s b
    ((edgeBoundary G S).card : ℝ) ≤
      (s : ℝ) * A.card + ((s : ℝ) - b) * (S.card - A.card) := by
  intro A
  have hA_sub : A ⊆ S := highExpansionVertices_subset G S s b
  -- Split sum over A and S \ A
  have hsum_split : (∑ v ∈ S, (edgeBoundaryAtVertex G S v).card : ℝ) =
      (∑ v ∈ A, (edgeBoundaryAtVertex G S v).card : ℝ) +
      (∑ v ∈ (S \ A), (edgeBoundaryAtVertex G S v).card : ℝ) := by
    push_cast
    rw [← Finset.sum_union (Finset.disjoint_sdiff)]
    congr 1
    exact (Finset.union_sdiff_of_subset hA_sub).symm
  -- Rewrite using partition
  have hpart_eq : ((edgeBoundary G S).card : ℝ) =
      (∑ v ∈ A, (edgeBoundaryAtVertex G S v).card : ℝ) +
      (∑ v ∈ (S \ A), (edgeBoundaryAtVertex G S v).card : ℝ) := by
    push_cast
    rw [edgeBoundary_partition_sum G S]
    exact_mod_cast hsum_split
  -- Bound sum over A: each term ≤ s
  have hA_bound : (∑ v ∈ A, (edgeBoundaryAtVertex G S v).card : ℝ) ≤ (s : ℝ) * A.card := by
    have h := Finset.sum_le_card_nsmul A (fun v => ((edgeBoundaryAtVertex G S v).card : ℝ)) (s : ℝ)
      (fun v _ => by simp only; exact_mod_cast edgeBoundaryAtVertex_le_degree G s hreg S v)
    simp only [nsmul_eq_mul] at h
    linarith
  -- Bound sum over B: each term < s - b, hence ≤ s - b
  have hB_bound : (∑ v ∈ (S \ A), (edgeBoundaryAtVertex G S v).card : ℝ) ≤
      ((s : ℝ) - b) * (S \ A).card := by
    have h := Finset.sum_le_card_nsmul (S \ A) (fun v => ((edgeBoundaryAtVertex G S v).card : ℝ))
      ((s : ℝ) - b) (fun v hv => by
        simp only
        have hv_not_A : v ∉ A := (Finset.mem_sdiff.mp hv).2
        have hv_S : v ∈ S := (Finset.mem_sdiff.mp hv).1
        have : ¬ ((s : ℝ) - b ≤ (edgeBoundaryAtVertex G S v).card) := by
          intro h_contra
          exact hv_not_A (Finset.mem_filter.mpr ⟨hv_S, h_contra⟩)
        exact le_of_lt (not_le.mp this))
    simp only [nsmul_eq_mul] at h
    linarith
  -- |S \ A| = |S| - |A|
  have hcard_sdiff : ((S \ A).card : ℝ) = S.card - A.card := by
    have h1 := Finset.card_sdiff_add_card_inter S A
    have hinter : A ∩ S = A := Finset.inter_eq_left.mpr hA_sub
    rw [Finset.inter_comm] at h1
    rw [hinter] at h1
    have h2 : (S \ A).card + A.card = S.card := h1
    have h3 : ((S \ A).card : ℝ) + (A.card : ℝ) = (S.card : ℝ) := by exact_mod_cast h2
    linarith
  rw [hcard_sdiff] at hB_bound
  linarith

/-! ## Main Theorem -/

/-- **Relative Vertex-to-Edge Expansion.** For a finite, connected, `s`-regular graph
with second-largest eigenvalue `λ₂`, `α ∈ (0,1)`, `S ⊆ V` with `|S| ≤ α|V|`,
and `0 < b ≤ s`, define `A = {v ∈ S | |(δS)_v| ≥ s - b}` and
`β = ((b - λ₂) - α(s - λ₂))/b`. Then `|A| ≥ β|S|`. -/
theorem relativeVertexToEdgeExpansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (α b : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hb0 : 0 < b) (hbs : b ≤ s)
    (hconn : G.Connected) (hreg : G.IsRegularOfDegree s)
    (hcard : 2 ≤ Fintype.card V)
    (S : Finset V) (hS_le : (S.card : ℝ) ≤ α * Fintype.card V) :
    let lam2 := secondLargestEigenvalue G hcard
    let A := highExpansionVertices G S s b
    ((b - lam2) - α * ((s : ℝ) - lam2)) / b * S.card ≤ A.card := by
  intro lam2 A
  -- Step 0: Trivial case S = ∅
  by_cases hS_pos : S.card = 0
  · simp [hS_pos]
  · push_neg at hS_pos
    have hS_pos' : 0 < S.card := Nat.pos_of_ne_zero hS_pos
    -- Step 3: Lower bound from relative Cheeger
    have h_lower := relativeCheeger_le G s α hα0 hα1 hconn hreg S hS_pos' hS_le hcard
    -- Step 2: Upper bound from partition
    have h_upper := edgeBoundary_upper_bound G s b hreg S
    -- Step 4-5: Combine and solve for |A|
    -- From h_lower: (1-α)(s-λ₂)|S| ≤ |δS|
    -- From h_upper: |δS| ≤ s|A| + (s-b)(|S|-|A|) = b|A| + (s-b)|S|
    -- So: (1-α)(s-λ₂)|S| ≤ b|A| + (s-b)|S|
    -- Thus: b|A| ≥ ((1-α)(s-λ₂) - (s-b))|S| = (b - λ₂ - α(s-λ₂))|S|
    -- Dividing by b > 0: |A| ≥ β|S|
    have h_combined : (1 - α) * ((s : ℝ) - lam2) * S.card ≤
        (s : ℝ) * (A.card : ℝ) + ((s : ℝ) - b) * ((S.card : ℝ) - (A.card : ℝ)) := by
      linarith
    -- Rearrange: b * A.card ≥ ((1-α)(s-λ₂) - (s-b)) * S.card
    have h_rearranged : b * (A.card : ℝ) ≥
        ((1 - α) * ((s : ℝ) - lam2) - ((s : ℝ) - b)) * S.card := by
      nlinarith
    -- Simplify the coefficient
    have h_coeff : (1 - α) * ((s : ℝ) - lam2) - ((s : ℝ) - b) =
        (b - lam2) - α * ((s : ℝ) - lam2) := by ring
    rw [h_coeff] at h_rearranged
    -- Divide by b
    rw [div_mul_eq_mul_div, div_le_iff₀ hb0, mul_comm]
    linarith

end RelativeVertexToEdgeExpansion
