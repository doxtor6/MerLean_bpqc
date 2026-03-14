import MerLeanBpqc.Theorems.Thm_6_AlonChung

/-!
# Corollary 1: Alon–Chung Contrapositive

## Main Results
- `incidentVertices`: The set of vertices incident to a set of edges.
- `alonChungContrapositive_direct`: If `E ⊆ X₁` is incident to at most `γ|X₀|` vertices,
  then `|E| ≤ α|X₁|`.
- `alonChungContrapositive`: If `|E| > α|X₁|`, then `E` is incident to more than `γ|X₀|`
  vertices.
-/

open SimpleGraph Fintype BigOperators Finset AlonChung GraphExpansion

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace AlonChungContrapositive

/-! ## Incident vertices of an edge set -/

/-- The set of vertices incident to a set of edges `E ⊆ X₁`:
`Γ(E) = {v ∈ X₀ | ∃ e ∈ E, v ∈ e}`. -/
def incidentVertices (E : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter (fun v => ∃ e ∈ E, v ∈ e)

lemma mem_incidentVertices (E : Finset (Sym2 V)) (v : V) :
    v ∈ incidentVertices E ↔ ∃ e ∈ E, v ∈ e := by
  simp [incidentVertices]

lemma incidentVertices_nonempty (E : Finset (Sym2 V))
    (h : ∃ e ∈ E, ∃ v : V, v ∈ e) : (incidentVertices E).Nonempty := by
  obtain ⟨e, he, v, hv⟩ := h
  exact ⟨v, (mem_incidentVertices E v).mpr ⟨e, he, hv⟩⟩

/-- Edges whose both endpoints lie in `incidentVertices E` include `E`. -/
lemma subset_inducedEdges_incidentVertices
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset (Sym2 V)) (hE : E ⊆ G.edgeFinset) :
    E ⊆ inducedEdges G (incidentVertices E) := by
  intro e he
  rw [mem_inducedEdges]
  refine ⟨hE he, fun v hv => ?_⟩
  rw [mem_incidentVertices]
  exact ⟨e, he, hv⟩

/-! ## Monotonicity of f(t) = t² + (λ₂/s) t(1-t) -/

/-- The function `f(t) = t² + c·t·(1-t) = (1-c)t² + c·t` is non-decreasing on `[0,∞)`
when `0 ≤ c ≤ 1`. -/
lemma alpha_mono {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ 2 + c * a * (1 - a) ≤ b ^ 2 + c * b * (1 - b) := by
  -- f(b) - f(a) = (1-c)(b²-a²) + c(b-a) = (b-a)((1-c)(b+a) + c) ≥ 0
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (b - a), mul_nonneg (sub_nonneg.mpr hab) (add_nonneg (mul_nonneg (sub_nonneg.mpr hc1) (add_nonneg ha (le_trans ha hab))) hc0)]

/-! ## Direct form: incident to at most γ|V| vertices implies |E| ≤ α|X₁| -/

/-- **Alon–Chung Contrapositive (direct form).** If `E ⊆ X₁` is incident to at most
`γ|X₀|` vertices, then `|E| ≤ α|X₁|` where `α = γ² + (λ₂/s)γ(1-γ)`. -/
theorem alonChungContrapositive_direct
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s) (hreg : G.IsRegularOfDegree s)
    (hcard : 2 ≤ Fintype.card V)
    (E : Finset (Sym2 V)) (hE : E ⊆ G.edgeFinset)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (lam₂ : ℝ) (hlam₂ : lam₂ = secondLargestEigenvalue G hcard)
    (hlam₂_nn : 0 ≤ lam₂)
    (hincident : ((incidentVertices E).card : ℝ) ≤ γ * Fintype.card V) :
    (E.card : ℝ) ≤ (γ ^ 2 + (lam₂ / ↑s) * γ * (1 - γ)) * G.edgeFinset.card := by
  -- Let S = incidentVertices E
  set S := incidentVertices E with hS_def
  -- Case: S = ∅
  by_cases hS_empty : S = ∅
  · -- E = ∅ since every edge has endpoints in S
    have hE_empty : E = ∅ := by
      by_contra hne
      have hne' : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨e, he⟩ := hne'
      have he_edge := hE he
      rw [SimpleGraph.mem_edgeFinset] at he_edge
      induction e using Sym2.ind with
      | h v w =>
      have hv : v ∈ S := (mem_incidentVertices E v).mpr ⟨s(v, w), he, Sym2.mem_mk_left v w⟩
      simp [hS_empty] at hv
    rw [hE_empty]; simp
    apply mul_nonneg
    · -- α ≥ 0
      have hs_pos : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega)
      have h1 : (0 : ℝ) ≤ lam₂ / ↑s := div_nonneg hlam₂_nn (le_of_lt hs_pos)
      have h2 : (0 : ℝ) ≤ 1 - γ := le_of_lt (sub_pos.mpr hγ1)
      nlinarith [sq_nonneg γ, mul_nonneg (mul_nonneg h1 (le_of_lt hγ0)) h2]
    · exact Nat.cast_nonneg _
  · -- S ≠ ∅, so S is nonempty
    have hS_empty := Finset.nonempty_iff_ne_empty.mpr hS_empty
    -- Set γ' = |S|/|V|, so 0 < γ' ≤ γ < 1
    set n := (Fintype.card V : ℝ) with hn_def
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    set γ' := (S.card : ℝ) / n with hγ'_def
    have hγ'_pos : 0 < γ' := by
      rw [hγ'_def]; exact div_pos (Nat.cast_pos.mpr (Finset.Nonempty.card_pos hS_empty)) hn_pos
    have hγ'_le_γ : γ' ≤ γ := by
      rw [hγ'_def]; rwa [div_le_iff₀ hn_pos]
    have hS_lt_V : S.card < Fintype.card V := by
      by_contra h
      push_neg at h
      have := Finset.card_le_card (Finset.subset_univ S)
      rw [Finset.card_univ] at this
      have hle : (Fintype.card V : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast h
      have hγV : (Fintype.card V : ℝ) ≤ γ * (Fintype.card V : ℝ) := le_trans hle hincident
      have hV_pos : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr (by omega)
      have : 1 ≤ γ := by
        rwa [← div_le_iff₀ hV_pos, div_self (ne_of_gt hV_pos)] at hγV
      linarith
    -- E ⊆ inducedEdges G S
    have hE_sub : E ⊆ inducedEdges G S :=
      subset_inducedEdges_incidentVertices G E hE
    -- |E| ≤ |inducedEdges G S|
    have hE_card : (E.card : ℝ) ≤ (inducedEdges G S).card := by
      exact_mod_cast Finset.card_le_card hE_sub
    -- Apply Alon–Chung to S with γ'
    have hAC := alonChung G s hs hreg hcard S hS_empty hS_lt_V
    -- hAC says: inducedEdges G S ≤ α' * |X₁| where α' = γ'² + (λ₂/s)γ'(1-γ')
    -- and γ' = |S|/n, lam₂_AC = secondLargestEigenvalue G hcard
    set α' := γ' ^ 2 + (secondLargestEigenvalue G hcard / ↑s) * γ' * (1 - γ') with hα'_def
    -- Monotonicity: α' ≤ α since γ' ≤ γ
    have hlam₂_le_s : lam₂ / ↑s ≤ 1 := by
      rw [div_le_one (Nat.cast_pos.mpr (by omega) : (0 : ℝ) < s)]
      rw [hlam₂]
      have h_max := max_eigenvalue_eq_degree G s hreg hcard
      show secondLargestEigenvalue G hcard ≤ ↑s
      unfold secondLargestEigenvalue
      have h_anti : adjEigenvalues G ⟨1, by omega⟩ ≤ adjEigenvalues G ⟨0, by omega⟩ :=
        adjEigenvalues_antitone G (show (⟨0, by omega⟩ : Fin (Fintype.card V)) ≤ ⟨1, by omega⟩ from Fin.mk_le_mk.mpr (by norm_num))
      linarith
    have hα'_le_α : α' ≤ γ ^ 2 + (lam₂ / ↑s) * γ * (1 - γ) := by
      rw [hα'_def, hlam₂]
      exact alpha_mono
        (div_nonneg (hlam₂ ▸ hlam₂_nn) (Nat.cast_nonneg _))
        (hlam₂ ▸ hlam₂_le_s)
        (le_of_lt hγ'_pos) hγ'_le_γ
    -- Combine: |E| ≤ |X(S)₁| ≤ α'|X₁| ≤ α|X₁|
    calc (E.card : ℝ) ≤ (inducedEdges G S).card := hE_card
      _ ≤ α' * G.edgeFinset.card := hAC
      _ ≤ (γ ^ 2 + (lam₂ / ↑s) * γ * (1 - γ)) * G.edgeFinset.card := by
          apply mul_le_mul_of_nonneg_right hα'_le_α (Nat.cast_nonneg _)

/-- **Alon–Chung Contrapositive.** If `|E| > α|X₁|`, then `E` is incident to more than
`γ|X₀|` vertices. -/
theorem alonChungContrapositive
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s) (hreg : G.IsRegularOfDegree s)
    (hcard : 2 ≤ Fintype.card V)
    (E : Finset (Sym2 V)) (hE : E ⊆ G.edgeFinset)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (lam₂ : ℝ) (hlam₂ : lam₂ = secondLargestEigenvalue G hcard)
    (hlam₂_nn : 0 ≤ lam₂)
    (hE_large : (E.card : ℝ) > (γ ^ 2 + (lam₂ / ↑s) * γ * (1 - γ)) * G.edgeFinset.card) :
    ((incidentVertices E).card : ℝ) > γ * Fintype.card V := by
  by_contra h
  push_neg at h
  have := alonChungContrapositive_direct G s hs hreg hcard E hE γ hγ0 hγ1 lam₂ hlam₂ hlam₂_nn h
  linarith

end AlonChungContrapositive
