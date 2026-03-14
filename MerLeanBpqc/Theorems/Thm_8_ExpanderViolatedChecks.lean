import MerLeanBpqc.Theorems.Thm_7_SipserSpielmanExpanderCodeDistance
import MerLeanBpqc.Lemmas.Lem_2_EdgeToVertexExpansion
import MerLeanBpqc.Lemmas.Lem_3_RelativeVertexToEdgeExpansion

/-!
# Theorem 8: Expander Violated Checks

For a Tanner code on an expander graph, a vector `x` of small Hamming weight
has `|∂(x)| ≥ β|x|`, where `β = β' · β''` combines edge-to-vertex expansion (Lem_2)
with vertex-to-edge-boundary expansion (Lem_3).

## Main Results
- `expanderViolatedChecks`: The main bound `|∂(x)| ≥ β' · β'' · |x|`.
-/

set_option maxRecDepth 1024
set_option maxHeartbeats 1600000

open SimpleGraph Fintype BigOperators Finset Classical
open EdgeToVertexExpansion RelativeVertexToEdgeExpansion SipserSpielman
open GraphExpansion AlonChungContrapositive

namespace ExpanderViolatedChecks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## β parameters -/

/-- The edge-to-vertex expansion parameter β':
`β' = (sqrt(λ₂² + 4s(s-λ₂)α) - λ₂) / (s(s-λ₂)α)`. -/
noncomputable def beta' (s : ℝ) (lam2 : ℝ) (alpha : ℝ) : ℝ :=
  betaParam s lam2 alpha

/-- The vertex-to-edge-boundary expansion parameter β'':
`β'' = ((dL - 1 - λ₂) - αs(s - λ₂)) / (dL - 1)`.
This is obtained by applying Lem_3 with `b = dL - 1` and `α' = αs`.
Note: The paper's stated formula uses `4α/s` and denominator `dL`, but the
proof derivation yields `αs` (since `|S| ≤ 2α|X₁| = αs|X₀|`) and
uses `b = dL - 1` to ensure all high-expansion vertices have violated checks. -/
noncomputable def beta'' (s : ℝ) (lam2 : ℝ) (alpha : ℝ) (dL : ℝ) : ℝ :=
  ((dL - 1 - lam2) - alpha * s * (s - lam2)) / (dL - 1)

/-! ## Hamming weight of the differential image -/

/-- The Hamming weight of the differential output `∂(x)`, counting the number of
vertices `v` where the local check `parityCheck(localView_v(x))` is nonzero. -/
noncomputable def differentialWeight
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (Λ : Labeling G (s := s))
    {m : ℕ} (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (x : G.edgeSet → 𝔽₂) : ℕ :=
  (Finset.univ.filter (fun v : V => parityCheck (localView Λ v x) ≠ 0)).card

/-! ## Helper: vertices in A have violated checks -/

/-- For a vertex `v ∈ A` (high expansion), if `v` is incident to at most `dL - 1`
edges in the support of `x`, then the local check at `v` is violated. -/
lemma violated_check_of_small_support
    {s : ℕ} (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (dL : ℕ) (hdL : dL = ClassicalCode.distance (ClassicalCode.ofParityCheck parityCheck))
    (hdL_pos : 0 < dL)
    (x : Fin s → 𝔽₂) (hx_ne : x ≠ 0)
    (hx_wt : hammingWeight x ≤ dL - 1) :
    parityCheck x ≠ 0 := by
  intro h_eq
  -- x ∈ ker(parityCheck) = code, x ≠ 0, so wt(x) ≥ dL
  have hmem : x ∈ (ClassicalCode.ofParityCheck parityCheck).code := by
    rw [ClassicalCode.code_eq_ker]; exact h_eq
  have h_dist := ClassicalCode.distance (ClassicalCode.ofParityCheck parityCheck)
  -- dL ≤ wt(x) ≤ dL - 1, contradiction
  unfold ClassicalCode.distance at hdL
  have h_ge : dL ≤ hammingWeight x := by
    rw [hdL]
    apply Nat.sInf_le
    exact ⟨x, hmem, hx_ne, rfl⟩
  omega

/-! ## Helper: counting edges within S incident to v -/

/-- The number of edges in `supportEdges` incident to vertex `v`. -/
noncomputable def supportEdgesAtVertex
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.edgeSet → 𝔽₂) (v : V) : ℕ :=
  ((supportEdges G c).filter (fun e => v ∈ e)).card

/-! ## Helper: edges in support are within S = incidentToSupport -/

/-- Every edge in the support has both endpoints in the incident vertex set S. -/
lemma supportEdges_both_endpoints_in_S
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.edgeSet → 𝔽₂) (e : Sym2 V) (he : e ∈ supportEdges G c)
    (w : V) (hw : w ∈ e) :
    w ∈ incidentToSupport G c := by
  simp only [incidentToSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [supportEdges, Finset.mem_image] at he
  obtain ⟨⟨e', he'prop⟩, he'mem, rfl⟩ := he
  simp only [SipserSpielman.support, Finset.mem_filter, Finset.mem_univ, true_and] at he'mem
  exact ⟨⟨e', he'prop⟩, he'mem, hw⟩

/-! ## Helper: support edges are disjoint from edge boundary -/

/-- Edges in the support are NOT in the edge boundary δS, since both endpoints are in S. -/
lemma supportEdge_not_in_edgeBoundary
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.edgeSet → 𝔽₂) (e : Sym2 V) (he : e ∈ supportEdges G c) :
    e ∉ CheegerConstant.edgeBoundary G (incidentToSupport G c) := by
  intro h_bd
  rw [CheegerConstant.mem_edgeBoundary] at h_bd
  obtain ⟨_, a, b, hab, ha, hb⟩ := h_bd
  subst hab
  exact hb (supportEdges_both_endpoints_in_S G c _ he b (Sym2.mem_mk_right a b))

/-! ## Helper: edges at v split into boundary and within-S -/

/-- For v ∈ S, the number of within-S edges at v plus boundary edges at v equals the degree s. -/
lemma withinS_plus_boundary_eq_degree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hreg : G.IsRegularOfDegree s)
    (S : Finset V) (v : V) (hv : v ∈ S) :
    let withinS := (G.edgeFinset.filter (fun e => v ∈ e ∧ ∀ w ∈ e, w ∈ S)).card
    let boundary := (edgeBoundaryAtVertex G S v).card
    let otherS := (G.edgeFinset.filter (fun e => v ∈ e ∧ (∀ w ∈ e, w ∈ S) ∧
      ¬(∃ w ∈ e, w ∉ S))).card
    boundary + withinS ≤ s := by
  intro withinS boundary otherS
  -- Both are subsets of incidenceFinset v
  have h1 : (edgeBoundaryAtVertex G S v) ⊆ G.incidenceFinset v := by
    intro e he
    simp only [edgeBoundaryAtVertex, Finset.mem_filter] at he
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨G.mem_edgeFinset.mp (CheegerConstant.edgeBoundary_subset_edgeFinset G S he.1), he.2⟩
  have h2 : (G.edgeFinset.filter (fun e => v ∈ e ∧ ∀ w ∈ e, w ∈ S)) ⊆
    G.incidenceFinset v := by
    intro e he
    simp only [Finset.mem_filter] at he
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨G.mem_edgeFinset.mp he.1, he.2.1⟩
  -- They are disjoint
  have h3 : Disjoint (edgeBoundaryAtVertex G S v)
    (G.edgeFinset.filter (fun e => v ∈ e ∧ ∀ w ∈ e, w ∈ S)) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [edgeBoundaryAtVertex, Finset.mem_filter] at he1
    simp only [Finset.mem_filter] at he2
    -- he1.1 ∈ edgeBoundary G S, so ∃ a ∈ S, b ∉ S
    rw [CheegerConstant.mem_edgeBoundary] at he1
    obtain ⟨⟨_, a, b, hab, _, hb⟩, _⟩ := he1
    subst hab
    exact hb (he2.2.2 b (Sym2.mem_mk_right a b))
  calc boundary + withinS
      = (edgeBoundaryAtVertex G S v ∪ G.edgeFinset.filter (fun e => v ∈ e ∧ ∀ w ∈ e, w ∈ S)).card := by
        rw [Finset.card_union_of_disjoint h3]
    _ ≤ (G.incidenceFinset v).card := Finset.card_le_card (Finset.union_subset h1 h2)
    _ = G.degree v := G.card_incidenceFinset_eq_degree v
    _ = s := hreg v

/-! ## Helper: Hamming weight of localView bounded by non-boundary edges -/

/-- The Hamming weight of the local view at v is at most the number of within-S
edges at v. Combined with `withinS_plus_boundary_eq_degree`, this gives
`hammingWeight(localView v c) ≤ s - |(δS)_v|`. -/
lemma localView_weight_le_withinS
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (Λ : Labeling G (s := s))
    (c : G.edgeSet → 𝔽₂) (S : Finset V)
    (hsupp : ∀ (e : G.edgeSet), c e ≠ 0 → ∀ w ∈ (e.val : Sym2 V), w ∈ S) :
    ∀ v : V, hammingWeight (localView Λ v c) ≤
      (G.edgeFinset.filter (fun e => v ∈ e ∧ ∀ w ∈ e, w ∈ S)).card := by
  intro v
  -- hammingWeight = |{i : Fin s | localView Λ v c i ≠ 0}|
  simp only [hammingWeight, hammingNorm, hammingDist]
  -- Map each support index i to the corresponding edge s(v, (Λ v)⁻¹(i))
  let mapEdge : Fin s → Sym2 V := fun i => s(v, ((Λ v).symm i).val)
  let suppIdx := Finset.univ.filter (fun i : Fin s => localView Λ v c i ≠ 0)
  let withinS := G.edgeFinset.filter (fun e => v ∈ e ∧ ∀ w ∈ e, w ∈ S)
  -- Show suppIdx maps into withinS
  have h_image : suppIdx.image mapEdge ⊆ withinS := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨i, hi, rfl⟩ := he
    rw [Finset.mem_filter] at hi ⊢
    simp only [Finset.mem_univ, true_and] at hi
    constructor
    · -- edge is in G.edgeFinset
      rw [SimpleGraph.mem_edgeFinset]
      exact G.mem_edgeSet.mpr ((Λ v).symm i).prop
    constructor
    · -- v ∈ edge
      exact Sym2.mem_mk_left v ((Λ v).symm i).val
    · -- all endpoints in S
      intro w hw
      have hci : c ⟨s(v, ((Λ v).symm i).val), G.mem_edgeSet.mpr ((Λ v).symm i).prop⟩ ≠ 0 := by
        exact hi
      exact hsupp ⟨_, G.mem_edgeSet.mpr ((Λ v).symm i).prop⟩ hci w hw
  -- Map is injective on suppIdx
  have h_inj : Set.InjOn mapEdge ↑suppIdx := by
    intro i _ j _ hij
    simp only [mapEdge] at hij
    have h1 := ((Λ v).symm i).prop  -- G.Adj v ((Λ v).symm i).val
    have h2 := ((Λ v).symm j).prop  -- G.Adj v ((Λ v).symm j).val
    have hne_i : v ≠ ((Λ v).symm i).val := G.ne_of_adj h1
    -- s(v, w₁) = s(v, w₂) with v ≠ w₁ implies w₁ = w₂
    have := Sym2.mk_eq_mk_iff.mp hij
    cases this with
    | inl h => exact (Λ v).symm.injective (Subtype.ext (Prod.mk.inj h).2)
    | inr h =>
      simp only [Prod.swap] at h
      exact absurd (Prod.mk.inj h).2.symm hne_i
  -- Cardinality chain
  have h1 : suppIdx.card = (suppIdx.image mapEdge).card :=
    (Finset.card_image_of_injOn h_inj).symm
  -- The goal is now #{i | (localView Λ v) c i ≠ 0} ≤ #withinS = suppIdx.card
  calc #{i | (localView Λ v) c i ≠ 0}
      = suppIdx.card := rfl
    _ = (suppIdx.image mapEdge).card := h1
    _ ≤ withinS.card := Finset.card_le_card h_image

/-- Combined: Hamming weight of localView + boundary edges ≤ s. -/
lemma localView_weight_add_boundary_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (Λ : Labeling G (s := s)) (hreg : G.IsRegularOfDegree s)
    (c : G.edgeSet → 𝔽₂) (S : Finset V) (v : V) (hv : v ∈ S)
    (hsupp : ∀ (e : G.edgeSet), c e ≠ 0 → ∀ w ∈ (e.val : Sym2 V), w ∈ S) :
    hammingWeight (localView Λ v c) + (edgeBoundaryAtVertex G S v).card ≤ s := by
  have h1 := localView_weight_le_withinS G Λ c S hsupp v
  have h2 := withinS_plus_boundary_eq_degree G s hreg S v hv
  omega

/-! ## Connection lemmas -/

/-- The card of `supportEdges` equals `edgeHammingWeight`. -/
lemma supportEdges_card_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.edgeSet → 𝔽₂) :
    (supportEdges G c).card = edgeHammingWeight G c := by
  simp only [supportEdges, edgeHammingWeight]
  exact Finset.card_image_of_injective _ Subtype.val_injective

/-- `incidentToSupport` equals `incidentVertices` of `supportEdges`. -/
lemma incidentToSupport_eq_incidentVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.edgeSet → 𝔽₂) :
    incidentToSupport G c = AlonChungContrapositive.incidentVertices (supportEdges G c) := by
  ext v
  simp only [incidentToSupport, AlonChungContrapositive.incidentVertices,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, hce, hve⟩
    exact ⟨e.val, Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hce⟩, rfl⟩, hve⟩
  · rintro ⟨e, he, hve⟩
    simp only [supportEdges, Finset.mem_image] at he
    obtain ⟨⟨e', he'⟩, hmem, rfl⟩ := he
    simp only [SipserSpielman.support, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact ⟨⟨e', he'⟩, hmem, hve⟩

/-- Handshaking lemma for regular graphs: `2 * |E| = s * |V|`. -/
lemma regular_handshaking (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hreg : G.IsRegularOfDegree s) :
    2 * G.edgeFinset.card = s * Fintype.card V := by
  have h := G.sum_degrees_eq_twice_card_edges
  simp only [hreg.degree_eq] at h
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  linarith

/-- `|incidentToSupport G c| ≤ 2 * |support G c|` (each edge contributes ≤ 2 vertices). -/
lemma incidentToSupport_card_le_twice (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.edgeSet → 𝔽₂) :
    (incidentToSupport G c).card ≤ 2 * edgeHammingWeight G c := by
  rw [incidentToSupport_eq_incidentVertices, ← supportEdges_card_eq]
  -- incidentVertices E ⊆ biUnion over E of edgeVerts
  set E := supportEdges G c
  have h_sub : AlonChungContrapositive.incidentVertices E ⊆
      E.biUnion (fun e => Finset.univ.filter (fun v => v ∈ e)) := by
    intro v hv
    rw [AlonChungContrapositive.mem_incidentVertices] at hv
    rw [Finset.mem_biUnion]
    obtain ⟨e, he, hve⟩ := hv
    exact ⟨e, he, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hve⟩⟩
  have h_card : ∀ e ∈ E, (Finset.univ.filter (fun v => v ∈ e)).card ≤ 2 := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have h_sub : Finset.univ.filter (fun v => v ∈ s(a, b)) ⊆ ({a, b} : Finset V) := by
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Sym2.mem_iff.mp hv
      calc (Finset.univ.filter (fun v => v ∈ s(a, b))).card
          ≤ ({a, b} : Finset V).card := Finset.card_le_card h_sub
        _ ≤ 2 := Finset.card_le_two
  calc (AlonChungContrapositive.incidentVertices E).card
      ≤ (E.biUnion (fun e => Finset.univ.filter (fun v => v ∈ e))).card :=
        Finset.card_le_card h_sub
    _ ≤ ∑ e ∈ E, (Finset.univ.filter (fun v => v ∈ e)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ E, 2 := Finset.sum_le_sum h_card
    _ = 2 * E.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- `|S| ≤ αs · |V|` where `S = incidentToSupport G x`. -/
lemma incidentToSupport_card_le_alphaS
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hreg : G.IsRegularOfDegree s)
    (alpha : ℝ) (halpha_pos : 0 < alpha)
    (x : G.edgeSet → 𝔽₂)
    (hx_le : (edgeHammingWeight G x : ℝ) ≤ alpha * G.edgeFinset.card) :
    ((incidentToSupport G x).card : ℝ) ≤ alpha * s * Fintype.card V := by
  have h1 := incidentToSupport_card_le_twice G x
  have h2 := regular_handshaking G s hreg
  -- |S| ≤ 2|E|, |E| ≤ α|X₁|, 2|X₁| = s|V|
  -- So |S| ≤ 2α|X₁| = αs|V|
  calc ((incidentToSupport G x).card : ℝ)
      ≤ 2 * edgeHammingWeight G x := by exact_mod_cast h1
    _ ≤ 2 * (alpha * G.edgeFinset.card) := by nlinarith
    _ = alpha * (2 * G.edgeFinset.card) := by ring
    _ = alpha * (s * Fintype.card V) := by
        congr 1; exact_mod_cast h2
    _ = alpha * s * Fintype.card V := by ring

/-! ## Violated checks at high-expansion vertices -/

/-- For `v ∈ incidentToSupport G c`, the local view `localView Λ v c` is nonzero. -/
lemma localView_ne_zero_of_incidentToSupport
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (Λ : Labeling G (s := s))
    (c : G.edgeSet → 𝔽₂) (v : V) (hv : v ∈ incidentToSupport G c) :
    localView Λ v c ≠ 0 := by
  simp only [incidentToSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨⟨e, he_mem⟩, hce, hve⟩ := hv
  -- e is an edge with c(e) ≠ 0 and v ∈ e
  -- The labeling assigns e to some index i, and localView v c i = c(e) ≠ 0
  intro h_eq
  -- If localView is zero, then all components are zero
  have h_all_zero : ∀ i : Fin s, localView Λ v c i = 0 := by
    intro i; exact congr_fun h_eq i
  -- Get the neighbor w such that e = s(v, w)
  have hve' : v ∈ (e : Sym2 V) := hve
  have h_adj : ∃ w, G.Adj v w ∧ (e : Sym2 V) = s(v, w) := by
    rw [Sym2.mem_iff_exists] at hve'
    obtain ⟨w, rfl⟩ := hve'
    exact ⟨w, G.mem_edgeSet.mp he_mem, rfl⟩
  obtain ⟨w, hadj, _⟩ := h_adj
  -- The index assigned to w by the labeling
  let i : Fin s := (Λ v) ⟨w, hadj⟩
  have h_lv : localView Λ v c i = c ⟨s(v, w), G.mem_edgeSet.mpr hadj⟩ := by
    simp only [localView, i]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply]
  -- But c(e) ≠ 0 and e = s(v, w), so localView v c i ≠ 0
  have h_eq_edge : (⟨s(v, w), G.mem_edgeSet.mpr hadj⟩ : G.edgeSet) = ⟨e, he_mem⟩ := by
    ext; simp [‹(e : Sym2 V) = s(v, w)›]
  have h_zero_i := h_all_zero i
  rw [h_lv, h_eq_edge] at h_zero_i
  exact hce h_zero_i

/-- The `differentialWeight` is at least the number of high-expansion vertices
(with parameter `b = dL - 1`). Each such vertex has a violated local check. -/
lemma differentialWeight_ge_highExpansion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (Λ : Labeling G (s := s)) (hreg : G.IsRegularOfDegree s)
    {m : ℕ} (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (c : G.edgeSet → 𝔽₂)
    (dL : ℕ) (hdL : dL = ClassicalCode.distance (ClassicalCode.ofParityCheck parityCheck))
    (hdL_pos : 0 < dL) :
    let S := incidentToSupport G c
    let A := highExpansionVertices G S s (↑dL - 1 : ℝ)
    A.card ≤ differentialWeight G Λ parityCheck c := by
  intro S A
  -- Show A ⊆ {v | parityCheck (localView Λ v c) ≠ 0}
  apply Finset.card_le_card
  intro v hv
  simp only [differentialWeight, Finset.mem_filter, Finset.mem_univ, true_and]
  -- v ∈ A means v ∈ S and |(δS)_v| ≥ s - (dL - 1)
  have hv_S : v ∈ S := highExpansionVertices_subset G S s (↑dL - 1) hv
  have hv_bdy : (s : ℝ) - (↑dL - 1) ≤ (edgeBoundaryAtVertex G S v).card := by
    have hv' : v ∈ highExpansionVertices G S s (↑dL - 1) := hv
    simp only [highExpansionVertices, Finset.mem_filter] at hv'
    exact hv'.2
  -- Support edges are within S
  have hsupp : ∀ (e : G.edgeSet), c e ≠ 0 → ∀ w ∈ (e.val : Sym2 V), w ∈ S := by
    intro e hce w hw
    show w ∈ incidentToSupport G c
    simp only [incidentToSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e, hce, hw⟩
  -- Hamming weight bound
  have h_wt_bdy := localView_weight_add_boundary_le G Λ hreg c S v hv_S hsupp
  -- So hammingWeight ≤ s - |(δS)_v| ≤ dL - 1
  have h_wt_le : hammingWeight (localView Λ v c) ≤ dL - 1 := by
    suffices h : (↑(hammingWeight (localView Λ v c)) : ℝ) ≤ ↑(dL - 1) by exact_mod_cast h
    have h1 : (↑(dL - 1) : ℝ) = ↑dL - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ dL)]; simp
    rw [h1]
    have : (↑(hammingWeight (localView Λ v c)) + ↑(edgeBoundaryAtVertex G S v).card : ℝ) ≤ ↑s := by
      exact_mod_cast h_wt_bdy
    linarith
  -- localView is nonzero
  have h_ne_zero := localView_ne_zero_of_incidentToSupport G Λ c v hv_S
  -- Apply violated_check_of_small_support
  exact violated_check_of_small_support parityCheck dL hdL hdL_pos
    (localView Λ v c) h_ne_zero h_wt_le

/-! ## Main Theorem -/

/-- β' is positive when s ≥ 1, λ₂ < s, and α > 0. The discriminant
λ₂² + 4s(s-λ₂)α > λ₂², so √(disc) > |λ₂| ≥ λ₂ (numerator > 0)
and s(s-λ₂)α > 0 (denominator > 0). -/
lemma beta'_pos (s : ℕ) (lam2 alpha : ℝ)
    (hs : 1 ≤ s) (hlam2_lt_s : lam2 < ↑s) (halpha_pos : 0 < alpha) :
    0 < beta' (↑s) lam2 alpha := by
  unfold beta' betaParam
  have hs_pos : (0 : ℝ) < ↑s := Nat.cast_pos.mpr (by omega)
  have h_slm : (0 : ℝ) < ↑s - lam2 := sub_pos.mpr hlam2_lt_s
  -- Denominator is positive
  have h_denom_pos : 0 < ↑s * (↑s - lam2) * alpha := by positivity
  rw [div_pos_iff_of_pos_right h_denom_pos]
  -- Need: sqrt(lam2² + 4s(s-lam2)α) > lam2
  have h_extra : 0 < 4 * ↑s * (↑s - lam2) * alpha := by positivity
  have h_disc_gt : lam2 ^ 2 < lam2 ^ 2 + 4 * ↑s * (↑s - lam2) * alpha := by linarith
  by_cases hlam : 0 ≤ lam2
  · -- lam2 ≥ 0: sqrt(disc) > sqrt(lam2²) = lam2
    have h1 : Real.sqrt (lam2 ^ 2) = lam2 := Real.sqrt_sq hlam
    have h2 : Real.sqrt (lam2 ^ 2) < Real.sqrt (lam2 ^ 2 + 4 * ↑s * (↑s - lam2) * alpha) :=
      Real.sqrt_lt_sqrt (sq_nonneg _) h_disc_gt
    linarith
  · -- lam2 < 0: sqrt(disc) ≥ 0 > lam2
    push_neg at hlam
    have : 0 ≤ Real.sqrt (lam2 ^ 2 + 4 * ↑s * (↑s - lam2) * alpha) := Real.sqrt_nonneg _
    linarith

/-- **Expander Violated Checks (Theorem 8).** For a Tanner code on an `s`-regular
expander graph with second-largest eigenvalue `λ₂`, local code distance `dL ≤ s`,
and a vector `x` with `|x| ≤ α|X₁|`, we have `|∂(x)| ≥ β' · β'' · |x|`
where `β' = (√(λ₂² + 4s(s-λ₂)α) - λ₂) / (s(s-λ₂)α)` and
`β'' = ((dL - 1 - λ₂) - αs(s - λ₂)) / (dL - 1)`.
-/

theorem expanderViolatedChecks
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (s : ℕ) (hs : 1 ≤ s) (hreg : G.IsRegularOfDegree s)
    (hcard : 2 ≤ Fintype.card V)
    {m : ℕ} (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (Λ : Labeling G (s := s))
    (dL : ℕ) (hdL : dL = ClassicalCode.distance (ClassicalCode.ofParityCheck parityCheck))
    (hdL_pos : 0 < dL) (hdL_le_s : dL ≤ s)
    (lam2 : ℝ) (hlam2 : lam2 = secondLargestEigenvalue G hcard)
    (hlam2_lt_s : lam2 < s)
    (alpha : ℝ) (halpha_pos : 0 < alpha) (halpha_le : alpha ≤ 1)
    (x : G.edgeSet → 𝔽₂)
    (hx_le : (edgeHammingWeight G x : ℝ) ≤ alpha * G.edgeFinset.card) :
    (differentialWeight G Λ parityCheck x : ℝ) ≥
      beta' s lam2 alpha * beta'' s lam2 alpha dL * edgeHammingWeight G x := by
  -- Trivial case: when β'β'' ≤ 0, the bound holds since |∂(x)| ≥ 0
  -- This covers αs ≥ 1 (β'' ≤ 0) and dL = 1 (β'' = 0/0 = 0 in Lean).
  by_cases h_beta_nn : beta' ↑s lam2 alpha * beta'' ↑s lam2 alpha ↑dL ≤ 0
  · have : beta' ↑s lam2 alpha * beta'' ↑s lam2 alpha ↑dL *
        edgeHammingWeight G x ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h_beta_nn (Nat.cast_nonneg _)
    have : (0 : ℝ) ≤ ↑(differentialWeight G Λ parityCheck x) := Nat.cast_nonneg _
    linarith
  -- Now β'β'' > 0, which requires αs < 1 and dL ≥ 2
  push_neg at h_beta_nn
  -- Derive αs < 1 from β'β'' > 0
  have h_beta'_pos : 0 < beta' ↑s lam2 alpha :=
    beta'_pos s lam2 alpha hs hlam2_lt_s halpha_pos
  have h_beta''_pos : 0 < beta'' ↑s lam2 alpha ↑dL := by
    by_contra h_neg
    push_neg at h_neg
    have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_beta'_pos) h_neg
    linarith
  -- β'' > 0 implies dL ≥ 2 and αs < 1
  have hdL_ge_two : 2 ≤ dL := by
    -- β'' = ((dL-1-λ₂) - αs(s-λ₂))/(dL-1) > 0 requires dL-1 > 0, i.e., dL ≥ 2
    -- If dL = 0, contradicts hdL_pos. If dL = 1, dL-1 = 0 so β'' = x/0 = 0 in Lean.
    by_contra h
    push_neg at h
    interval_cases dL
    · -- dL = 1: β'' = ((1-1-λ₂) - αs(s-λ₂))/(1-1) = _/0 = 0
      simp only [beta'', Nat.cast_one] at h_beta''_pos
      have : (1 : ℝ) - 1 = 0 := sub_self 1
      rw [this, div_zero] at h_beta''_pos
      exact lt_irrefl 0 h_beta''_pos
  have halpha_s_lt_one : alpha * ↑s < 1 := by
    -- β'' > 0 with dL ≤ s implies αs < 1
    -- β'' = ((dL-1-λ₂) - αs(s-λ₂))/(dL-1) > 0
    -- Since dL ≥ 2, dL-1 > 0, so numerator > 0:
    --   (dL-1-λ₂) > αs(s-λ₂)
    -- Since dL ≤ s: dL-1 ≤ s-1 < s, so dL-1-λ₂ < s-λ₂
    -- If αs ≥ 1: αs(s-λ₂) ≥ s-λ₂ > dL-1-λ₂, contradicting numerator > 0
    by_contra h
    push_neg at h  -- h : 1 ≤ alpha * ↑s
    have h_dL1_pos : (0 : ℝ) < ↑dL - 1 := by
      have : (2 : ℝ) ≤ ↑dL := by exact_mod_cast hdL_ge_two
      linarith
    have h_num_pos : 0 < (↑dL - 1 - lam2) - alpha * ↑s * (↑s - lam2) := by
      rwa [beta'', div_pos_iff_of_pos_right h_dL1_pos] at h_beta''_pos
    have h_slm_pos : (0 : ℝ) < ↑s - lam2 := sub_pos.mpr hlam2_lt_s
    -- αs ≥ 1 implies αs(s-λ₂) ≥ s-λ₂
    have h1 : (↑s - lam2) ≤ alpha * ↑s * (↑s - lam2) :=
      le_mul_of_one_le_left (le_of_lt h_slm_pos) h
    -- dL ≤ s implies dL-1 ≤ s-1 < s, so dL-1-λ₂ < s-λ₂
    have h2 : (↑dL : ℝ) - 1 - lam2 ≤ ↑s - lam2 := by
      have : (↑dL : ℝ) ≤ ↑s := by exact_mod_cast hdL_le_s
      linarith
    -- Combining: (dL-1-λ₂) ≤ (s-λ₂) ≤ αs(s-λ₂), contradicting numerator > 0
    linarith
  -- Handle trivial case: x = 0
  by_cases hx_zero : edgeHammingWeight G x = 0
  · simp [hx_zero]
  -- x ≠ 0
  push_neg at hx_zero
  have hE_pos : (0 : ℝ) < edgeHammingWeight G x :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hx_zero)
  set S := incidentToSupport G x
  set E := supportEdges G x
  set A := highExpansionVertices G S s (↑dL - 1 : ℝ)
  -- Step 1: |∂(x)| ≥ |A| (from differentialWeight_ge_highExpansion)
  have h_diff_ge_A := differentialWeight_ge_highExpansion G Λ hreg parityCheck x dL hdL hdL_pos
  have h_step1 : (A.card : ℝ) ≤ differentialWeight G Λ parityCheck x := by
    have := h_diff_ge_A
    dsimp only at this
    exact Nat.cast_le.mpr this
  -- Step 2: |S| ≥ β' · |E| (from Lem_2: edgeToVertexExpansion)
  have hE_sub : E ⊆ G.edgeFinset := supportEdges_subset G x
  have hE_card : (E.card : ℝ) = edgeHammingWeight G x := by
    exact_mod_cast supportEdges_card_eq G x
  have hE_le : (E.card : ℝ) ≤ alpha * G.edgeFinset.card := by rw [hE_card]; exact hx_le
  have h_lem2 := edgeToVertexExpansion G s hs hreg hcard lam2 hlam2 hlam2_lt_s
    alpha halpha_pos halpha_le E hE_sub hE_le
  -- h_lem2 : (incidentVertices E).card ≥ betaParam s lam2 alpha * E.card
  have h_S_eq : S = AlonChungContrapositive.incidentVertices E :=
    incidentToSupport_eq_incidentVertices G x
  have h_step2 : beta' ↑s lam2 alpha * edgeHammingWeight G x ≤ (S.card : ℝ) := by
    rw [h_S_eq]; rw [hE_card] at h_lem2; unfold beta'; linarith
  -- Step 3: |A| ≥ β'' · |S| (from Lem_3: relativeVertexToEdgeExpansion)
  have h_S_le : (S.card : ℝ) ≤ alpha * ↑s * Fintype.card V :=
    incidentToSupport_card_le_alphaS G s hreg alpha halpha_pos x hx_le
  have hb0 : (0 : ℝ) < ↑dL - 1 := by
    have : (2 : ℝ) ≤ ↑dL := by exact_mod_cast hdL_ge_two
    linarith
  have hbs : (↑dL - 1 : ℝ) ≤ ↑s := by
    have : (↑dL : ℝ) ≤ ↑s := by exact_mod_cast hdL_le_s
    linarith
  have h_lem3 := relativeVertexToEdgeExpansion G s (alpha * ↑s) (↑dL - 1)
    (by positivity) halpha_s_lt_one hb0 hbs hconn hreg hcard S h_S_le
  -- h_lem3 : ((dL-1 - lam2') - αs*(s - lam2')) / (dL-1) * S.card ≤ A.card
  -- Rewrite using hlam2 to match our beta''
  have h_step3 : beta'' ↑s lam2 alpha ↑dL * S.card ≤ (A.card : ℝ) := by
    have h3 := h_lem3
    simp only at h3
    rw [← hlam2] at h3
    convert h3 using 2
  -- Step 4: Combine: β'β''|E| ≤ β''|S| ≤ |A| ≤ |∂(x)|
  have h_chain1 : beta' ↑s lam2 alpha * beta'' ↑s lam2 alpha ↑dL *
      edgeHammingWeight G x ≤ beta'' ↑s lam2 alpha ↑dL * S.card := by
    have := mul_le_mul_of_nonneg_left h_step2 (le_of_lt h_beta''_pos)
    nlinarith
  linarith

end ExpanderViolatedChecks
