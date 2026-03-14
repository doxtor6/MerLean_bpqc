import MerLeanBpqc.Definitions.Def_3_ClassicalCode
import MerLeanBpqc.Definitions.Def_14_GraphExpansion
import MerLeanBpqc.Definitions.Def_15_TannerCodeLocalSystem
import MerLeanBpqc.Theorems.Cor_1_AlonChungContrapositive
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Theorem 7: Sipser–Spielman Expander Code Distance

## Main Results
- `sipserSpielman_dimension_bound` — The dimension of the Tanner code satisfies
  `k ≥ (2k_L/s - 1)|X₁|`.
- `sipserSpielman_distance_bound` — The distance of the Tanner code satisfies
  `d ≥ (d_L - λ₂)d_L / ((s - λ₂)s) · |X₁|`.
-/

set_option maxRecDepth 1024
set_option maxHeartbeats 800000

open SimpleGraph Fintype BigOperators Finset Classical

namespace SipserSpielman

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Helper: LinearEquiv for Submodule.pi -/

/-- A linear equivalence between `Submodule.pi Set.univ (fun _ => p)` and `ι → ↥p`. -/
noncomputable def piSubmoduleEquiv {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (ι : Type*) (p : Submodule R M) :
    ↥(Submodule.pi (Set.univ : Set ι) (fun _ => p)) ≃ₗ[R] (ι → ↥p) where
  toFun x i := ⟨(x : ι → M) i, x.prop i (Set.mem_univ i)⟩
  invFun f := ⟨fun i => (f i : M), fun i _ => (f i).prop⟩
  left_inv x := by ext i; rfl
  right_inv f := by ext i; rfl
  map_add' x y := by ext i; rfl
  map_smul' r x := by ext i; rfl

/-- The finrank of `Submodule.pi Set.univ (fun _ => p)` equals `|ι| * finrank(p)`. -/
lemma finrank_pi_submodule {R : Type*} [CommSemiring R] [StrongRankCondition R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (ι : Type*) [Fintype ι] (p : Submodule R M)
    [Module.Free R ↥p] [Module.Finite R ↥p] :
    Module.finrank R ↥(Submodule.pi (Set.univ : Set ι) (fun _ => p)) =
      Fintype.card ι * Module.finrank R ↥p := by
  rw [LinearEquiv.finrank_eq (piSubmoduleEquiv ι p)]
  rw [Module.finrank_pi_fintype]
  simp

/-! ## Helper: range of differential -/

/-- The range of the differential is contained in the pi of ranges of parityCheck. -/
lemma range_differential_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (Λ : Labeling G (s := s))
    {m : ℕ} (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) :
    LinearMap.range (differential Λ parityCheck) ≤
      Submodule.pi Set.univ (fun (_ : V) => LinearMap.range parityCheck) := by
  intro f hf
  rw [Submodule.mem_pi]
  intro v _
  obtain ⟨c, hc⟩ := hf
  exact ⟨localView Λ v c, congr_fun hc v⟩

/-- Upper bound on finrank of the range of the differential. -/
lemma finrank_range_differential_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (Λ : Labeling G (s := s))
    {m : ℕ} (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) :
    Module.finrank 𝔽₂ ↥(LinearMap.range (differential Λ parityCheck)) ≤
      Fintype.card V * Module.finrank 𝔽₂ ↥(LinearMap.range parityCheck) := by
  calc Module.finrank 𝔽₂ ↥(LinearMap.range (differential Λ parityCheck))
      ≤ Module.finrank 𝔽₂ ↥(Submodule.pi Set.univ
          (fun (_ : V) => LinearMap.range parityCheck)) :=
        Submodule.finrank_mono (range_differential_le G Λ parityCheck)
    _ = Fintype.card V * Module.finrank 𝔽₂ ↥(LinearMap.range parityCheck) :=
        finrank_pi_submodule V (LinearMap.range parityCheck)

/-! ## Part 1: Dimension Bound -/

/-- The dimension of the Tanner code `C(X, L, Λ)` satisfies
`k ≥ (2k_L/s - 1) · |X₁|`. -/
theorem sipserSpielman_dimension_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s) (hreg : G.IsRegularOfDegree s)
    (hcard : 2 ≤ Fintype.card V)
    {m : ℕ} (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (Λ : Labeling G (s := s))
    (kL : ℕ) (hkL : kL = Module.finrank 𝔽₂ (LinearMap.ker parityCheck)) :
    (Module.finrank 𝔽₂ (tannerCode Λ parityCheck) : ℝ) ≥
      (2 * (kL : ℝ) / (s : ℝ) - 1) * (G.edgeFinset.card : ℝ) := by
  -- tannerCode = ker(differential)
  have h_tc : tannerCode Λ parityCheck = LinearMap.ker (differential Λ parityCheck) := rfl
  -- Rank-nullity: finrank(range) + finrank(ker) = finrank(domain)
  have h_rn := LinearMap.finrank_range_add_finrank_ker (differential Λ parityCheck)
  -- finrank(edgeSet → 𝔽₂) = |edgeFinset|
  have h_dom : Module.finrank 𝔽₂ (G.edgeSet → 𝔽₂) = G.edgeFinset.card := by
    rw [Module.finrank_pi 𝔽₂]; exact G.card_edgeSet
  -- Rank-nullity for parityCheck: finrank(range) + kL = s
  have h_pc_rn := LinearMap.finrank_range_add_finrank_ker parityCheck
  have h_pc_dom : Module.finrank 𝔽₂ (Fin s → 𝔽₂) = s := by
    rw [Module.finrank_pi 𝔽₂]; simp [Fintype.card_fin]
  -- kL ≤ s
  have hkL_le_s : kL ≤ s := by rw [hkL]; omega
  -- finrank(range parityCheck) = s - kL
  have h_rpc : Module.finrank 𝔽₂ ↥(LinearMap.range parityCheck) = s - kL := by
    omega
  -- Range of differential bounded
  have h_range := finrank_range_differential_le G Λ parityCheck
  rw [h_rpc] at h_range
  -- From rank-nullity: finrank(tannerCode) = |X₁| - finrank(range)
  have h_ker : Module.finrank 𝔽₂ (tannerCode Λ parityCheck) =
    G.edgeFinset.card - Module.finrank 𝔽₂ ↥(LinearMap.range (differential Λ parityCheck)) := by
    rw [h_tc]; omega
  -- finrank(tannerCode) ≥ |X₁| - |V| * (s - kL)
  have h_lb : Module.finrank 𝔽₂ (tannerCode Λ parityCheck) ≥
    G.edgeFinset.card - Fintype.card V * (s - kL) := by omega
  -- Handshaking: 2|X₁| = s|V|
  have h_hs := AlonChung.twice_card_edgeFinset_eq G s hreg
  -- Now do the real arithmetic
  have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr (by omega)
  -- Convert to ℝ and simplify
  rw [ge_iff_le, ← sub_nonneg]
  -- We need: finrank(TC) - (2kL/s - 1) * |X₁| ≥ 0
  have key : (Module.finrank 𝔽₂ (tannerCode Λ parityCheck) : ℝ) -
    (2 * ↑kL / ↑s - 1) * ↑(G.edgeFinset.card) ≥ 0 := by
    have h1 : (Module.finrank 𝔽₂ (tannerCode Λ parityCheck) : ℝ) ≥
      ↑(G.edgeFinset.card) - ↑(Fintype.card V) * (↑s - ↑kL) := by
      by_cases h_le : Fintype.card V * (s - kL) ≤ G.edgeFinset.card
      · have h_nat := h_lb
        have h_cast : (Module.finrank 𝔽₂ (tannerCode Λ parityCheck) : ℝ) ≥
          ↑(G.edgeFinset.card - Fintype.card V * (s - kL)) := by exact_mod_cast h_nat
        rw [Nat.cast_sub h_le] at h_cast
        rw [Nat.cast_mul, Nat.cast_sub hkL_le_s] at h_cast; linarith
      · push_neg at h_le
        have h_nn : (0 : ℝ) ≤ ↑(Module.finrank 𝔽₂ (tannerCode Λ parityCheck)) :=
          Nat.cast_nonneg _
        have h_le' : (↑(#G.edgeFinset) : ℝ) < ↑(Fintype.card V) * ↑(s - kL) := by
          exact_mod_cast h_le
        rw [Nat.cast_sub hkL_le_s] at h_le'
        linarith
    -- (2kL/s - 1) * |X₁| = |X₁| - (2(s-kL)/s) * |X₁| = |X₁| - (s-kL) * |V|
    -- because 2|X₁|/s = |V|
    have h2 : (2 * ↑kL / ↑s - 1) * ↑(G.edgeFinset.card) =
      ↑(G.edgeFinset.card) - (↑s - ↑kL) * (↑(Fintype.card V) : ℝ) := by
      have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs_pos
      have hV : (↑(Fintype.card V) : ℝ) * ↑s = 2 * ↑(G.edgeFinset.card) := by linarith
      have goal_eq : ((2 * ↑kL / ↑s - 1) * ↑(G.edgeFinset.card) -
        (↑(G.edgeFinset.card) - (↑s - ↑kL) * (↑(Fintype.card V) : ℝ))) * ↑s = 0 := by
        have h1 : 2 * (↑kL : ℝ) / ↑s * ↑s = 2 * ↑kL := by
          rw [div_mul_cancel₀ (2 * (↑kL : ℝ)) hs_ne]
        nlinarith [h1]
      nlinarith [mul_eq_zero.mp goal_eq, hs_ne]
    linarith
  linarith

/-! ## Part 2: Distance Bound -/

/-- Helper: the support of a vector as a Finset of edges. -/
noncomputable def support (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.edgeSet → 𝔽₂) : Finset G.edgeSet :=
  Finset.univ.filter (fun e => c e ≠ 0)

/-- The Hamming weight of a vector over `G.edgeSet → 𝔽₂`. -/
noncomputable def edgeHammingWeight (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.edgeSet → 𝔽₂) : ℕ :=
  (support G c).card

/-- The set of vertices incident to the support of an edge function `c`. -/
noncomputable def incidentToSupport (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.edgeSet → 𝔽₂) : Finset V :=
  Finset.univ.filter (fun v => ∃ e : G.edgeSet, c e ≠ 0 ∧ v ∈ (e : Sym2 V))

/-- The degree of a vertex in the support of `c`: the number of edges in `supp(c)`
incident to `v`. -/
noncomputable def supportDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (Λ : Labeling G (s := s)) (c : G.edgeSet → 𝔽₂) (v : V) : ℕ :=
  (Finset.univ.filter (fun i : Fin s =>
    let w := ((Λ v).symm i).val
    c ⟨s(v, w), G.mem_edgeSet.mpr ((Λ v).symm i).prop⟩ ≠ 0)).card

/-- For a codeword of the Tanner code, the local view at each vertex is in ker(parityCheck).
If the local view is nonzero, its Hamming weight is at least `d_L`. -/
lemma localView_weight_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (Λ : Labeling G (s := s))
    {m : ℕ} (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (c : G.edgeSet → 𝔽₂) (hc : c ∈ tannerCode Λ parityCheck)
    (dL : ℕ) (hdL : dL = ClassicalCode.distance (ClassicalCode.ofParityCheck parityCheck))
    (v : V) (hv : localView Λ v c ≠ 0) :
    dL ≤ hammingWeight (localView Λ v c) := by
  rw [hdL]
  have hmem : localView Λ v c ∈ (ClassicalCode.ofParityCheck parityCheck).code := by
    rw [ClassicalCode.code_eq_ker]
    exact (mem_tannerCode_iff Λ parityCheck c).mp hc v
  unfold ClassicalCode.distance
  apply Nat.sInf_le
  exact ⟨localView Λ v c, hmem, hv, rfl⟩

/-! ### Distance bound helper lemmas -/

/-- The support Finset of a nonzero function has positive cardinality. -/
lemma support_nonempty_of_ne_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.edgeSet → 𝔽₂) (hc : c ≠ 0) :
    (support G c).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  apply hc
  ext e
  have : e ∉ support G c := by rw [h]; exact Finset.notMem_empty _
  simp [support, Finset.mem_filter] at this
  simp [this]

/-- The edgeHammingWeight equals the number of nonzero components. -/
lemma edgeHammingWeight_pos_of_ne_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.edgeSet → 𝔽₂) (hc : c ≠ 0) :
    0 < edgeHammingWeight G c := by
  exact Finset.Nonempty.card_pos (support_nonempty_of_ne_zero G c hc)

/-- The support as a Finset of Sym2 V (edges of G). -/
noncomputable def supportEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.edgeSet → 𝔽₂) : Finset (Sym2 V) :=
  (support G c).image (fun e => e.val)

/-- supportEdges ⊆ G.edgeFinset -/
lemma supportEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.edgeSet → 𝔽₂) :
    supportEdges G c ⊆ G.edgeFinset := by
  intro e he
  simp [supportEdges, Finset.mem_image] at he
  obtain ⟨he_mem, _⟩ := he
  exact G.mem_edgeFinset.mpr he_mem

/-- The cardinality of supportEdges equals edgeHammingWeight (edges in G.edgeSet are distinct). -/
lemma card_supportEdges_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.edgeSet → 𝔽₂) :
    (supportEdges G c).card = edgeHammingWeight G c := by
  simp [supportEdges, edgeHammingWeight]
  rw [Finset.card_image_of_injective]
  exact Subtype.val_injective

/-- If v is incident to the support, the local view at v is nonzero. -/
lemma localView_ne_zero_of_incident (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (Λ : Labeling G (s := s)) (c : G.edgeSet → 𝔽₂)
    (v : V) (hv : v ∈ incidentToSupport G c) :
    localView Λ v c ≠ 0 := by
  simp [incidentToSupport, Finset.mem_filter] at hv
  obtain ⟨e, hce, hve⟩ := hv
  intro h
  -- h says localView Λ v c = 0, i.e., all components are 0
  -- But e is an edge incident to v with c(e) ≠ 0
  -- The edge e = s(v, w) for some neighbor w, and Λ v maps w to some i
  -- localView v c i = c(e) ≠ 0, contradicting h
  have h0 : ∀ i, localView Λ v c i = 0 := fun i => by
    rw [h]; rfl
  -- e.val is a Sym2 V with v ∈ e.val
  -- Since G is simple, e = s(v, w) for some w ≠ v with G.Adj v w
  -- e : Sym2 V, hce : ∃ (x : e ∈ G.edgeSet), c ⟨e, x⟩ ≠ 0, hve : v ∈ e
  obtain ⟨hedge_mem, hce'⟩ := hce
  -- v ∈ e and e ∈ G.edgeSet. Use Sym2.other_spec: s(v, other) = e
  set w_val := Sym2.Mem.other hve
  have hother : s(v, w_val) = e := Sym2.other_spec hve
  have hadj : G.Adj v w_val := by
    rw [← hother] at hedge_mem; exact G.mem_edgeSet.mp hedge_mem
  let w : G.neighborSet v := ⟨w_val, hadj⟩
  let i := Λ v w
  have hi := h0 i
  rw [localView_apply] at hi
  have hsymm : (Λ v).symm i = w := (Λ v).symm_apply_apply w
  simp only [hsymm] at hi
  exact hce' (by
    have : (⟨s(v, w_val), G.mem_edgeSet.mpr hadj⟩ : G.edgeSet) = ⟨e, hedge_mem⟩ :=
      Subtype.ext hother
    rw [← this]; exact hi)

/-- For a codeword, each incident vertex has at least dL edges in the support. -/
lemma incident_vertex_degree_ge_dL (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (Λ : Labeling G (s := s))
    {m : ℕ} (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (c : G.edgeSet → 𝔽₂) (hc : c ∈ tannerCode Λ parityCheck)
    (dL : ℕ) (hdL : dL = ClassicalCode.distance (ClassicalCode.ofParityCheck parityCheck))
    (v : V) (hv : v ∈ incidentToSupport G c) :
    dL ≤ supportDegree G Λ c v := by
  have hlv := localView_ne_zero_of_incident G Λ c v hv
  have hwt := localView_weight_bound G s Λ parityCheck c hc dL hdL v hlv
  -- supportDegree counts nonzero entries of localView, which equals hammingWeight
  -- hammingWeight counts {i | localView Λ v c i ≠ 0}
  -- supportDegree counts {i | c(s(v, (Λ v)⁻¹(i))) ≠ 0} = {i | localView Λ v c i ≠ 0}
  convert hwt using 1

/-- For each edge, at most 2 vertices are incident to it. -/
lemma card_filter_mem_sym2_le_two (e : Sym2 V) :
    (Finset.univ.filter (fun v => v ∈ e)).card ≤ 2 := by
  induction e using Sym2.ind with
  | h a b =>
  calc (Finset.univ.filter (fun v => v ∈ s(a, b))).card
      ≤ ({a, b} : Finset V).card := Finset.card_le_card (by
        intro v; simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Sym2.mem_iff])
    _ ≤ 2 := by
        have : ({a, b} : Finset V).card ≤ ({b} : Finset V).card + 1 :=
          Finset.card_insert_le a {b}
        simp [Finset.card_singleton] at this; omega

/-- Key double-counting: |S| * dL ≤ 2 * |E| for a codeword. -/
lemma incidentCount_le_twice_weight (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : ℕ} (Λ : Labeling G (s := s))
    {m : ℕ} (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (c : G.edgeSet → 𝔽₂) (hc : c ∈ tannerCode Λ parityCheck)
    (dL : ℕ) (hdL : dL = ClassicalCode.distance (ClassicalCode.ofParityCheck parityCheck)) :
    (incidentToSupport G c).card * dL ≤ 2 * edgeHammingWeight G c := by
  -- Use labeling-based sigma: {(v, i) : S × Fin s | localView Λ v c i ≠ 0}
  let T := (incidentToSupport G c).sigma
    (fun v => Finset.univ.filter (fun i : Fin s => localView Λ v c i ≠ 0))
  -- Lower bound: |T| ≥ |S| * dL
  -- Each v ∈ S has hammingWeight(localView v c) ≥ dL
  have h_lower : (incidentToSupport G c).card * dL ≤ T.card := by
    rw [Finset.card_sigma]
    apply Finset.card_nsmul_le_sum
    intro v hv
    have hlv := localView_ne_zero_of_incident G Λ c v hv
    have hwt := localView_weight_bound G s Λ parityCheck c hc dL hdL v hlv
    -- hammingWeight = card of filter of nonzero entries
    simp only [hammingWeight, hammingNorm, hammingDist] at hwt
    convert hwt using 1
  -- Upper bound: |T| ≤ 2 * |E|
  -- Map (v, i) ↦ ⟨s(v, (Λ v)⁻¹(i)), ...⟩ ∈ edgeSet; image ⊆ support; each fiber ≤ 2
  -- Define the edge map
  let edgeOf : (v : V) → Fin s → G.edgeSet := fun v i =>
    ⟨s(v, ((Λ v).symm i).val), G.mem_edgeSet.mpr ((Λ v).symm i).prop⟩
  -- Map T → G.edgeSet
  let φ : (Σ (_ : V), Fin s) → G.edgeSet := fun ⟨v, i⟩ => edgeOf v i
  -- Elements of T map into support
  have hφ_support : ∀ p ∈ T, φ p ∈ support G c := by
    intro ⟨v, i⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and, T] at hp
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, φ, edgeOf]
    rw [localView_apply] at hp
    exact hp.2
  -- Each support edge has ≤ 2 preimages
  have h_fiber : ∀ e ∈ T.image φ, (T.filter (fun p => φ p = e)).card ≤ 2 := by
    intro e _
    calc (T.filter (fun p => φ p = e)).card
        ≤ (Finset.univ.filter (fun v : V => v ∈ (e.val : Sym2 V))).card := by
          apply Finset.card_le_card_of_injOn Sigma.fst
          · intro ⟨v, i⟩ hvi
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hvi
            have heq : φ ⟨v, i⟩ = e := hvi.2
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
            show v ∈ (e : Sym2 V)
            have : (e : Sym2 V) = s(v, ((Λ v).symm i).val) := by
              rw [← heq]
            rw [this]
            exact Sym2.mem_mk_left v _
          · intro ⟨v₁, i₁⟩ h₁ ⟨v₂, i₂⟩ h₂ (heq : v₁ = v₂)
            subst heq
            congr 1
            simp only [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
            have h₁eq := h₁.2; have h₂eq := h₂.2
            have : φ ⟨v₁, i₁⟩ = φ ⟨v₁, i₂⟩ := by rw [h₁eq, h₂eq]
            simp only [φ, edgeOf, Subtype.mk.injEq] at this
            -- this : s(v₁, ↑((Λ v₁).symm i₁)) = s(v₁, ↑((Λ v₁).symm i₂))
            have hrel := Sym2.eq_iff.mp this
            -- hrel : (v₁ = v₁ ∧ w₁ = w₂) ∨ (v₁ = w₂ ∧ w₁ = v₁)
            have hw_eq : ((Λ v₁).symm i₁).val = ((Λ v₁).symm i₂).val := by
              rcases hrel with ⟨_, h⟩ | ⟨h1, _⟩
              · exact h
              · -- swap case: v₁ = ((Λ v₁).symm i₂).val, contradicts loopless
                exfalso
                have hmem := ((Λ v₁).symm i₂).prop
                rw [SimpleGraph.mem_neighborSet, ← h1] at hmem
                exact G.loopless _ hmem
            exact (Λ v₁).symm.injective (Subtype.val_injective hw_eq)
      _ ≤ 2 := card_filter_mem_sym2_le_two e.val
  have h := Finset.card_le_mul_card_image (f := φ) T 2 h_fiber
  have h_image_le : (T.image φ).card ≤ (support G c).card := by
    apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_image] at he
    obtain ⟨p, hp, rfl⟩ := he
    exact hφ_support p hp
  have h_upper : T.card ≤ 2 * edgeHammingWeight G c := by
    calc T.card ≤ 2 * (T.image φ).card := h
      _ ≤ 2 * (support G c).card := Nat.mul_le_mul_left _ h_image_le
      _ = 2 * edgeHammingWeight G c := rfl
  omega

/-- Hamming weight of any vector in Fin s → 𝔽₂ is at most s. -/
lemma hammingWeight_le_card {n : ℕ} (x : Fin n → 𝔽₂) : hammingWeight x ≤ n := by
  simp only [hammingWeight, hammingNorm, hammingDist]
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The distance of a code of length s is at most s (when there's a nonzero codeword). -/
lemma distance_le_length' {s : ℕ} (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (hdL_pos : 0 < ClassicalCode.distance (ClassicalCode.ofParityCheck parityCheck)) :
    ClassicalCode.distance (ClassicalCode.ofParityCheck parityCheck) ≤ s := by
  unfold ClassicalCode.distance at hdL_pos ⊢
  -- Since sInf > 0, the set is nonempty
  have hne : (({w | ∃ x, x ∈ (ClassicalCode.ofParityCheck parityCheck).code ∧
    x ≠ 0 ∧ hammingWeight x = w} : Set ℕ)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp [h] at hdL_pos
  obtain ⟨w, ⟨x, hx, hne, rfl⟩⟩ := hne
  apply (Nat.sInf_le (⟨x, hx, hne, rfl⟩ : hammingWeight x ∈ {w | ∃ x ∈ (ClassicalCode.ofParityCheck parityCheck).code, x ≠ 0 ∧ hammingWeight x = w})).trans
  exact hammingWeight_le_card x

/-- The distance of the Tanner code `C(X, L, Λ)` satisfies
`d ≥ (d_L - λ₂) · d_L / ((s - λ₂) · s) · |X₁|`. -/
theorem sipserSpielman_distance_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (s : ℕ) (hs : 1 ≤ s) (hreg : G.IsRegularOfDegree s)
    (hcard : 2 ≤ Fintype.card V)
    {m : ℕ} (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (Λ : Labeling G (s := s))
    (dL : ℕ) (hdL : dL = ClassicalCode.distance (ClassicalCode.ofParityCheck parityCheck))
    (lam₂ : ℝ) (hlam₂ : lam₂ = GraphExpansion.secondLargestEigenvalue G hcard)
    (hlam₂_nn : 0 ≤ lam₂)
    (hdL_gt_lam₂ : (dL : ℝ) > lam₂) :
    ∀ c : G.edgeSet → 𝔽₂, c ∈ tannerCode Λ parityCheck → c ≠ 0 →
      (edgeHammingWeight G c : ℝ) ≥
        ((dL : ℝ) - lam₂) * dL / (((s : ℝ) - lam₂) * s) * G.edgeFinset.card := by
  intro c hc hc_ne
  -- Setup notation
  set S := incidentToSupport G c
  set E := edgeHammingWeight G c
  set n := Fintype.card V
  -- Positivity
  have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hdL_pos : (0 : ℝ) < (dL : ℝ) := by
    rcases Nat.eq_zero_or_pos dL with h | h
    · subst h; simp at hdL_gt_lam₂; linarith
    · exact Nat.cast_pos.mpr h
  have hdL_nat_pos : 0 < dL := by exact_mod_cast hdL_pos
  have hs_lam : (s : ℝ) - lam₂ > 0 := by
    have hdL_le : (ClassicalCode.ofParityCheck parityCheck).distance ≤ s :=
      distance_le_length' parityCheck (hdL ▸ hdL_nat_pos)
    have : dL ≤ s := hdL ▸ hdL_le
    have : (dL : ℝ) ≤ (s : ℝ) := by exact_mod_cast this
    linarith
  -- Key inequality: |S| * dL ≤ 2 * E
  have h_count : S.card * dL ≤ 2 * E :=
    incidentCount_le_twice_weight G Λ parityCheck c hc dL hdL
  -- S is nonempty
  have hS_nonempty : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hc_ne
    ext ⟨e, he⟩
    simp only [Pi.zero_apply]
    by_contra hce
    -- e is a support edge, so its endpoints are in S
    induction e using Sym2.ind with
    | h a b =>
    have : a ∈ S := by
      simp only [incidentToSupport, Finset.mem_filter, Finset.mem_univ, true_and, S]
      exact ⟨⟨s(a, b), he⟩, hce, Sym2.mem_mk_left a b⟩
    rw [hempty] at this; simp at this
  -- Handshaking: 2|X₁| = s * n
  have h_hs := AlonChung.twice_card_edgeFinset_eq G s hreg
  -- dL ≤ s
  have hdL_le_s : (dL : ℝ) ≤ s := by
    have h1 : (ClassicalCode.ofParityCheck parityCheck).distance ≤ s :=
      distance_le_length' parityCheck (hdL ▸ hdL_nat_pos)
    have h2 : dL ≤ s := hdL ▸ h1
    exact_mod_cast h2
  -- The bound factor (dL - λ₂) / (s - λ₂) ∈ (0, 1]
  have hfrac_pos : 0 < ((dL : ℝ) - lam₂) / ((s : ℝ) - lam₂) := by
    exact div_pos (by linarith) hs_lam
  have hfrac_le_one : ((dL : ℝ) - lam₂) / ((s : ℝ) - lam₂) ≤ 1 := by
    rw [div_le_one hs_lam]; linarith
  -- Case split: S.card ≥ n or S.card < n
  by_cases h_all : n ≤ S.card
  · -- Case 1: |S| ≥ n (all vertices incident)
    -- n * dL ≤ 2E, so E ≥ n * dL / 2 = (dL/s) * |X₁|
    have h1 : (n : ℝ) * dL ≤ 2 * (E : ℝ) := by
      have h_all' : (n : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast h_all
      have h_count' : (S.card : ℝ) * (dL : ℝ) ≤ 2 * (E : ℝ) := by exact_mod_cast h_count
      nlinarith
    -- (dL/s) * |X₁| ≥ bound * |X₁| since (dL-λ₂)/(s-λ₂) ≤ 1
    have h2 : ((dL : ℝ) - lam₂) * dL / (((s : ℝ) - lam₂) * s) ≤ dL / s := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ((s : ℝ) - lam₂) * s) hs_pos]
      have h_sub : (dL : ℝ) - lam₂ ≤ (s : ℝ) - lam₂ := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h_sub (le_of_lt hs_pos),
                 mul_le_mul_of_nonneg_left (le_of_lt hs_pos) (le_of_lt hdL_pos)]
    -- linarith can close this directly from h1, h2, h_hs, and other facts
    have h_edgeFinset : (G.edgeFinset.card : ℝ) = (s : ℝ) * n / 2 := by linarith
    have h3 : (E : ℝ) ≥ n * dL / 2 := by linarith
    have h4 : n * (dL : ℝ) / 2 = (dL / s) * ((s : ℝ) * n / 2) := by
      have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs_pos
      field_simp
    have h5 : (dL : ℝ) / s * G.edgeFinset.card = n * dL / 2 := by
      rw [h_edgeFinset]; linarith [h4]
    have h6 : (E : ℝ) ≥ (dL : ℝ) / s * G.edgeFinset.card := by linarith
    calc (E : ℝ) ≥ (dL : ℝ) / s * G.edgeFinset.card := h6
      _ ≥ ((dL : ℝ) - lam₂) * dL / (((s : ℝ) - lam₂) * s) * G.edgeFinset.card := by
          apply mul_le_mul_of_nonneg_right h2 (by positivity)
  · -- Case 2: |S| < n
    push_neg at h_all
    have hS_lt_n : S.card < n := h_all
    have hS_pos : 0 < S.card := hS_nonempty.card_pos
    -- Let γ = |S| / n
    set γ := (S.card : ℝ) / n
    have hγ_pos : 0 < γ := div_pos (Nat.cast_pos.mpr hS_pos) hn_pos
    have hγ_lt_1 : γ < 1 := by
      rw [div_lt_one hn_pos]; exact_mod_cast hS_lt_n
    -- AC direct: |supportEdges| ≤ α(γ) * |X₁|
    have hS_le : (S.card : ℝ) ≤ γ * n := by
      simp [γ]; field_simp; norm_num
    -- Need: incidentVertices(supportEdges) ⊆ S in cardinality
    -- Actually incidentVertices(supportEdges) = S
    have hAC := AlonChungContrapositive.alonChungContrapositive_direct
      G s hs hreg hcard (supportEdges G c) (supportEdges_subset G c)
      γ hγ_pos hγ_lt_1 lam₂ hlam₂ hlam₂_nn
      (by -- incidentVertices(supportEdges) ≤ γ * n
        calc ((AlonChungContrapositive.incidentVertices (supportEdges G c)).card : ℝ)
            ≤ S.card := by
              exact_mod_cast Finset.card_le_card (fun v hv => by
                rw [AlonChungContrapositive.mem_incidentVertices] at hv
                simp only [incidentToSupport, Finset.mem_filter, Finset.mem_univ, true_and, S]
                obtain ⟨e, he, hve⟩ := hv
                simp only [supportEdges, Finset.mem_image] at he
                obtain ⟨⟨e', he'prop⟩, he'mem, rfl⟩ := he
                simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at he'mem
                exact ⟨⟨e', he'prop⟩, he'mem, hve⟩)
          _ ≤ γ * n := hS_le)
    -- hAC: |supportEdges| ≤ (γ² + (λ₂/s)γ(1-γ)) * |X₁|
    rw [card_supportEdges_eq] at hAC
    -- Now: (E : ℝ) ≤ (γ² + (λ₂/s)γ(1-γ)) * |X₁|
    -- Combined with |S| * dL ≤ 2E (in ℝ): γ * n * dL ≤ 2E ≤ 2(γ² + (λ₂/s)γ(1-γ))|X₁|
    -- Since |X₁| = sn/2: γ * n * dL ≤ (γ² + (λ₂/s)γ(1-γ)) * s * n
    -- Dividing by n (> 0) and γ (> 0): dL ≤ (γ + (λ₂/s)(1-γ)) * s = sγ + λ₂(1-γ)
    -- So γ(s-λ₂) ≥ dL - λ₂, hence γ ≥ (dL-λ₂)/(s-λ₂)
    have h_count_real : γ * (n : ℝ) * dL ≤ 2 * (E : ℝ) := by
      have := h_count
      have : (S.card : ℝ) * dL ≤ 2 * (E : ℝ) := by push_cast at this ⊢; exact_mod_cast this
      calc γ * n * dL = (S.card : ℝ) * dL := by
            simp only [γ]; rw [div_mul_cancel₀]
            exact ne_of_gt hn_pos
        _ ≤ 2 * (E : ℝ) := this
    have h_gamma_bound : γ ≥ ((dL : ℝ) - lam₂) / ((s : ℝ) - lam₂) := by
      rw [ge_iff_le, div_le_iff₀ hs_lam]
      -- From AC + count: γ * dL ≤ (γ² + (λ₂/s)γ(1-γ)) * s
      -- i.e., dL ≤ sγ + λ₂(1-γ) = γ(s-λ₂) + λ₂
      -- so dL - λ₂ ≤ γ(s-λ₂)
      have hE_le : (E : ℝ) ≤ (γ ^ 2 + lam₂ / ↑s * γ * (1 - γ)) * G.edgeFinset.card := hAC
      -- γ * n * dL ≤ 2 * E ≤ 2 * (γ² + (λ₂/s)γ(1-γ)) * |X₁|
      -- = (γ² + (λ₂/s)γ(1-γ)) * s * n
      have key : γ * dL ≤ (γ ^ 2 + lam₂ / ↑s * γ * (1 - γ)) * s := by
        have h1 : γ * ↑n * ↑dL ≤ 2 * ((γ ^ 2 + lam₂ / ↑s * γ * (1 - γ)) * ↑(G.edgeFinset.card)) :=
          by linarith
        have h_ef : (G.edgeFinset.card : ℝ) = ↑s * ↑n / 2 := by linarith
        have h2 : 2 * ((γ ^ 2 + lam₂ / ↑s * γ * (1 - γ)) * ↑(G.edgeFinset.card)) =
          (γ ^ 2 + lam₂ / ↑s * γ * (1 - γ)) * ↑s * ↑n := by rw [h_ef]; ring
        have h3 : γ * ↑n * ↑dL ≤ (γ ^ 2 + lam₂ / ↑s * γ * (1 - γ)) * ↑s * ↑n := by linarith
        have h4 : γ * ↑dL * ↑n ≤ (γ ^ 2 + lam₂ / ↑s * γ * (1 - γ)) * ↑s * ↑n := by linarith
        exact le_of_mul_le_mul_right (by linarith) hn_pos
      -- key: γ * dL ≤ (γ² + (λ₂/s)γ(1-γ)) * s = sγ² + λ₂γ(1-γ) = γ(sγ + λ₂(1-γ))
      -- Since γ > 0: dL ≤ sγ + λ₂(1-γ) = γ(s-λ₂) + λ₂
      have key2 : ↑dL ≤ γ * (↑s - lam₂) + lam₂ := by
        have : γ * ↑dL ≤ γ * (γ * (↑s - lam₂) + lam₂) := by
          calc γ * ↑dL ≤ (γ ^ 2 + lam₂ / ↑s * γ * (1 - γ)) * ↑s := key
            _ = γ * (γ * ↑s + lam₂ * (1 - γ)) := by ring_nf; field_simp
            _ = γ * (γ * (↑s - lam₂) + lam₂) := by ring
        exact le_of_mul_le_mul_left this hγ_pos
      linarith
    -- Final bound: E ≥ γ * n * dL / 2 ≥ γ₀ * n * dL / 2 = bound * |X₁|
    -- linarith closes this from h_count_real, h_gamma_bound, h_hs, etc.
    have h_edgeFinset' : (G.edgeFinset.card : ℝ) = (s : ℝ) * n / 2 := by linarith
    have h_step1 : (E : ℝ) ≥ γ * n * dL / 2 := by linarith
    have h_step2 : γ * n * (dL : ℝ) / 2 ≥ ((dL : ℝ) - lam₂) / ((s : ℝ) - lam₂) * n * dL / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) < 2).le
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right h_gamma_bound (by positivity)
      · positivity
    have h_step3 : ((dL : ℝ) - lam₂) / ((s : ℝ) - lam₂) * n * dL / 2 =
        ((dL : ℝ) - lam₂) * dL / (((s : ℝ) - lam₂) * s) * (s * n / 2) := by
      field_simp
    have h_step4 : ((dL : ℝ) - lam₂) * dL / (((s : ℝ) - lam₂) * s) * (s * n / 2) =
        ((dL : ℝ) - lam₂) * dL / (((s : ℝ) - lam₂) * s) * G.edgeFinset.card := by
      congr 1; linarith
    linarith

end SipserSpielman
