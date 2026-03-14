import MerLeanBpqc.Definitions.Def_3_ClassicalCode
import MerLeanBpqc.Definitions.Def_14_GraphExpansion
import MerLeanBpqc.Definitions.Def_15_TannerCodeLocalSystem
import MerLeanBpqc.Definitions.Def_16_DualCode
import MerLeanBpqc.Definitions.Def_18_CheegerConstant
import MerLeanBpqc.Lemmas.Lem_3_RelativeVertexToEdgeExpansion
import MerLeanBpqc.Remarks.Rem_3_ExpandingMatrixDefinition

/-!
# Theorem 9: Expander Bit Degree

## Main Results
- `expanderBitDegree`: For a Tanner code on an expander graph with local code `L`
  and dual distance `d_{L⊥} ≥ 2`, the coboundary δ satisfies `|δ(y)| ≥ β|y|` for
  vectors `y` of bounded weight, where
  `β = ((d_{L⊥} - 1 - λ₂) - α(s-k_L)(s - λ₂)) / ((s-k_L)(d_{L⊥} - 1))`.
-/

set_option maxRecDepth 1024
set_option maxHeartbeats 800000

open SimpleGraph Fintype BigOperators Finset Classical
open RelativeVertexToEdgeExpansion GraphExpansion CheegerConstant

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ExpanderBitDegree

/-! ## Hamming weight for product vectors -/

/-- The total Hamming weight of `y : V → Fin m → 𝔽₂`. -/
noncomputable def totalWeight (y : V → Fin m → 𝔽₂) : ℕ :=
  ∑ v : V, hammingWeight (y v)

/-- The vertex support of `y`. -/
noncomputable def vertexSupport (y : V → Fin m → 𝔽₂) : Finset V :=
  Finset.univ.filter fun v => y v ≠ 0

lemma vertexSupport_nonempty {m : ℕ} {y : V → Fin m → 𝔽₂} (hy : y ≠ 0) :
    (vertexSupport y).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]; intro h
  apply hy; ext v i
  have hv : ¬(y v ≠ 0) := by
    intro hne
    have hmem : v ∈ vertexSupport y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [h] at hmem; exact (Finset.notMem_empty v) hmem
  push_neg at hv; exact congr_fun hv i

/-! ## Weight bounds -/

lemma card_vertexSupport_le_totalWeight {m : ℕ} (y : V → Fin m → 𝔽₂) :
    (vertexSupport y).card ≤ totalWeight y := by
  unfold totalWeight
  calc (vertexSupport y).card
      = ∑ v ∈ vertexSupport y, 1 := by simp
    _ ≤ ∑ v ∈ vertexSupport y, hammingWeight (y v) := by
        apply Finset.sum_le_sum
        intro v hv
        simp only [vertexSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        exact Nat.one_le_iff_ne_zero.mpr (hammingNorm_ne_zero_iff.mpr hv)
    _ ≤ ∑ v : V, hammingWeight (y v) :=
        Finset.sum_le_sum_of_subset (fun v _ => Finset.mem_univ v)

lemma totalWeight_le_mul_card {m : ℕ} (y : V → Fin m → 𝔽₂) :
    totalWeight y ≤ m * (vertexSupport y).card := by
  unfold totalWeight
  have hsplit : (∑ v : V, hammingWeight (y v)) =
      ∑ v ∈ vertexSupport y, hammingWeight (y v) +
      ∑ v ∈ Finset.univ \ vertexSupport y, hammingWeight (y v) := by
    rw [← Finset.sum_sdiff (show vertexSupport y ⊆ Finset.univ from Finset.filter_subset _ _)]
    exact add_comm _ _
  rw [hsplit]
  have hzero : ∑ v ∈ Finset.univ \ vertexSupport y, hammingWeight (y v) = 0 := by
    apply Finset.sum_eq_zero; intro v hv
    simp only [vertexSupport, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_filter, not_not] at hv
    simp [hv]
  rw [hzero, add_zero]
  calc ∑ v ∈ vertexSupport y, hammingWeight (y v)
      ≤ ∑ _v ∈ vertexSupport y, m := by
        apply Finset.sum_le_sum; intro v _
        exact hammingNorm_le_card_fintype.trans_eq (Fintype.card_fin m)
    _ = m * (vertexSupport y).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

lemma totalWeight_div_le_card {m : ℕ} (hm : 0 < m) (y : V → Fin m → 𝔽₂) :
    (totalWeight y : ℝ) / m ≤ (vertexSupport y).card := by
  rw [div_le_iff₀ (Nat.cast_pos.mpr hm)]
  have := totalWeight_le_mul_card y
  exact_mod_cast (show totalWeight y ≤ (vertexSupport y).card * m from by linarith)

/-! ## Coboundary map -/

/-- The coboundary map `δ`, the transpose of the Tanner differential. -/
noncomputable def coboundary (G : SimpleGraph V) [DecidableRel G.Adj]
    {s m : ℕ} (Λ : Labeling G (s := s))
    (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (y : V → Fin m → 𝔽₂) : (G.edgeSet → 𝔽₂) :=
  fun e => ∑ v : V, dotProduct (y v) (differential Λ parityCheck (Pi.single e 1) v)

noncomputable def coboundaryWeight (G : SimpleGraph V) [DecidableRel G.Adj]
    {s m : ℕ} (Λ : Labeling G (s := s))
    (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (y : V → Fin m → 𝔽₂) : ℕ :=
  hammingNorm (coboundary G Λ parityCheck y)

/-! ## Transpose of parity check -/

/-- The transpose of `parityCheck` via the dot product:
`(parityCheckTranspose H y)(j) = dotProduct y (H (Pi.single j 1))`. -/
noncomputable def parityCheckTranspose {s m : ℕ}
    (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) :
    (Fin m → 𝔽₂) →ₗ[𝔽₂] (Fin s → 𝔽₂) where
  toFun y j := dotProduct y (parityCheck (Pi.single j 1))
  map_add' x y := by
    ext j; simp [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    ext j; simp [dotProduct, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- If `parityCheck` is surjective, its transpose is injective. -/
lemma parityCheckTranspose_injective {s m : ℕ}
    (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (hPC_surj : Function.Surjective parityCheck) :
    Function.Injective (parityCheckTranspose parityCheck) := by
  rw [← LinearMap.ker_eq_bot]
  ext y
  simp only [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hy
    -- parityCheckTranspose y = 0 means ∀ j, dot(y, H(e_j)) = 0
    -- Since H is surjective, for any z ∈ Fin m → 𝔽₂, z = H(x) for some x
    -- dot(y, z) = dot(y, H(x)) = ∑_j x_j * dot(y, H(e_j)) = 0
    -- So dot(y, z) = 0 for all z, hence y = 0
    ext i
    have h : dotProduct y (Pi.single i 1) = 0 := by
      -- parityCheckTranspose maps Fin m → Fin s, not Fin m → Fin m
      -- We need to show y = 0 using surjectivity
      -- dot(y, H(e_j)) = 0 for all j : Fin s
      -- Pick z = e_i : Fin m → 𝔽₂. Since H surjective, z = H(x) for some x
      -- dot(y, z) = dot(y, H(x)) = dot(y, ∑_j x_j • H(e_j))
      --           = ∑_j x_j * dot(y, H(e_j)) = 0
      obtain ⟨x, hx⟩ := hPC_surj (Pi.single i (1 : 𝔽₂))
      have hyz : dotProduct y (Pi.single i 1) = dotProduct y (parityCheck x) := by
        rw [hx]
      rw [hyz]
      -- dot(y, H(x)) = ∑_k y_k * H(x)_k = ∑_k y_k * (∑_j x_j * H(e_j)_k)
      -- We can expand x = ∑_j x_j • e_j and use linearity
      have : parityCheck x = ∑ j, x j • parityCheck (Pi.single j 1) := by
        conv_lhs => rw [show x = ∑ j, x j • Pi.single j 1 from by
          ext k; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']]
        simp [map_sum, map_smul]
      rw [this, dotProduct_sum]
      apply Finset.sum_eq_zero
      intro j _
      simp only [dotProduct_smul, smul_eq_mul]
      have hj : (parityCheckTranspose parityCheck y) j = 0 := congr_fun hy j
      simp only [parityCheckTranspose, LinearMap.coe_mk, AddHom.coe_mk] at hj
      rw [mul_comm, hj, zero_mul]
    simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq'] at h
    exact h
  · intro hy; subst hy; simp [parityCheckTranspose]; ext j; simp [dotProduct]

/-- The transpose image lies in the dual code. -/
lemma parityCheckTranspose_mem_dualCode {s m : ℕ}
    (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (y : Fin m → 𝔽₂) :
    parityCheckTranspose parityCheck y ∈
      (ClassicalCode.dualCode (ClassicalCode.ofParityCheck parityCheck)).code := by
  rw [ClassicalCode.mem_dualCode_iff]
  intro c hc
  rw [ClassicalCode.code_eq_ker] at hc
  -- c ∈ ker(parityCheck), i.e., parityCheck c = 0
  have hpc : parityCheck c = 0 := LinearMap.mem_ker.mp hc
  -- dot(transpose(y), c) = ∑_j transpose(y)_j * c_j
  --   = ∑_j dot(y, H(e_j)) * c_j = dot(y, ∑_j c_j • H(e_j)) = dot(y, H(c)) = dot(y, 0) = 0
  -- dot(transpose(y), c) = ∑_j dot(y, H(e_j)) * c_j
  -- = dot(y, ∑_j c_j • H(e_j)) = dot(y, H(c)) = dot(y, 0) = 0
  change dotProduct (fun j => dotProduct y (parityCheck (Pi.single j 1))) c = 0
  simp only [dotProduct]
  -- Goal: ∑ x, (∑ i, y i * parityCheck (Pi.single x 1) i) * c x = 0
  -- Rewrite as: ∑ i, y i * (∑ x, parityCheck (Pi.single x 1) i * c x) = 0
  rw [show (∑ x, (∑ i, y i * parityCheck (Pi.single x 1) i) * c x) =
    ∑ i, y i * (∑ x, parityCheck (Pi.single x 1) i * c x) from by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext x; ring]
  -- ∑ x, H(e_x)_i * c_x = H(c)_i = 0
  suffices h : ∀ i, (∑ x, parityCheck (Pi.single x 1) i * c x) = 0 by
    simp [h]
  intro i
  have : (∑ x, parityCheck (Pi.single x 1) i * c x) = parityCheck c i := by
    conv_rhs => rw [show c = ∑ j, c j • Pi.single j 1 from by
      ext k; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']]
    simp [map_sum, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [this, hpc]; simp

/-- For nonzero `y`, the weight of the transpose image is at least `dLperp`. -/
lemma parityCheckTranspose_weight_ge {s m : ℕ}
    (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (hPC_surj : Function.Surjective parityCheck)
    (dLperp : ℕ)
    (hdLperp_def : dLperp = ClassicalCode.distance
      (ClassicalCode.dualCode (ClassicalCode.ofParityCheck parityCheck)))
    (y : Fin m → 𝔽₂) (hy : y ≠ 0) :
    dLperp ≤ hammingWeight (parityCheckTranspose parityCheck y) := by
  have hinj := parityCheckTranspose_injective parityCheck hPC_surj
  have hne : parityCheckTranspose parityCheck y ≠ 0 := by
    intro h; exact hy (hinj (by simp [h, map_zero]))
  have hmem := parityCheckTranspose_mem_dualCode parityCheck y
  rw [hdLperp_def]
  apply Nat.sInf_le
  exact ⟨parityCheckTranspose parityCheck y, hmem, hne, rfl⟩

/-! ## Coboundary at boundary edges -/

/-- The coboundary at an edge equals the sum of local transpose contributions. -/
lemma coboundary_eq_sum {s m : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]
    (Λ : Labeling G (s := s))
    (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (y : V → Fin m → 𝔽₂) (e : G.edgeSet) :
    coboundary G Λ parityCheck y e =
      ∑ v : V, dotProduct (y v) (differential Λ parityCheck (Pi.single e 1) v) := rfl

/-! ## Core combinatorial lemma -/

/-- For a boundary edge `e = {v, w}` with `w ∉ vertexSupport y`, the coboundary value
depends only on the contribution from `v`. -/
lemma coboundary_boundary_vertex {s m : ℕ} {G : SimpleGraph V} [DecidableRel G.Adj]
    (Λ : Labeling G (s := s))
    (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (y : V → Fin m → 𝔽₂)
    (e : G.edgeSet) (v : V) (hve : v ∈ (e : Sym2 V))
    (hother : ∀ w, w ∈ (e : Sym2 V) → w ≠ v → y w = 0) :
    coboundary G Λ parityCheck y e =
      dotProduct (y v) (differential Λ parityCheck (Pi.single e 1) v) := by
  unfold coboundary
  rw [show (∑ u : V, dotProduct (y u) (differential Λ parityCheck (Pi.single e 1) u)) =
    dotProduct (y v) (differential Λ parityCheck (Pi.single e 1) v) +
    ∑ u ∈ Finset.univ.erase v,
      dotProduct (y u) (differential Λ parityCheck (Pi.single e 1) u) from by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]]
  suffices h : ∑ u ∈ Finset.univ.erase v,
      dotProduct (y u) (differential Λ parityCheck (Pi.single e 1) u) = 0 by
    rw [h, add_zero]
  apply Finset.sum_eq_zero
  intro u hu
  have hu : u ≠ v := Finset.ne_of_mem_erase hu
  -- Either u is the other endpoint of e (in which case y u = 0) or
  -- u is not incident to e (in which case localView is zero)
  by_cases hue : u ∈ (e : Sym2 V)
  · -- u is the other endpoint, y u = 0
    have := hother u hue hu
    rw [this]; simp [dotProduct]
  · -- u is not incident to e, so localView Λ u (Pi.single e 1) = 0
    -- hence differential ... = parityCheck 0 = 0
    have hlv : localView Λ u (Pi.single e 1) = 0 := by
      ext i
      simp only [localView, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      -- (Pi.single e 1) at edge {u, (Λ u)⁻¹(i)} should be 0 since u ∉ e
      have : (⟨s(u, ((Λ u).symm i).val), G.mem_edgeSet.mpr ((Λ u).symm i).prop⟩ : G.edgeSet) ≠ e := by
        intro heq
        have : u ∈ (e : Sym2 V) := heq ▸ Sym2.mem_mk_left u _
        exact hue this
      simp [Pi.single_apply, this]
    rw [differential_apply, hlv, map_zero]; simp [dotProduct]

/-- For v ∈ S in an s-regular graph, the number of label positions corresponding to
neighbors in S, plus the boundary edge count at v, is at most s. -/
lemma nonBdyPos_add_boundary_le_degree
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {s : ℕ} (Λ : Labeling G (s := s)) (hreg : G.IsRegularOfDegree s)
    (S : Finset V) (v : V) (hv : v ∈ S) :
    (Finset.univ.filter (fun j : Fin s => ((Λ v).symm j).val ∈ S)).card +
      (edgeBoundaryAtVertex G S v).card ≤ s := by
  set nonBdyPos := Finset.univ.filter (fun j : Fin s => ((Λ v).symm j).val ∈ S)
  set complement := Finset.univ.filter (fun j : Fin s => ((Λ v).symm j).val ∉ S)
  -- nonBdyPos + complement = s (partition of Fin s)
  have h_partition : nonBdyPos.card + complement.card = s := by
    have h_union : nonBdyPos ∪ complement = Finset.univ := by
      ext j; simp [nonBdyPos, complement, or_iff_not_imp_left]
    have h_disj : Disjoint nonBdyPos complement := by
      rw [Finset.disjoint_filter]; intro j _ h1 h2; exact h2 h1
    rw [← Finset.card_union_of_disjoint h_disj, h_union, Finset.card_univ,
      Fintype.card_fin]
  -- Injection: boundary edges → complement
  -- For each boundary edge, the non-S endpoint has a label in complement
  suffices h : (edgeBoundaryAtVertex G S v).card ≤ complement.card by omega
  -- Handle s = 0 case separately (no edges, boundary is empty)
  rcases Nat.eq_zero_or_pos s with hs0 | hs_pos
  · subst hs0
    have hc0 : complement.card = 0 := by
      have : complement = ∅ := Finset.eq_empty_of_isEmpty complement
      simp [this]
    rw [hc0]
    exact edgeBoundaryAtVertex_le_degree G 0 hreg S v
  -- Map each boundary edge to the label of its non-S endpoint
  -- Use the other' function for the endpoint extraction
  let f : Sym2 V → Fin s := fun e =>
    if h : v ∈ e ∧ e ∈ G.edgeFinset then
      (Λ v) ⟨Sym2.Mem.other' h.1, by
        have he := G.mem_edgeFinset.mp h.2
        rw [← Sym2.other_spec' h.1] at he
        exact G.mem_edgeSet.mp he⟩
    else ⟨0, hs_pos⟩
  apply Finset.card_le_card_of_injOn f
  · -- f maps edgeBoundaryAtVertex into complement
    intro e he
    simp only [edgeBoundaryAtVertex, Finset.mem_coe, Finset.mem_filter] at he
    obtain ⟨he_bdy, hve⟩ := he
    have he_ef : e ∈ G.edgeFinset :=
      CheegerConstant.edgeBoundary_subset_edgeFinset G S he_bdy
    show f e ∈ ↑complement
    have hf_eq : f e = (Λ v) ⟨Sym2.Mem.other' hve, by
        have he := G.mem_edgeFinset.mp he_ef
        rw [← Sym2.other_spec' hve] at he
        exact G.mem_edgeSet.mp he⟩ := by
      show (if h : v ∈ e ∧ e ∈ G.edgeFinset then _ else _) = _
      rw [dif_pos ⟨hve, he_ef⟩]
    rw [hf_eq]
    simp only [complement, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.symm_apply_apply]
    -- The other endpoint is not in S
    -- Since e ∈ edgeBoundary, ∃ a ∈ S, b ∉ S with e = s(a, b)
    rw [CheegerConstant.mem_edgeBoundary] at he_bdy
    obtain ⟨_, a, b_, hab, haS, hbS⟩ := he_bdy
    -- v ∈ S, so v = a (b_ ∉ S)
    have hva : v = a := by
      rcases Sym2.mem_iff.mp (hab ▸ hve) with rfl | rfl
      · rfl
      · exact absurd hv hbS
    subst hva
    -- Now need: Sym2.Mem.other' hve ∉ S
    -- From Sym2.other_spec': s(v, other') = e = s(v, b_)
    have h_spec : s(v, Sym2.Mem.other' hve) = s(v, b_) := by
      rw [Sym2.other_spec' hve, hab]
    have hne : v ≠ b_ := fun h => hbS (h ▸ hv)
    have h_eq : Sym2.Mem.other' hve = b_ := by
      have h_other_mem : Sym2.Mem.other' hve ∈ (s(v, b_) : Sym2 V) := by
        have hspec := Sym2.other_spec' hve  -- s(v, other') = e
        rw [Sym2.mem_iff]
        have : s(v, Sym2.Mem.other' hve) = s(v, b_) := hspec.trans hab.symm
        rcases Sym2.eq_iff.mp this with ⟨_, h⟩ | ⟨_, h⟩
        · exact .inr h
        · exact .inl h
      rcases Sym2.mem_iff.mp h_other_mem with h | h
      · -- other' = v → s(v,v) = e contradicts no loops
        exfalso
        have hspec := Sym2.other_spec' hve  -- s(v, other') = e
        rw [h] at hspec  -- s(v, v) = e
        -- e = s(v, b_) from hab, so s(v, v) = s(v, b_)
        have hvvb : s(v, v) = s(v, b_) := hspec.trans hab.symm
        rcases Sym2.eq_iff.mp hvvb with ⟨_, hh⟩ | ⟨hh, _⟩ <;> exact hne hh
      · exact h
    rw [h_eq]; exact hbS
  · -- f is injective on edgeBoundaryAtVertex
    intro e₁ he₁ e₂ he₂ hfeq
    simp only [edgeBoundaryAtVertex, Finset.mem_coe, Finset.mem_filter] at he₁ he₂
    have hve₁ := he₁.2; have hve₂ := he₂.2
    have hef₁ := CheegerConstant.edgeBoundary_subset_edgeFinset G S he₁.1
    have hef₂ := CheegerConstant.edgeBoundary_subset_edgeFinset G S he₂.1
    have hadj₁ : G.Adj v (Sym2.Mem.other' hve₁) := by
      have he := G.mem_edgeFinset.mp hef₁
      rw [← Sym2.other_spec' hve₁] at he
      exact G.mem_edgeSet.mp he
    have hadj₂ : G.Adj v (Sym2.Mem.other' hve₂) := by
      have he := G.mem_edgeFinset.mp hef₂
      rw [← Sym2.other_spec' hve₂] at he
      exact G.mem_edgeSet.mp he
    have hf₁ : f e₁ = (Λ v) ⟨Sym2.Mem.other' hve₁, hadj₁⟩ := by
      show (if h : v ∈ e₁ ∧ e₁ ∈ G.edgeFinset then _ else _) = _
      rw [dif_pos ⟨hve₁, hef₁⟩]
    have hf₂ : f e₂ = (Λ v) ⟨Sym2.Mem.other' hve₂, hadj₂⟩ := by
      show (if h : v ∈ e₂ ∧ e₂ ∈ G.edgeFinset then _ else _) = _
      rw [dif_pos ⟨hve₂, hef₂⟩]
    -- (Λ v)(other₁) = (Λ v)(other₂) → other₁ = other₂
    have hinj := (Λ v).injective (hf₁.symm.trans (hfeq.trans hf₂))
    have h_sub : Sym2.Mem.other' hve₁ = Sym2.Mem.other' hve₂ :=
      congr_arg Subtype.val hinj
    -- other₁ = other₂ means the edges are equal
    have h1 := Sym2.other_spec' hve₁  -- s(v, other₁) = e₁
    have h2 := Sym2.other_spec' hve₂  -- s(v, other₂) = e₂
    rw [h_sub] at h1; rw [← h1]; exact h2

/-! ## Main Theorem -/

theorem expanderBitDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s)
    (hconn : G.Connected)
    (hreg : G.IsRegularOfDegree s)
    (hcard : 2 ≤ Fintype.card V)
    {m : ℕ} (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (hPC_surj : Function.Surjective parityCheck)
    (Λ : Labeling G (s := s))
    (kL : ℕ) (hkL : kL + m = s)
    (dLperp : ℕ) (hdLperp_ge : 2 ≤ dLperp) (hdLperp_le : dLperp ≤ s)
    (hdLperp_def : dLperp = ClassicalCode.distance
      (ClassicalCode.dualCode (ClassicalCode.ofParityCheck parityCheck)))
    (α : ℝ) (hα_pos : 0 < α) (hα_bound : α * m < 1)
    (y : V → Fin m → 𝔽₂)
    (hy_weight : (totalWeight y : ℝ) ≤ α * Fintype.card V * m) :
    let lam2 := secondLargestEigenvalue G hcard
    let β := ((dLperp - 1 : ℝ) - lam2 - α * m * ((s : ℝ) - lam2)) /
              (m * (dLperp - 1 : ℝ))
    β * totalWeight y ≤ coboundaryWeight G Λ parityCheck y := by
  intro lam2 β
  by_cases hy0 : y = 0
  · subst hy0
    simp only [totalWeight, hammingWeight, Pi.zero_apply, hammingNorm_zero,
      Finset.sum_const_zero, Nat.cast_zero, mul_zero]
    exact Nat.cast_nonneg _
  set S := vertexSupport y
  have hS_pos : 0 < S.card := (vertexSupport_nonempty hy0).card_pos
  have hm_pos : 0 < m := by
    by_contra h; push_neg at h
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero h
    subst hm0; exact hy0 (funext fun v => funext fun i => i.elim0)
  have hS_le : (S.card : ℝ) ≤ α * m * Fintype.card V := by
    calc (S.card : ℝ) ≤ totalWeight y :=
          by exact_mod_cast card_vertexSupport_le_totalWeight y
      _ ≤ α * Fintype.card V * m := hy_weight
      _ = α * m * Fintype.card V := by ring
  set α' := α * m
  set b := (dLperp : ℝ) - 1
  have hα'_pos : 0 < α' := mul_pos hα_pos (Nat.cast_pos.mpr hm_pos)
  have hα'_lt_one : α' < 1 := hα_bound
  have hb_pos : 0 < b := by
    show 0 < (dLperp : ℝ) - 1
    have : (2 : ℝ) ≤ dLperp := by exact_mod_cast hdLperp_ge
    linarith
  have hb_le_s : b ≤ (s : ℝ) := by
    show (dLperp : ℝ) - 1 ≤ s
    have : (dLperp : ℝ) ≤ s := by exact_mod_cast hdLperp_le
    linarith
  have hS_le' : (S.card : ℝ) ≤ α' * Fintype.card V := by linarith
  set A := highExpansionVertices G S s b
  have h_lem3 := relativeVertexToEdgeExpansion G s α' b hα'_pos hα'_lt_one hb_pos hb_le_s
    hconn hreg hcard S hS_le'
  have h_A_ge : ((b - lam2) - α' * ((s : ℝ) - lam2)) / b * S.card ≤ (A.card : ℝ) := h_lem3
  have h_S_ge : (totalWeight y : ℝ) / m ≤ S.card := totalWeight_div_le_card hm_pos y
  suffices h_cob : (A.card : ℝ) ≤ coboundaryWeight G Λ parityCheck y by
    have hm_pos_real : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
    have hβ_eq : β = ((b - lam2) - α' * ((s : ℝ) - lam2)) / (↑m * b) := by
      show ((dLperp - 1 : ℝ) - lam2 - α * m * ((s : ℝ) - lam2)) /
        (m * (dLperp - 1 : ℝ)) =
        (((dLperp : ℝ) - 1 - lam2) - α * ↑m * ((s : ℝ) - lam2)) /
        (↑m * ((dLperp : ℝ) - 1))
      ring
    rw [hβ_eq]
    by_cases h_coeff : 0 ≤ ((b - lam2) - α' * ((s : ℝ) - lam2)) / b
    · calc ((b - lam2) - α' * ((s : ℝ) - lam2)) / (↑m * b) * totalWeight y
          = ((b - lam2) - α' * ((s : ℝ) - lam2)) / b *
            ((totalWeight y : ℝ) / m) := by
            field_simp
        _ ≤ ((b - lam2) - α' * ((s : ℝ) - lam2)) / b * S.card :=
            mul_le_mul_of_nonneg_left h_S_ge h_coeff
        _ ≤ (A.card : ℝ) := h_A_ge
        _ ≤ coboundaryWeight G Λ parityCheck y := h_cob
    · push_neg at h_coeff
      have hneg : b - lam2 - α' * (↑s - lam2) < 0 := by
        rcases div_neg_iff.mp h_coeff with ⟨_, h⟩ | ⟨h, _⟩
        · linarith
        · exact h
      have hmb_pos : (0 : ℝ) < ↑m * b := mul_pos hm_pos_real hb_pos
      have : ((b - lam2) - α' * ((s : ℝ) - lam2)) / (↑m * b) *
          totalWeight y ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (div_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) (le_of_lt hmb_pos))
          (Nat.cast_nonneg _)
      have : (0 : ℝ) ≤ ↑(coboundaryWeight G Λ parityCheck y) := Nat.cast_nonneg _
      linarith
  -- Core combinatorial argument: coboundaryWeight ≥ A.card
  -- For each v ∈ A, find a boundary edge with nonzero coboundary
  -- These edges are distinct → injection → coboundaryWeight ≥ |A|
  suffices h_nat : A.card ≤ coboundaryWeight G Λ parityCheck y by exact_mod_cast h_nat
  -- coboundaryWeight = #{e : G.edgeSet | coboundary(...)(e) ≠ 0}
  unfold coboundaryWeight
  rw [show hammingNorm (coboundary G Λ parityCheck y) =
    (Finset.univ.filter (fun e : G.edgeSet => coboundary G Λ parityCheck y e ≠ 0)).card from by
    simp [hammingNorm]]
  -- Build an injection from A to {e | coboundary(y)(e) ≠ 0}
  -- For each v ∈ A, the local transpose vector has weight ≥ dLperp
  -- and non-boundary edges ≤ dLperp - 1, so there's a boundary edge
  -- where the coboundary is nonzero
  -- Step A: For v ∈ A ⊆ S, y v ≠ 0
  have hA_sub_S : A ⊆ S := highExpansionVertices_subset G S s b
  have hy_ne : ∀ v ∈ A, y v ≠ 0 := by
    intro v hv
    have hvS : v ∈ S := hA_sub_S hv
    simp only [S, vertexSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hvS
    exact hvS
  -- Step B: For v ∈ A, there's a boundary edge e incident to v
  -- where coboundary(y)(e) ≠ 0
  have h_exists : ∀ v ∈ A, ∃ e : G.edgeSet,
      v ∈ (e : Sym2 V) ∧
      (e : Sym2 V) ∈ CheegerConstant.edgeBoundary G S ∧
      coboundary G Λ parityCheck y e ≠ 0 := by
    intro v hv
    -- v ∈ A means boundary degree ≥ s - b = s - (dLperp - 1)
    have hvA : v ∈ highExpansionVertices G S s b := hv
    simp only [highExpansionVertices, Finset.mem_filter] at hvA
    have hvS := hvA.1
    have hbdy_ge := hvA.2  -- (s : ℝ) - b ≤ |(δS)_v|
    -- Weight of transpose image ≥ dLperp
    have h_wt := parityCheckTranspose_weight_ge parityCheck hPC_surj dLperp hdLperp_def
      (y v) (hy_ne v hv)
    -- Non-boundary edges at v: edges {v, w} with w ∈ S
    -- These correspond to positions in Fin s where the labeling gives a neighbor in S
    -- Number of non-boundary edges = s - |(δS)_v| ≤ b = dLperp - 1
    -- The transpose vector has ≥ dLperp nonzero positions
    -- By pigeonhole, at least one nonzero position corresponds to a boundary edge
    -- The transpose vector is: j ↦ dot(y v, parityCheck(e_j))
    set tv := parityCheckTranspose parityCheck (y v) with htv_def
    -- tv has weight ≥ dLperp
    -- Positions: {j : Fin s | tv j ≠ 0}
    set suppTV := Finset.univ.filter (fun j : Fin s => tv j ≠ 0)
    have h_suppTV_card : dLperp ≤ suppTV.card := by
      rwa [show suppTV.card = hammingWeight tv from by
        simp [hammingWeight, hammingNorm, suppTV]]
    -- Positions corresponding to non-boundary neighbors
    set nonBdyPos := Finset.univ.filter (fun j : Fin s =>
      ((Λ v).symm j).val ∈ S)
    -- nonBdyPos.card = number of neighbors of v in S = s - |(δS)_v|
    -- Actually, we know |(δS)_v| ≥ s - b, so non-boundary ≤ b = dLperp - 1
    -- But let me use a simpler bound: suppTV ⊄ nonBdyPos since |suppTV| > |nonBdyPos|
    -- So ∃ j ∈ suppTV \ nonBdyPos
    have h_nonBdy_card : (nonBdyPos.card : ℝ) ≤ b := by
      have h_total := nonBdyPos_add_boundary_le_degree Λ hreg S v hvS
      have h1 : (↑nonBdyPos.card : ℝ) + ↑(edgeBoundaryAtVertex G S v).card ≤ ↑s := by
        exact_mod_cast h_total
      linarith [hbdy_ge]
    -- Since suppTV.card ≥ dLperp and nonBdyPos.card ≤ dLperp - 1 = b < dLperp
    -- there exists j ∈ suppTV \ nonBdyPos
    have h_exists_j : ∃ j ∈ suppTV, j ∉ nonBdyPos := by
      by_contra h_all
      push_neg at h_all
      have h_sub : suppTV ⊆ nonBdyPos := h_all
      have h_card_le := Finset.card_le_card h_sub
      have h_cast : (dLperp : ℝ) ≤ (nonBdyPos.card : ℝ) := by
        exact_mod_cast le_trans h_suppTV_card h_card_le
      linarith
    obtain ⟨j, hj_supp, hj_not_nonBdy⟩ := h_exists_j
    -- j ∈ suppTV means tv j ≠ 0, i.e., dot(y v, parityCheck(e_j)) ≠ 0
    simp only [suppTV, Finset.mem_filter, Finset.mem_univ, true_and] at hj_supp
    simp only [nonBdyPos, Finset.mem_filter, Finset.mem_univ, true_and] at hj_not_nonBdy
    -- j ∉ nonBdyPos means (Λ v)⁻¹(j) ∉ S
    -- So the edge e = {v, (Λ v)⁻¹(j)} is a boundary edge
    set w_sub := (Λ v).symm j with hw_sub_def
    have hadj : G.Adj v w_sub.val := w_sub.prop
    set e_val := s(v, w_sub.val) with he_val_def
    have he_mem : e_val ∈ G.edgeSet := G.mem_edgeSet.mpr hadj
    set e : G.edgeSet := ⟨e_val, he_mem⟩
    refine ⟨e, ?_, ?_, ?_⟩
    · -- v ∈ e
      exact Sym2.mem_mk_left v w_sub.val
    · -- e ∈ edgeBoundary G S
      rw [CheegerConstant.mem_edgeBoundary]
      exact ⟨G.mem_edgeFinset.mpr he_mem, v, w_sub.val, rfl, hvS, hj_not_nonBdy⟩
    · -- coboundary(y)(e) ≠ 0
      -- For a boundary edge, coboundary depends only on v's contribution
      have h_eq := coboundary_boundary_vertex Λ parityCheck y e v
        (Sym2.mem_mk_left v w_sub.val)
        (by
          intro u hu hne
          -- e = s(v, w_sub.val), so u ∈ e means u = v or u = w_sub.val
          have : u ∈ (s(v, w_sub.val) : Sym2 V) := hu
          rcases Sym2.mem_iff.mp this with rfl | rfl
          · exact absurd rfl hne
          · -- u = w_sub.val, which is ∉ S = vertexSupport y
            simp only [S, vertexSupport, Finset.mem_filter, Finset.mem_univ,
              true_and, not_not] at hj_not_nonBdy ⊢
            exact hj_not_nonBdy)
      rw [h_eq]
      -- Now show dot(y v, differential ... e v) ≠ 0
      -- differential Λ parityCheck (Pi.single e 1) v = parityCheck (localView Λ v (Pi.single e 1))
      rw [differential_apply]
      -- localView Λ v (Pi.single e 1) = Pi.single j 1 (since the labeling assigns j to edge e at v)
      -- So this becomes dot(y v, parityCheck (Pi.single j 1)) = tv j ≠ 0
      -- Need: localView Λ v (Pi.single e 1) i = if i = j then 1 else 0
      have h_lv : localView Λ v (Pi.single e 1) = Pi.single j 1 := by
        ext i
        simp only [localView, LinearMap.coe_mk, AddHom.coe_mk]
        -- Goal: (Pi.single e 1) ⟨s(v, ((Λ v).symm i).val), _⟩ = Pi.single j 1 i
        by_cases hij : i = j
        · subst hij
          simp only [Pi.single_apply, if_pos rfl]
          -- (Λ v).symm i = w_sub, so the edge matches e
          have h_w : ((Λ v).symm i) = w_sub := rfl
          have h_edge_eq : (⟨s(v, ((Λ v).symm i).val), G.mem_edgeSet.mpr ((Λ v).symm i).prop⟩ : G.edgeSet) = e := by
            exact Subtype.ext (by simp [h_w, e, e_val])
          rw [h_edge_eq]; simp [Pi.single_apply]
        · simp only [Pi.single_apply, if_neg hij]
          have hne_edge : (⟨s(v, ((Λ v).symm i).val), G.mem_edgeSet.mpr ((Λ v).symm i).prop⟩ : G.edgeSet) ≠ e := by
            intro heq
            apply hij
            have : ((Λ v).symm i).val = w_sub.val := by
              have h_eq_sym := congr_arg Subtype.val heq
              simp only [e, he_val_def] at h_eq_sym
              have hne_v : v ≠ ((Λ v).symm i).val := G.ne_of_adj ((Λ v).symm i).prop
              rcases Sym2.eq_iff.mp h_eq_sym with ⟨_, h⟩ | ⟨_, h⟩
              · exact h
              · exact absurd h.symm hne_v
            exact (Λ v).symm.injective (Subtype.ext this) |>.symm |>.symm
          simp [Pi.single_apply, hne_edge]
      rw [h_lv]
      -- Now goal is: dotProduct (y v) (parityCheck (Pi.single j 1)) ≠ 0
      -- This equals tv j = (parityCheckTranspose parityCheck (y v)) j
      change dotProduct (y v) (parityCheck (Pi.single j 1)) ≠ 0
      exact hj_supp
  -- Step C: Choose a witness edge for each v ∈ A
  choose f hf_mem hf_bdy hf_ne using h_exists
  -- Create a non-dependent function for Finset.card_le_card_of_injOn
  -- Use an arbitrary default edge for vertices not in A
  -- First establish that G has at least one edge (connected + ≥ 2 vertices)
  haveI : Nonempty G.edgeSet := by
    -- G is connected with ≥ 2 vertices, so it has at least one edge
    -- G is s-regular with s ≥ 1, so any vertex has a neighbor
    obtain ⟨v₀⟩ := hconn.nonempty
    have hdeg : G.degree v₀ = s := hreg v₀
    have hpos : 0 < G.degree v₀ := by omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    rw [SimpleGraph.mem_neighborFinset] at hw
    exact ⟨⟨s(v₀, w), G.mem_edgeSet.mpr hw⟩⟩
  let g : V → G.edgeSet := fun v =>
    if hv : v ∈ A then f v hv else Classical.choice ‹Nonempty G.edgeSet›
  -- Step D: g is injective on A
  have h_inj : Set.InjOn g ↑A := by
    intro v₁ hv₁' v₂ hv₂' heq
    have hv₁ : v₁ ∈ A := Finset.mem_coe.mp hv₁'
    have hv₂ : v₂ ∈ A := Finset.mem_coe.mp hv₂'
    simp only [g, dif_pos hv₁, dif_pos hv₂] at heq
    have hv₁_mem := hf_mem v₁ hv₁
    have hv₂_mem := heq ▸ hf_mem v₂ hv₂
    have hv₁_S := hA_sub_S hv₁
    have hv₂_S := hA_sub_S hv₂
    have hbdy₁ := hf_bdy v₁ hv₁
    rw [CheegerConstant.mem_edgeBoundary] at hbdy₁
    obtain ⟨_, a, b_, hab, haS, hbS⟩ := hbdy₁
    have hv₁_eq : v₁ = a := by
      rcases Sym2.mem_iff.mp (hab ▸ hv₁_mem) with rfl | rfl
      · rfl
      · exact absurd hv₁_S hbS
    have hv₂_eq : v₂ = a := by
      rcases Sym2.mem_iff.mp (hab ▸ hv₂_mem) with rfl | rfl
      · rfl
      · exact absurd hv₂_S hbS
    rw [hv₁_eq, hv₂_eq]
  -- Step E: Map A into support of coboundary
  apply Finset.card_le_card_of_injOn g
  · -- g maps A into {e | coboundary(y)(e) ≠ 0}
    intro v hv
    have hvA : v ∈ A := Finset.mem_coe.mp hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_univ, true_and,
      Set.mem_sep_iff]
    show coboundary G Λ parityCheck y (g v) ≠ 0
    simp only [g, dif_pos hvA]
    exact hf_ne v hvA
  · exact h_inj

end ExpanderBitDegree
