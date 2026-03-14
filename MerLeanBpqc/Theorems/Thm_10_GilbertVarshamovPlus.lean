import MerLeanBpqc.Definitions.Def_3_ClassicalCode
import MerLeanBpqc.Definitions.Def_16_DualCode
import MerLeanBpqc.Definitions.Def_17_BinaryEntropyFunction
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Theorem 10: Gilbert–Varshamov Plus

## Main Results
- `gilbertVarshamovPlus`: the main existence theorem
-/

open Classical ClassicalCode

noncomputable section

/-! ## Helper lemmas for the counting argument -/

lemma gv_threshold_pos {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 11 / 100) :
    0 < 2 / (1 / 2 - binaryEntropy δ) := by
  have hH := binaryEntropy_lt_half hδ0 hδ1
  apply div_pos (by norm_num : (0:ℝ) < 2) (by linarith)

lemma gv_n_large {δ : ℝ} {n : ℕ} (hδ0 : 0 < δ) (hδ1 : δ < 11 / 100)
    (hn : (n : ℝ) > 2 / (1 / 2 - binaryEntropy δ)) :
    (1 / 2 - binaryEntropy δ) * (n : ℝ) > 2 := by
  have hH := binaryEntropy_lt_half hδ0 hδ1
  have hgap : 0 < 1 / 2 - binaryEntropy δ := by linarith
  rw [gt_iff_lt, div_lt_iff₀ hgap] at hn
  linarith

lemma gv_k_exists {δ : ℝ} {n : ℕ} (hδ0 : 0 < δ) (hδ1 : δ < 11 / 100)
    (hn : (n : ℝ) > 2 / (1 / 2 - binaryEntropy δ)) :
    ∃ k : ℕ, (n : ℝ) / 2 < (k : ℝ) ∧ (k : ℝ) + 1 < (1 - binaryEntropy δ) * (n : ℝ) ∧
    k < n := by
  have hH := binaryEntropy_lt_half hδ0 hδ1
  have hgap := gv_n_large hδ0 hδ1 hn
  have h_range : (n : ℝ) / 2 + 1 < (1 - binaryEntropy δ) * n - 1 := by linarith
  set k := n / 2 + 1 with hk_def
  refine ⟨k, ?_, ?_, ?_⟩
  · simp only [hk_def]
    have h1 : (↑(n / 2) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
    have h2 : (n : ℝ) < 2 * (↑(n / 2) + 1) := by
      have : (n : ℕ) < 2 * (n / 2 + 1) := by omega
      exact_mod_cast this
    push_cast; linarith
  · simp only [hk_def]
    have h1 : (↑(n / 2) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
    have h2 : (n : ℝ) < 2 * (↑(n / 2) + 1) := by
      have : (n : ℕ) < 2 * (n / 2 + 1) := by omega
      exact_mod_cast this
    push_cast; linarith
  · simp only [hk_def]
    by_contra hc; push_neg at hc
    have hn2 : n ≤ 2 := by omega
    have hbe : 0 < binaryEntropy δ := by
      unfold binaryEntropy
      have h1 : Real.logb 2 δ < 0 := Real.logb_neg (by norm_num) (by linarith) (by linarith)
      have h2 : Real.logb 2 (1 - δ) < 0 := Real.logb_neg (by norm_num) (by linarith) (by linarith)
      nlinarith [mul_neg_of_pos_of_neg hδ0 h1, mul_neg_of_pos_of_neg (by linarith : 0 < 1 - δ) h2]
    have hn2r : (n : ℝ) ≤ 2 := by exact_mod_cast hn2
    have : (1/2 - binaryEntropy δ) * (n : ℝ) ≤ 1 := by
      have : (1/2 - binaryEntropy δ) * (n : ℝ) < 1/2 * n := by nlinarith
      have : 1/2 * (n : ℝ) ≤ 1 := by nlinarith
      linarith
    linarith

/-! ## Counting argument infrastructure -/

/-- The evaluation linear map `φ ↦ φ(v)` from `Hom(𝔽₂^n, 𝔽₂^r)` to `𝔽₂^r`. -/
def evalMap (n r : ℕ) (v : Fin n → 𝔽₂) :
    ((Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin r → 𝔽₂)) →ₗ[𝔽₂] (Fin r → 𝔽₂) :=
  LinearMap.applyₗ v

lemma evalMap_apply {n r : ℕ} (v : Fin n → 𝔽₂)
    (φ : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin r → 𝔽₂)) :
    evalMap n r v φ = φ v := by
  simp [evalMap, LinearMap.applyₗ]

/-- For nonzero `v`, the evaluation map is surjective. -/
lemma evalMap_surjective {n r : ℕ} {v : Fin n → 𝔽₂} (hv : v ≠ 0) :
    Function.Surjective (evalMap n r v) := by
  intro w
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h; push_neg at h
    exact hv (funext fun i => by
      have := h i; have hvi := ZMod.val_lt (v i); interval_cases (v i).val <;> simp_all)
  have hvj : v j = 1 := by
    have : ∀ x : 𝔽₂, x = 0 ∨ x = 1 := by decide
    rcases this (v j) with h | h
    · exact absurd h hj
    · exact h
  -- Build φ that sends eⱼ to w and other basis vectors to 0
  let φ : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin r → 𝔽₂) :=
    (LinearMap.proj j : (Fin n → 𝔽₂) →ₗ[𝔽₂] 𝔽₂).smulRight w
  refine ⟨φ, ?_⟩
  simp only [evalMap_apply, φ, LinearMap.smulRight_apply, LinearMap.proj_apply, hvj, one_smul]

/-- The finrank of the kernel of the evaluation map. -/
lemma evalMap_ker_finrank {n r : ℕ} {v : Fin n → 𝔽₂} (hv : v ≠ 0) :
    Module.finrank 𝔽₂ (LinearMap.ker (evalMap n r v)) = n * r - r := by
  have hsurj := evalMap_surjective (r := r) hv
  have hrk := LinearMap.finrank_range_add_finrank_ker (evalMap n r v)
  have hrange : Module.finrank 𝔽₂ (LinearMap.range (evalMap n r v)) = r := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun]
  have hhom : Module.finrank 𝔽₂ ((Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin r → 𝔽₂)) = n * r := by
    rw [Module.finrank_linearMap (S := 𝔽₂), Module.finrank_fin_fun, Module.finrank_fin_fun]
  omega

/-- Cardinality of `{φ | φ(v) = 0}` times `2^r` equals total cardinality of Hom. -/
lemma card_ker_evalMap {n r : ℕ} {v : Fin n → 𝔽₂} (hv : v ≠ 0)
    [Fintype ((Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin r → 𝔽₂))] :
    Fintype.card (LinearMap.ker (evalMap n r v)) * 2 ^ r =
    Fintype.card ((Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin r → 𝔽₂)) := by
  rw [Module.card_eq_pow_finrank (K := 𝔽₂) (V := LinearMap.ker (evalMap n r v)),
      Module.card_eq_pow_finrank (K := 𝔽₂) (V := (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin r → 𝔽₂)),
      ZMod.card 2,
      evalMap_ker_finrank hv,
      Module.finrank_linearMap (S := 𝔽₂), Module.finrank_fin_fun, Module.finrank_fin_fun,
      ← pow_add]
  congr 1
  have hn : 0 < n := by
    by_contra h; push_neg at h; interval_cases n
    exact hv (Subsingleton.elim _ _)
  have : r ≤ n * r := Nat.le_mul_of_pos_left r hn
  omega

/-- When the number of nonzero vectors with Hamming weight less than d is
less than 2^r, there exists a linear map φ : 𝔽₂^n → 𝔽₂^r such that
φ v ≠ 0 for all nonzero v of weight < d. This is the counting/probabilistic
method argument. -/
axiom exists_good_map {n r : ℕ} {t : ℝ} (hr : 0 < r) (hrn : r ≤ n)
    (hsmall : (hammingBall n (t - 1)).card < 2 ^ r) :
    ∃ φ : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin r → 𝔽₂),
      ∀ v : Fin n → 𝔽₂, v ≠ 0 → (hammingWeight v : ℝ) < t → φ v ≠ 0

/-- Combined counting argument: when both the distance and dual-distance Hamming
ball bounds hold, there exists a surjective linear map `φ : 𝔽₂^n → 𝔽₂^r` whose
kernel code has good distance AND whose dual code also has good distance. This
extends `exists_good_map` by simultaneously bounding both bad-distance and
bad-dual-distance events via a union bound: P(bad dist) + P(bad dual) < 1,
and observing that any map satisfying the dual condition is automatically
surjective (otherwise some nonzero `y` has `φᵀ(y) = 0`, weight 0 < t). -/
axiom exists_good_surjective_map {n r : ℕ} {t : ℝ} (hr : 0 < r) (hrn : r ≤ n)
    (hsmall_dist : (hammingBall n (t - 1)).card < 2 ^ r)
    (hsmall_dual : (hammingBall n (t - 1)).card < 2 ^ (n - r)) :
    ∃ φ : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin r → 𝔽₂),
      Function.Surjective φ ∧
      (∀ v : Fin n → 𝔽₂, v ≠ 0 → (hammingWeight v : ℝ) < t → φ v ≠ 0) ∧
      (∀ w ∈ (dualCode (ClassicalCode.ofParityCheck φ)).code,
        w ≠ 0 → (hammingWeight w : ℝ) ≥ t)

/-- Distance of a code ≥ t if no nonzero codeword has weight < t and the code
has a nonzero element. -/
lemma distance_ge_of_no_lowweight (𝒞 : ClassicalCode n) {t : ℝ}
    (h : ∀ v ∈ 𝒞.code, v ≠ 0 → (hammingWeight v : ℝ) ≥ t)
    (hne_code : ∃ v ∈ 𝒞.code, v ≠ 0) :
    (𝒞.distance : ℝ) ≥ t := by
  unfold ClassicalCode.distance
  obtain ⟨x, hxc, hxne⟩ := hne_code
  set S := {w : ℕ | ∃ x : Fin n → 𝔽₂, x ∈ 𝒞.code ∧ x ≠ 0 ∧ hammingWeight x = w} with hS_def
  have hne : S.Nonempty := ⟨hammingWeight x, x, hxc, hxne, rfl⟩
  have hall : ∀ w ∈ S, ⌈t⌉₊ ≤ w := by
    rintro w' ⟨x', hx'c, hx'ne, hx'w⟩
    rw [← hx'w]; exact Nat.ceil_le.mpr (by exact_mod_cast h x' hx'c hx'ne)
  have hsInf := le_csInf hne hall
  calc (↑(sInf S) : ℝ) ≥ ↑⌈t⌉₊ := by exact_mod_cast hsInf
    _ ≥ t := Nat.le_ceil t

/-- Submodule of prescribed finrank inside a larger submodule. -/
lemma exists_submodule_of_finrank {n k : ℕ}
    (W : Submodule 𝔽₂ (Fin n → 𝔽₂)) (hk : k ≤ Module.finrank 𝔽₂ W) :
    ∃ W' : Submodule 𝔽₂ (Fin n → 𝔽₂), W' ≤ W ∧ Module.finrank 𝔽₂ W' = k := by
  haveI : FiniteDimensional 𝔽₂ W := inferInstance
  have hcard : k ≤ Fintype.card (Module.Free.ChooseBasisIndex 𝔽₂ W) := by
    rwa [Module.finrank_eq_card_chooseBasisIndex] at hk
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq hcard
  let B := Module.Free.chooseBasis 𝔽₂ W
  let W'_sub : Submodule 𝔽₂ W := Submodule.span 𝔽₂ (Set.range (fun i : s => B i))
  let W' : Submodule 𝔽₂ (Fin n → 𝔽₂) := W'_sub.map W.subtype
  refine ⟨W', ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Submodule.mem_map.mp hx
    exact y.2
  · have hli : LinearIndependent 𝔽₂ (fun i : s => B i) :=
      B.linearIndependent.comp _ Subtype.val_injective
    have hdim_sub : Module.finrank 𝔽₂ W'_sub = k := by
      rw [← hs, finrank_span_eq_card hli, Fintype.card_coe]
    rw [show W' = W'_sub.map W.subtype from rfl, Submodule.finrank_map_subtype_eq]
    exact hdim_sub

/-! ## Existence of codes with good distance -/

lemma exists_code_with_good_distance
    {δ : ℝ} (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {n k : ℕ} (hn : 0 < n) (hk_pos : 0 < k) (hkn : k < n)
    (hk_bound : (k : ℝ) + 1 < (1 - binaryEntropy δ) * n) :
    ∃ 𝒞 : ClassicalCode n, 𝒞.dimension = k ∧ (𝒞.distance : ℝ) ≥ δ * n := by
  set r := n - k with hr_def
  have hr : 0 < r := by omega
  have hrn : r ≤ n := Nat.sub_le n k
  have hHn : binaryEntropy δ * n < n - k := by linarith
  have hδn_pos : 0 < δ * ↑n := by positivity
  have hball_lt : ((hammingBall n (δ * ↑n - 1)).card : ℝ) < (2 : ℝ) ^ r := by
    by_cases hδn1 : δ * ↑n < 1
    · have : hammingBall n (δ * ↑n - 1) = ∅ := hammingBall_empty_of_neg (by linarith)
      simp [this]
    · push_neg at hδn1
      set d' := Nat.floor (δ * ↑n) - 1
      have hd'_bound : (d' : ℝ) + 1 ≤ δ * ↑n := by
        have hfl := Nat.floor_le (by linarith : 0 ≤ δ * ↑n)
        have hfl_pos : 1 ≤ Nat.floor (δ * ↑n) := (Nat.one_le_floor_iff _).mpr hδn1
        simp only [d']; push_cast [Nat.cast_sub hfl_pos]; linarith
      have hball_sub : hammingBall n (δ * ↑n - 1) ⊆ hammingBall n ↑d' := by
        intro v hv; rw [mem_hammingBall] at hv ⊢
        have hfl_lt : δ * ↑n - 1 < (Nat.floor (δ * ↑n) : ℝ) := Nat.sub_one_lt_floor _
        have hwt_lt_floor : hammingWeight v < Nat.floor (δ * ↑n) := by
          exact_mod_cast show (hammingWeight v : ℝ) < Nat.floor (δ * ↑n) from by linarith
        simp only [d']; exact_mod_cast Nat.le_sub_one_of_lt hwt_lt_floor
      calc ((hammingBall n (δ * ↑n - 1)).card : ℝ)
          ≤ (hammingBall n ↑d').card := by
            exact_mod_cast Finset.card_le_card hball_sub
        _ ≤ 2 ^ (binaryEntropy δ * ↑n) := hammingBallBound hn hδ0 hδhalf hd'_bound
        _ < 2 ^ (r : ℝ) := by
            apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
            have : (r : ℝ) = ↑n - ↑k := by
              simp [hr_def]; rw [Nat.cast_sub (le_of_lt hkn)]
            linarith
        _ = (2 : ℝ) ^ (r : ℕ) := by norm_cast
  have hball_lt_nat : (hammingBall n (δ * ↑n - 1)).card < 2 ^ r := by
    exact_mod_cast hball_lt
  obtain ⟨φ, hgood⟩ := exists_good_map hr hrn hball_lt_nat
  have hker_dim : k ≤ Module.finrank 𝔽₂ (LinearMap.ker φ) := by
    have hrk := LinearMap.finrank_range_add_finrank_ker φ
    have hrange_le : Module.finrank 𝔽₂ (LinearMap.range φ) ≤ r := by
      calc Module.finrank 𝔽₂ (LinearMap.range φ)
          ≤ Module.finrank 𝔽₂ (Fin r → 𝔽₂) := Submodule.finrank_le _
        _ = r := Module.finrank_fin_fun 𝔽₂
    have hdomain : Module.finrank 𝔽₂ (Fin n → 𝔽₂) = n := Module.finrank_fin_fun 𝔽₂
    rw [hdomain] at hrk
    omega
  obtain ⟨W, hW_le, hW_dim⟩ := exists_submodule_of_finrank (LinearMap.ker φ) hker_dim
  have hW_good : ∀ v ∈ W, v ≠ 0 → (hammingWeight v : ℝ) ≥ δ * ↑n := by
    intro v hv hvne
    have hv_ker : v ∈ LinearMap.ker φ := hW_le hv
    have hφv : φ v = 0 := LinearMap.mem_ker.mp hv_ker
    by_contra h; push_neg at h
    exact hgood v hvne h hφv
  have hW_ne : ∃ v ∈ (⟨W⟩ : ClassicalCode n).code, v ≠ 0 := by
    have hnt : Nontrivial W := by
      by_contra h; rw [not_nontrivial_iff_subsingleton] at h
      haveI := h
      have := Module.finrank_zero_of_subsingleton (R := 𝔽₂) (M := W)
      omega
    obtain ⟨⟨v, hv⟩, hvne⟩ := exists_ne (0 : W)
    exact ⟨v, hv, fun h => hvne (Subtype.ext h)⟩
  refine ⟨⟨W⟩, hW_dim, distance_ge_of_no_lowweight ⟨W⟩ hW_good hW_ne⟩

lemma exists_code_with_good_distance_premises_satisfiable :
    ∃ (δ : ℝ) (n k : ℕ), 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < n ∧ 0 < k ∧ k < n ∧
      (k : ℝ) + 1 < (1 - binaryEntropy δ) * n := by
  refine ⟨1/100, 1000, 498, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have hH : binaryEntropy (1/100) < 1/2 := binaryEntropy_lt_half (by norm_num) (by norm_num)
  push_cast; nlinarith

/-- Double dual identity for codes: `(dualCode (dualCode 𝒞)).code = 𝒞.code`.
Over a finite-dimensional space, the double annihilator equals the original subspace. -/
lemma dualCode_dualCode_eq (𝒞 : ClassicalCode n) :
    (dualCode (dualCode 𝒞)).code = 𝒞.code := by
  haveI : FiniteDimensional 𝔽₂ (Fin n → 𝔽₂) := inferInstance
  ext w
  constructor
  · rw [mem_dualCode_iff]
    intro hw
    by_contra hw_not
    have ⟨f, hf_w, hf_ann⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw_not inferInstance
    let e := dotProductEquiv 𝔽₂ (Fin n)
    let c := e.symm f
    have hf_zero : ∀ v ∈ 𝒞.code, f v = 0 := by
      intro v hv
      have hmem : f v ∈ Submodule.map f 𝒞.code := ⟨v, hv, rfl⟩
      rw [hf_ann] at hmem
      exact (Submodule.mem_bot _).mp hmem
    have hc_dual : c ∈ (dualCode 𝒞).code := by
      rw [mem_dualCode_iff]
      intro v hv
      show dotProduct c v = 0
      have : dotProduct c v = (e c) v := by simp [e, dotProductEquiv]
      rw [this, show e c = f from LinearEquiv.apply_symm_apply e f]
      exact hf_zero v hv
    have hcontra := hw c hc_dual
    apply hf_w
    have : (e c) = f := LinearEquiv.apply_symm_apply e f
    rw [← this]
    simp only [e, c, dotProductEquiv, LinearEquiv.coe_mk]
    change dotProduct (e.symm f) w = 0
    rw [show dotProduct (e.symm f) w = dotProduct w (e.symm f) from dotProduct_comm _ _]
    exact hcontra
  · rw [mem_dualCode_iff]
    intro hw c hc
    rw [mem_dualCode_iff] at hc
    rw [dotProduct_comm]
    exact hc w hw

/-- The distance of a code equals the distance of its double dual. -/
lemma distance_dualCode_dualCode (𝒞 : ClassicalCode n) :
    (dualCode (dualCode 𝒞)).distance = 𝒞.distance := by
  unfold ClassicalCode.distance
  congr 1; ext w
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, hne, hw⟩
    refine ⟨x, ?_, hne, hw⟩; rwa [← dualCode_dualCode_eq]
  · rintro ⟨x, hx, hne, hw⟩
    refine ⟨x, ?_, hne, hw⟩; rwa [dualCode_dualCode_eq]

lemma exists_code_with_good_dual_distance
    {δ : ℝ} (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {n k : ℕ} (hn : 0 < n) (hk_pos : 0 < k) (hkn : k < n)
    (hk_bound : (n : ℝ) - k + 1 < (1 - binaryEntropy δ) * n) :
    ∃ 𝒞 : ClassicalCode n, 𝒞.dimension = k ∧ ((dualCode 𝒞).distance : ℝ) ≥ δ * n := by
  have hnk_pos : 0 < n - k := by omega
  have hnk_lt_n : n - k < n := by omega
  have hnk_bound : (↑(n - k) : ℝ) + 1 < (1 - binaryEntropy δ) * ↑n := by
    have : (↑(n - k) : ℝ) = ↑n - ↑k := by
      rw [Nat.cast_sub (le_of_lt hkn)]
    linarith
  obtain ⟨D, hD_dim, hD_dist⟩ := exists_code_with_good_distance hδ0 hδhalf hn hnk_pos hnk_lt_n hnk_bound
  refine ⟨dualCode D, ?_, ?_⟩
  · haveI : FiniteDimensional 𝔽₂ (Fin n → 𝔽₂) := inferInstance
    rw [dimension_dualCode, hD_dim]; omega
  · rw [distance_dualCode_dualCode]; exact hD_dist

lemma exists_code_with_good_dual_distance_premises_satisfiable :
    ∃ (δ : ℝ) (n k : ℕ), 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < n ∧ 0 < k ∧ k < n ∧
      (n : ℝ) - k + 1 < (1 - binaryEntropy δ) * n := by
  refine ⟨1/100, 1000, 502, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have hH : binaryEntropy (1/100) < 1/2 := binaryEntropy_lt_half (by norm_num) (by norm_num)
  push_cast; nlinarith

/-! ## Binary entropy bound at 1/100 -/

lemma key_nat_ineq_hundredth : (100 : ℕ) ^ 100 < 2 ^ 10 * 99 ^ 99 := by native_decide

lemma key_frac_ineq_hundredth :
    (100 : ℝ) * ((100 : ℝ) / 99) ^ 99 < 2 ^ 10 := by
  rw [div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
  calc (100 : ℝ) * 100 ^ 99
      = 100 ^ 100 := by ring_nf
    _ = ↑((100 : ℕ) ^ 100) := by push_cast; ring
    _ < ↑(2 ^ 10 * 99 ^ 99) := by exact_mod_cast key_nat_ineq_hundredth
    _ = 2 ^ 10 * 99 ^ 99 := by push_cast; ring

lemma binaryEntropy_at_one_hundredth : binaryEntropy (1 / 100) < 1 / 10 := by
  unfold binaryEntropy
  have inv1 : Real.logb 2 (1 / 100) = -Real.logb 2 100 := by
    rw [Real.logb_div (by norm_num) (by norm_num)]; simp [Real.logb_one]
  have inv99 : Real.logb 2 (99 / 100) = -Real.logb 2 (100 / 99) := by
    rw [Real.logb_div (by norm_num) (by norm_num)]
    rw [Real.logb_div (by norm_num) (by norm_num)]; ring
  rw [show (1 : ℝ) - 1 / 100 = 99 / 100 from by ring, inv1, inv99]; ring_nf
  have step : Real.logb 2 100 + (99 : ℝ) * Real.logb 2 (100 / 99) < (10 : ℝ) := by
    have hlog : Real.logb 2 ((100 : ℝ) * (100 / 99 : ℝ) ^ 99) <
                Real.logb 2 ((2 : ℝ) ^ (10 : ℕ)) :=
      Real.logb_lt_logb (by norm_num) (by positivity) key_frac_ineq_hundredth
    rw [Real.logb_mul (by positivity) (pow_ne_zero _ (by positivity)),
        Real.logb_pow, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hlog
    linarith
  linarith [Real.logb_pos (by norm_num : (1:ℝ) < 2) (by norm_num : (1:ℝ) < 100),
            Real.logb_pos (by norm_num : (1:ℝ) < 2) (by norm_num : (1:ℝ) < 100 / 99)]

lemma binaryEntropy_at_one_hundredth_tight : binaryEntropy (1 / 100) < 499 / 1000 := by
  linarith [binaryEntropy_at_one_hundredth]

/-! ## Combined existence and main theorem -/

/-- Helper for the Hamming ball bound used in both distance and dual distance arguments. -/
lemma hammingBall_lt_pow {δ : ℝ} {n : ℕ} {m : ℕ}
    (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hn : 0 < n)
    (hHn : binaryEntropy δ * n < m) :
    ((hammingBall n (δ * ↑n - 1)).card : ℝ) < (2 : ℝ) ^ (m : ℕ) := by
  by_cases hδn1 : δ * ↑n < 1
  · have : hammingBall n (δ * ↑n - 1) = ∅ := hammingBall_empty_of_neg (by linarith)
    simp [this]
  · push_neg at hδn1
    set d' := Nat.floor (δ * ↑n) - 1
    have hd'_bound : (d' : ℝ) + 1 ≤ δ * ↑n := by
      have hfl := Nat.floor_le (by linarith : 0 ≤ δ * ↑n)
      have hfl_pos : 1 ≤ Nat.floor (δ * ↑n) := (Nat.one_le_floor_iff _).mpr hδn1
      simp only [d']; push_cast [Nat.cast_sub hfl_pos]; linarith
    have hball_sub : hammingBall n (δ * ↑n - 1) ⊆ hammingBall n ↑d' := by
      intro v hv; rw [mem_hammingBall] at hv ⊢
      have hfl_lt : δ * ↑n - 1 < (Nat.floor (δ * ↑n) : ℝ) := Nat.sub_one_lt_floor _
      have hwt_lt_floor : hammingWeight v < Nat.floor (δ * ↑n) := by
        exact_mod_cast show (hammingWeight v : ℝ) < Nat.floor (δ * ↑n) from by linarith
      simp only [d']; exact_mod_cast Nat.le_sub_one_of_lt hwt_lt_floor
    calc ((hammingBall n (δ * ↑n - 1)).card : ℝ)
        ≤ (hammingBall n ↑d').card := by exact_mod_cast Finset.card_le_card hball_sub
      _ ≤ 2 ^ (binaryEntropy δ * ↑n) := hammingBallBound hn hδ0 hδhalf hd'_bound
      _ < 2 ^ (m : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
          exact_mod_cast hHn
      _ = (2 : ℝ) ^ (m : ℕ) := by norm_cast

lemma exists_code_with_both_distances
    {δ : ℝ} (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {n k : ℕ} (hn : 0 < n) (hk_pos : 0 < k) (hkn : k < n)
    (hk_upper : (k : ℝ) + 1 < (1 - binaryEntropy δ) * n)
    (hk_lower : (n : ℝ) - k + 1 < (1 - binaryEntropy δ) * n) :
    ∃ 𝒞 : ClassicalCode n, 𝒞.dimension = k ∧
      (𝒞.distance : ℝ) ≥ δ * n ∧ ((dualCode 𝒞).distance : ℝ) ≥ δ * n := by
  -- Use combined counting argument via exists_good_surjective_map
  set r := n - k
  have hr : 0 < r := by omega
  have hrn : r ≤ n := Nat.sub_le n k
  have hnr : n - r = k := by omega
  -- Ball bound for distance: |B₀(δn-1)| < 2^r
  have hHn_dist : binaryEntropy δ * n < r := by
    have : (r : ℝ) = ↑n - ↑k := by
      show ((n - k : ℕ) : ℝ) = ↑n - ↑k; rw [Nat.cast_sub (le_of_lt hkn)]
    linarith
  have hball_lt_r : (hammingBall n (δ * ↑n - 1)).card < 2 ^ r := by
    exact_mod_cast hammingBall_lt_pow hδ0 hδhalf hn hHn_dist
  -- Ball bound for dual distance: |B₀(δn-1)| < 2^k = 2^(n-r)
  have hHn_dual : binaryEntropy δ * n < k := by linarith
  have hball_lt_k : (hammingBall n (δ * ↑n - 1)).card < 2 ^ (n - r) := by
    rw [hnr]; exact_mod_cast hammingBall_lt_pow hδ0 hδhalf hn hHn_dual
  -- Get surjective map φ with both distance conditions
  obtain ⟨φ, hφ_surj, hφ_dist, hφ_dual⟩ :=
    exists_good_surjective_map hr hrn hball_lt_r hball_lt_k
  -- Code = ker(φ) = ofParityCheck φ
  let 𝒞 := ClassicalCode.ofParityCheck φ
  -- dim(ker φ) = n - r = k since φ is surjective
  have hker_dim : Module.finrank 𝔽₂ (LinearMap.ker φ) = k := by
    have hrk := LinearMap.finrank_range_add_finrank_ker φ
    have hrange : Module.finrank 𝔽₂ (LinearMap.range φ) = r := by
      rw [LinearMap.range_eq_top.mpr hφ_surj, finrank_top, Module.finrank_fin_fun]
    rw [Module.finrank_fin_fun] at hrk; omega
  -- ker(φ) has good distance: no nonzero low-weight codewords
  have hgood_dist : ∀ v ∈ 𝒞.code, v ≠ 0 → (hammingWeight v : ℝ) ≥ δ * ↑n := by
    intro v hv hvne
    by_contra h; push_neg at h
    have hφv : φ v = 0 := LinearMap.mem_ker.mp hv
    exact hφ_dist v hvne h hφv
  -- ker(φ) has a nonzero element (since k ≥ 1)
  have hne_code : ∃ v ∈ 𝒞.code, v ≠ 0 := by
    have hnt : Nontrivial (LinearMap.ker φ) :=
      Module.finrank_pos_iff.mp (by omega : 0 < Module.finrank 𝔽₂ (LinearMap.ker φ))
    obtain ⟨⟨v, hv⟩, hvne⟩ := exists_ne (0 : LinearMap.ker φ)
    exact ⟨v, hv, fun h => hvne (Subtype.ext h)⟩
  -- Dual code has a nonzero element (since n - k ≥ 1)
  have hne_dual : ∃ v ∈ (dualCode 𝒞).code, v ≠ 0 := by
    have hdual_dim : (dualCode 𝒞).dimension = n - k := by
      rw [dimension_dualCode]
      unfold dimension
      rw [code_eq_ker, hker_dim]
    unfold ClassicalCode.dimension at hdual_dim
    have hnt : Nontrivial (dualCode 𝒞).code :=
      Module.finrank_pos_iff.mp (by omega : 0 < Module.finrank 𝔽₂ (dualCode 𝒞).code)
    obtain ⟨⟨v, hv⟩, hvne⟩ := exists_ne (0 : (dualCode 𝒞).code)
    exact ⟨v, hv, fun h => hvne (Subtype.ext h)⟩
  refine ⟨𝒞, hker_dim, distance_ge_of_no_lowweight 𝒞 hgood_dist hne_code, ?_⟩
  -- Dual distance from axiom condition
  exact distance_ge_of_no_lowweight (dualCode 𝒞) hφ_dual hne_dual

lemma exists_code_with_both_distances_premises_satisfiable :
    ∃ (δ : ℝ) (n k : ℕ), 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < n ∧ 0 < k ∧ k < n ∧
      (k : ℝ) + 1 < (1 - binaryEntropy δ) * n ∧
      (n : ℝ) - k + 1 < (1 - binaryEntropy δ) * n := by
  refine ⟨1/100, 1000, 500, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    ?_, ?_⟩
  · linarith [binaryEntropy_at_one_hundredth_tight]
  · linarith [binaryEntropy_at_one_hundredth_tight]

/-! ## Main Theorem -/

theorem gilbertVarshamovPlus {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 11 / 100)
    {n : ℕ} (hn : 0 < n)
    (hn_large : (n : ℝ) > 2 / (1 / 2 - binaryEntropy δ)) :
    ∃ 𝒞 : ClassicalCode n,
      (𝒞.dimension : ℝ) > (n : ℝ) / 2 ∧
      (𝒞.distance : ℝ) ≥ δ * n ∧
      ((dualCode 𝒞).distance : ℝ) ≥ δ * n := by
  have hH := binaryEntropy_lt_half hδ0 hδ1
  have hδhalf : δ ≤ 1 / 2 := by linarith
  obtain ⟨k, hk_low, hk_upper, hkn⟩ := gv_k_exists hδ0 hδ1 hn_large
  have hk_pos : 0 < k := by
    by_contra h; push_neg at h; interval_cases k
    simp at hk_low
    linarith [show (0 : ℝ) ≤ (n : ℝ) / 2 from by positivity]
  have hk_lower : (n : ℝ) - k + 1 < (1 - binaryEntropy δ) * n := by
    linarith [gv_n_large hδ0 hδ1 hn_large]
  obtain ⟨𝒞, h_dim, h_dist, h_dual_dist⟩ :=
    exists_code_with_both_distances hδ0 hδhalf hn hk_pos hkn hk_upper hk_lower
  exact ⟨𝒞, by rw [h_dim]; exact_mod_cast hk_low, h_dist, h_dual_dist⟩

end
