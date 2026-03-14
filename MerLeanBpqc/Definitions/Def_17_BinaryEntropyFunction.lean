import MerLeanBpqc.Remarks.Rem_1_BaseField
import MerLeanBpqc.Remarks.Rem_3_ExpandingMatrixDefinition
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Definition 17: Binary Entropy Function

The binary entropy function `H₂ : ℝ → ℝ` defined by
`H₂(δ) = -δ log₂(δ) - (1 - δ) log₂(1 - δ)`.

## Main Results
- `binaryEntropy`: the binary entropy function
- `binaryEntropy_lt_half`: `H₂(δ) < 1/2` for `δ ∈ (0, 11/100)`
- `hammingBall`: the Hamming ball of radius `r`
- `hammingBallBound`: `|B₀(⌊δn - 1⌋)| ≤ 2^{H₂(δ) · n}`
-/

open Real Finset BigOperators

noncomputable section

/-! ## Binary Entropy Function -/

/-- The binary entropy function `H₂ : ℝ → ℝ` defined by
`H₂(δ) = -δ log₂(δ) - (1 - δ) log₂(1 - δ)`.
For `δ ∈ (0, 1)`, this gives the Shannon entropy of a Bernoulli(δ) distribution
measured in bits. Outside `(0, 1)`, the function extends by continuity
(with `log₂(0) = 0` in Mathlib's convention). -/
def binaryEntropy (δ : ℝ) : ℝ := -δ * Real.logb 2 δ - (1 - δ) * Real.logb 2 (1 - δ)

/-! ## Key numerical inequality: H₂(11/100) < 1/2

The proof strategy converts the entropy inequality to a product inequality
via exponentiation, then verifies the resulting natural number inequality.
-/

/-- The key Nat inequality: `100^100 < 2^50 * 11^11 * 89^89`.
This is the exponential form of `H₂(11/100) < 1/2`. -/
lemma key_nat_ineq : (100 : ℕ) ^ 100 < 2 ^ 50 * 11 ^ 11 * 89 ^ 89 := by native_decide

/-- `(100/11)^11 * (100/89)^89 < 2^50` in ℝ. -/
lemma key_frac_ineq : ((100 : ℝ) / 11) ^ 11 * ((100 : ℝ) / 89) ^ 89 < 2 ^ 50 := by
  rw [div_pow, div_pow, div_mul_div_comm, div_lt_iff₀ (by positivity)]
  calc (100 : ℝ) ^ 11 * 100 ^ 89
      = 100 ^ 100 := by ring_nf
    _ = ↑((100 : ℕ) ^ 100) := by push_cast; ring
    _ < ↑(2 ^ 50 * 11 ^ 11 * 89 ^ 89) := by exact_mod_cast key_nat_ineq
    _ = 2 ^ 50 * (11 ^ 11 * 89 ^ 89) := by push_cast; ring

/-- `H₂(11/100) < 1/2`: the binary entropy function at `11/100` is less than `1/2`.
The proof converts to the product form using `logb`, then applies `key_frac_ineq`. -/
lemma binaryEntropy_at_eleven_hundredths : binaryEntropy (11 / 100) < 1 / 2 := by
  unfold binaryEntropy
  -- We need: -11/100 * logb 2 (11/100) - 89/100 * logb 2 (89/100) < 1/2
  -- Equivalently: 11/100 * logb 2 (100/11) + 89/100 * logb 2 (100/89) < 1/2
  -- Equivalently: logb 2 ((100/11)^(11/100) * (100/89)^(89/100)) < 1/2
  -- Equivalently: (100/11)^(11/100) * (100/89)^(89/100) < 2^(1/2)
  -- We use a stronger: (100/11)^11 * (100/89)^89 < 2^50
  have h11 : (11 : ℝ) / 100 > 0 := by norm_num
  have h89 : (89 : ℝ) / 100 > 0 := by norm_num
  have hlog11 : Real.logb 2 (11 / 100) < 0 := by
    apply Real.logb_neg (by norm_num : (1 : ℝ) < 2) (by linarith) (by norm_num)
  have hlog89 : Real.logb 2 (89 / 100) < 0 := by
    apply Real.logb_neg (by norm_num : (1 : ℝ) < 2) (by linarith) (by norm_num)
  -- Rewrite using logb(a/b) = logb a - logb b
  have inv11 : Real.logb 2 (11 / 100) = -Real.logb 2 (100 / 11) := by
    rw [Real.logb_div (by norm_num : (11 : ℝ) ≠ 0) (by norm_num : (100 : ℝ) ≠ 0)]
    rw [Real.logb_div (by norm_num : (100 : ℝ) ≠ 0) (by norm_num : (11 : ℝ) ≠ 0)]
    ring
  have inv89 : Real.logb 2 (89 / 100) = -Real.logb 2 (100 / 89) := by
    rw [Real.logb_div (by norm_num : (89 : ℝ) ≠ 0) (by norm_num : (100 : ℝ) ≠ 0)]
    rw [Real.logb_div (by norm_num : (100 : ℝ) ≠ 0) (by norm_num : (89 : ℝ) ≠ 0)]
    ring
  -- Now the LHS becomes 11/100 * logb 2 (100/11) + 89/100 * logb 2 (100/89)
  have simp1 : (1 : ℝ) - 11 / 100 = 89 / 100 := by ring
  rw [simp1, inv11, inv89]
  -- Goal: -(11/100) * -(logb 2 (100/11)) - 89/100 * -(logb 2 (100/89)) < 1/2
  ring_nf
  -- Goal should be: 11/100 * logb 2 (100/11) + 89/100 * logb 2 (100/89) < 1/2
  -- Use: a * logb b x = logb b (x^a) when x > 0
  -- So 11/100 * logb 2 (100/11) + 89/100 * logb 2 (100/89)
  --  = logb 2 ((100/11)^(11/100)) + logb 2 ((100/89)^(89/100))
  --  = logb 2 ((100/11)^(11/100) * (100/89)^(89/100))
  -- And we need this < 1/2 = logb 2 (2^(1/2)) = logb 2 (sqrt 2)
  -- Equivalently: (100/11)^(11/100) * (100/89)^(89/100) < sqrt 2
  -- From key_frac_ineq: (100/11)^11 * (100/89)^89 < 2^50
  -- Taking 1/100-th power: ((100/11)^11 * (100/89)^89)^(1/100) < (2^50)^(1/100) = 2^(1/2)
  -- After ring_nf, goal is of the form: a * logb 2 (100/11) + b * logb 2 (100/89) < 1/2
  -- where a = 11/100, b = 89/100 (up to ring_nf reordering).
  -- From key_frac_ineq: (100/11)^11 * (100/89)^89 < 2^50, take logb 2:
  have h100_11_pos : (0 : ℝ) < 100 / 11 := by positivity
  have h100_89_pos : (0 : ℝ) < 100 / 89 := by positivity
  have step : ↑(11 : ℕ) * Real.logb 2 (100 / 11) + ↑(89 : ℕ) * Real.logb 2 (100 / 89) < (50 : ℝ) := by
    have hlog : Real.logb 2 ((100 / 11 : ℝ) ^ 11 * (100 / 89 : ℝ) ^ 89) <
                Real.logb 2 ((2 : ℝ) ^ (50 : ℕ)) :=
      Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) key_frac_ineq
    rw [Real.logb_mul (pow_ne_zero _ (ne_of_gt h100_11_pos)) (pow_ne_zero _ (ne_of_gt h100_89_pos)),
        Real.logb_pow, Real.logb_pow, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hlog
    linarith
  have hlog_pos11 : 0 < Real.logb 2 (100 / 11) :=
    Real.logb_pos (by norm_num) (by norm_num : (1 : ℝ) < 100 / 11)
  have hlog_pos89 : 0 < Real.logb 2 (100 / 89) :=
    Real.logb_pos (by norm_num) (by norm_num : (1 : ℝ) < 100 / 89)
  -- Now the casted Nat 11 and 89 equal the reals 11 and 89
  push_cast at step
  linarith

/-! ## Derivative and monotonicity of binary entropy -/

/-- `binaryEntropy` equals Mathlib's `binEntropy` divided by `log 2`. -/
lemma binaryEntropy_eq_binEntropy_div (δ : ℝ) :
    binaryEntropy δ = Real.binEntropy δ / Real.log 2 := by
  simp only [binaryEntropy, Real.binEntropy, Real.logb, Real.log_inv]
  ring

lemma hasDerivAt_binaryEntropy {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt binaryEntropy (Real.logb 2 ((1 - x) / x)) x := by
  have hx_ne : x ≠ 0 := ne_of_gt hx0
  have hx1_ne : x ≠ 1 := ne_of_lt hx1
  have h1mx_ne : (1 - x : ℝ) ≠ 0 := by linarith
  rw [show binaryEntropy = fun δ => Real.binEntropy δ / Real.log 2 from
    funext binaryEntropy_eq_binEntropy_div]
  have hderiv := (Real.hasDerivAt_binEntropy hx_ne hx1_ne).div_const (Real.log 2)
  convert hderiv using 1
  rw [Real.logb, Real.log_div h1mx_ne hx_ne]

/-- `H₂` is strictly increasing on `(0, 1/2)`: for `0 < a < b < 1/2`, `H₂(a) < H₂(b)`.
This follows from `H₂'(x) = logb 2 ((1-x)/x) > 0` for `x < 1/2`. -/
lemma binaryEntropy_strictMonoOn : StrictMonoOn binaryEntropy (Set.Ioo 0 (1/2)) := by
  intro a ha b hb hab
  rw [binaryEntropy_eq_binEntropy_div, binaryEntropy_eq_binEntropy_div]
  apply div_lt_div_of_pos_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have ha' : a ∈ Set.Icc 0 2⁻¹ := by
    constructor <;> simp_all [Set.mem_Ioo] <;> linarith
  have hb' : b ∈ Set.Icc 0 2⁻¹ := by
    constructor <;> simp_all [Set.mem_Ioo] <;> linarith
  exact Real.binEntropy_strictMonoOn ha' hb' hab

/-- `H₂(δ) < 1/2` for `δ ∈ (0, 11/100)`. Since `H₂` is strictly increasing on `(0, 1/2)`
and `11/100 < 1/2`, we have `H₂(δ) < H₂(11/100) < 1/2` for `δ < 11/100`. -/
theorem binaryEntropy_lt_half {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 11 / 100) :
    binaryEntropy δ < 1 / 2 := by
  have hδhalf : δ < 1 / 2 := by linarith
  have h11half : (11 : ℝ) / 100 < 1 / 2 := by norm_num
  have h11pos : (0 : ℝ) < 11 / 100 := by norm_num
  have hδ_mem : δ ∈ Set.Ioo 0 (1/2) := ⟨hδ0, hδhalf⟩
  have h11_mem : (11 : ℝ) / 100 ∈ Set.Ioo 0 (1/2) := ⟨h11pos, h11half⟩
  calc binaryEntropy δ
      < binaryEntropy (11 / 100) := binaryEntropy_strictMonoOn hδ_mem h11_mem hδ1
    _ < 1 / 2 := binaryEntropy_at_eleven_hundredths

/-! ## Hamming Ball -/

/-- The Hamming ball of radius `r` centered at the origin in `𝔽₂^n`:
`B₀(r) = {v ∈ 𝔽₂^n : wt(v) ≤ r}`, where `wt` is the Hamming weight.
This is defined as a `Finset` of vectors. When `r < 0`, the ball is empty. -/
def hammingBall (n : ℕ) (r : ℝ) : Finset (Fin n → 𝔽₂) :=
  Finset.univ.filter (fun v => (hammingWeight v : ℝ) ≤ r)

/-- Membership in the Hamming ball: `v ∈ B₀(r)` iff `wt(v) ≤ r`. -/
theorem mem_hammingBall {n : ℕ} {r : ℝ} {v : Fin n → 𝔽₂} :
    v ∈ hammingBall n r ↔ (hammingWeight v : ℝ) ≤ r := by
  simp [hammingBall]

/-- The Hamming ball is empty when `r < 0`. -/
lemma hammingBall_empty_of_neg {n : ℕ} {r : ℝ} (hr : r < 0) :
    hammingBall n r = ∅ := by
  ext v
  constructor
  · intro hv
    simp [hammingBall] at hv
    linarith [show (0 : ℝ) ≤ (hammingWeight v : ℝ) from Nat.cast_nonneg _]
  · intro hv; exact absurd hv (Finset.notMem_empty _)

/-- The Hamming ball is non-empty when `r ≥ 0`: the zero vector has weight 0. -/
lemma hammingBall_nonempty {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    (hammingBall n r).Nonempty := by
  use 0
  rw [mem_hammingBall]
  simp [hammingWeight, hammingNorm, hammingDist_self]
  exact hr

/-! ## Hamming Ball Bound helpers -/

/-- Helper: for `0 < δ ≤ 1/2` and `a ≤ k ≤ n`, we have
`δ^a · (1-δ)^(n-a) ≥ δ^k · (1-δ)^(n-k)`. This is because `δ ≤ 1-δ`,
so replacing `a` by `k` (moving weight from `1-δ` to `δ` exponent) decreases the product. -/
lemma bernoulli_weight_mono {n : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/2)
    {a k : ℕ} (hak : a ≤ k) (hkn : k ≤ n) :
    δ ^ k * (1 - δ) ^ (n - k) ≤ δ ^ a * (1 - δ) ^ (n - a) := by
  have h1mδ_pos : 0 < 1 - δ := by linarith
  have hδ_le_1mδ : δ ≤ 1 - δ := by linarith
  have hka : k = a + (k - a) := (Nat.add_sub_cancel' hak).symm
  have hna : n - a = (k - a) + (n - k) := by omega
  rw [hka, pow_add, hna, pow_add]
  have hsimp : n - (a + (k - a)) = n - k := by omega
  rw [hsimp]
  calc δ ^ a * δ ^ (k - a) * (1 - δ) ^ (n - k)
      = δ ^ a * ((1 - δ) ^ (n - k) * δ ^ (k - a)) := by ring
    _ ≤ δ ^ a * ((1 - δ) ^ (n - k) * (1 - δ) ^ (k - a)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_pos hδ0 _).le
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ0.le hδ_le_1mδ _) (pow_pos h1mδ_pos _).le
    _ = δ ^ a * ((1 - δ) ^ (k - a) * (1 - δ) ^ (n - k)) := by ring

/-- The total Bernoulli weight over all vectors equals 1:
`∑_{v : Fin n → 𝔽₂} δ^(wt v) · (1-δ)^(n - wt v) = 1`.
This is a consequence of the binomial theorem `(δ + (1-δ))^n = 1^n = 1`. -/
lemma bernoulli_weight_sum {n : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/2) :
    ∑ v : Fin n → 𝔽₂, δ ^ (hammingWeight v) * (1 - δ) ^ (n - hammingWeight v) = 1 := by
  -- Equivalence between (Fin n → 𝔽₂) and Finset (Fin n) via support
  have zmod2_cases : ∀ x : 𝔽₂, x = 0 ∨ x = 1 := by decide
  let e : (Fin n → 𝔽₂) ≃ Finset (Fin n) :=
  { toFun := fun v => Finset.univ.filter (fun i => v i ≠ 0)
    invFun := fun s => fun i => if i ∈ s then 1 else 0
    left_inv := by
      intro v; ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases zmod2_cases (v i) with
      | inl h => simp [h]
      | inr h => simp [h]
    right_inv := by
      intro s; ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : i ∈ s <;> simp [h] }
  -- (e v).card = hammingWeight v by definition
  have hcard : ∀ v, (e v).card = hammingWeight v := fun v => rfl
  -- Use binomial theorem: ∑ s, δ^s.card * (1-δ)^(n-s.card) = (δ+(1-δ))^n = 1
  have key := Fin.sum_pow_mul_eq_add_pow (n := n) δ (1 - δ)
  rw [add_sub_cancel, one_pow] at key
  have sum_eq : ∑ v : Fin n → 𝔽₂, δ ^ (hammingWeight v) * (1 - δ) ^ (n - hammingWeight v) =
      ∑ s : Finset (Fin n), δ ^ s.card * (1 - δ) ^ (n - s.card) := by
    rw [← Equiv.sum_comp e]
    congr 1
  rw [sum_eq, key]

/-! ## Hamming Ball Bound -/

/-- The Hamming ball bound: for positive `n` and `δ ∈ (0, 1/2]`,
the number of binary vectors of length `n` with Hamming weight at most `k`
satisfies `|B₀(k)| ≤ 2^{H₂(δ) · n}` whenever `k + 1 ≤ δ · n`.
The proof shows `|B₀(k)| · δ^k · (1-δ)^{n-k} ≤ 1` by summing Bernoulli weights,
then converts to the entropy form. -/
-- Helper: the logb inequality for the entropy bound
private lemma entropy_logb_ineq {n : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    {k : ℕ} (hkn : k ≤ n) (hk : (k : ℝ) + 1 ≤ δ * ↑n) :
    -(↑k * Real.logb 2 δ + ↑(n - k) * Real.logb 2 (1 - δ)) ≤ binaryEntropy δ * ↑n := by
  unfold binaryEntropy
  have hδn_gt_k : δ * ↑n - ↑k > 0 := by linarith
  have hlog_le : Real.logb 2 δ ≤ Real.logb 2 (1 - δ) := by
    apply (Real.strictMonoOn_logb (by norm_num : (1 : ℝ) < 2)).monotoneOn
      (Set.mem_Ioi.mpr hδ0) (Set.mem_Ioi.mpr (by linarith)) (by linarith)
  -- The difference is (δn - k) * (logb 2 (1-δ) - logb 2 δ) ≥ 0
  rw [Nat.cast_sub hkn]
  nlinarith [mul_nonneg (le_of_lt hδn_gt_k) (sub_nonneg.mpr hlog_le)]

theorem hammingBallBound {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    {k : ℕ} (hk : k + 1 ≤ δ * n) :
    ((hammingBall n (↑k : ℝ)).card : ℝ) ≤ 2 ^ (binaryEntropy δ * n) := by
  have h1mδ : 0 < 1 - δ := by linarith
  have hkn : k ≤ n := by
    by_contra h; push_neg at h
    have : δ * ↑n < ↑n := by nlinarith [hδ1]
    linarith [show (↑k : ℝ) ≥ ↑n from by exact_mod_cast h.le]
  have hprod_pos : 0 < δ ^ k * (1 - δ) ^ (n - k) := by positivity
  -- Step 1: |B₀(k)| * δ^k * (1-δ)^(n-k) ≤ 1
  have step1 : ↑(hammingBall n ↑k).card * (δ ^ k * (1 - δ) ^ (n - k)) ≤ 1 := by
    calc ↑(hammingBall n ↑k).card * (δ ^ k * (1 - δ) ^ (n - k))
        = ∑ _v ∈ hammingBall n ↑k, δ ^ k * (1 - δ) ^ (n - k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ hammingBall n ↑k,
            δ ^ (hammingWeight v) * (1 - δ) ^ (n - hammingWeight v) := by
          apply Finset.sum_le_sum; intro v hv
          rw [mem_hammingBall] at hv
          exact bernoulli_weight_mono hδ0 hδ1 (by exact_mod_cast hv) hkn
      _ ≤ ∑ v, δ ^ (hammingWeight v) * (1 - δ) ^ (n - hammingWeight v) :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
      _ = 1 := bernoulli_weight_sum hδ0 hδ1
  -- Step 2: (δ^k * (1-δ)^(n-k))⁻¹ ≤ 2^(H₂(δ)*n)
  have step2 : (δ ^ k * (1 - δ) ^ (n - k))⁻¹ ≤ 2 ^ (binaryEntropy δ * ↑n) := by
    rw [← Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (inv_pos.mpr hprod_pos)]
    rw [Real.logb_inv, Real.logb_mul (ne_of_gt (pow_pos hδ0 _))
        (ne_of_gt (pow_pos h1mδ _)), Real.logb_pow, Real.logb_pow]
    exact entropy_logb_ineq hδ0 hδ1 hkn hk
  -- Combine: |B₀(k)| ≤ (δ^k * (1-δ)^(n-k))⁻¹ ≤ 2^(H₂(δ)*n)
  have hcard_le : (↑(hammingBall n ↑k).card : ℝ) ≤ (δ ^ k * (1 - δ) ^ (n - k))⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hprod_pos).mpr step1
  linarith [step2]

end
