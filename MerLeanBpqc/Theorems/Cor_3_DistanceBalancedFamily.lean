import MerLeanBpqc.Theorems.Thm_15_ExplicitFamilyQuantumCodes

/-!
# Corollary 3: Distance-Balanced Family of Quantum Codes

There exists an explicit construction of a family of `[[N, K, D]]` LDPC quantum codes
with `K ∈ Θ(N^{4/5})` and `D ∈ Ω(N^{3/5})`.

## Construction
1. Start with the `[[N₀, K₀, D_{X,0}, D_{Z,0}]]` LDPC subsystem CSS codes from Thm_15
   with `K₀ ∈ Θ(N₀^{2/3})`, `D_{X,0} ∈ Ω(N₀^{1/3})`, `D_{Z,0} ∈ Θ(N₀)`.
2. Choose classical codes of length `n_c ∈ Θ(N₀^{2/3})` via Gilbert–Varshamov (Thm_10)
   with `k_c ∈ Θ(n_c)` and `d_c ∈ Θ(n_c)`.
3. Apply the distance balancing procedure of Evra–Kaufman–Zemor [EKZ, Thm 1],
   producing a CSS code with `N = N₀ · n_c`, `K = K₀ · k_c`, `D_X ≥ D_{X,0} · d_c`,
   `D_Z ≥ D_{Z,0}`.
4. Compute: `N ∈ Θ(N₀^{5/3})`, `K ∈ Θ(N₀^{4/3}) = Θ(N^{4/5})`,
   `D ∈ Ω(N₀) = Ω(N^{3/5})`.

## Main Results
- `ekz_distance_balancing` — axiom for the EKZ distance balancing procedure
- `distanceBalancedFamily` — the main corollary
-/

open CategoryTheory Real ExplicitFamilyQuantumCodes
open scoped TensorProduct DirectSum

noncomputable section

namespace DistanceBalancedFamily

/-! ## Distance-Balanced Parameters

The distance-balanced code length is `N = N₀ · n_c` where `N₀ = codeLength vp`
and `n_c = q²` is the classical code length. -/

/-- The classical code length `n_c = q²`, which is in `Θ(N₀^{2/3})`. -/
def classicalCodeLength (vp : ValidPrime) : ℕ := vp.q ^ 2

/-- The balanced code length `N = N₀ · n_c = codeLength(vp) · q²`. -/
def balancedCodeLength (vp : ValidPrime) : ℕ := codeLength vp * classicalCodeLength vp

/-! ## EKZ Distance Balancing Axiom

The distance balancing procedure of Evra–Kaufman–Zemor [EKZ22] takes a subsystem CSS
code and a classical code, and produces a (non-subsystem) CSS code with balanced
distances. We axiomatize this as a single well-known external theorem. -/

/-- The output of the EKZ distance balancing procedure for a valid prime `q`.
This bundles the CSS code produced by the procedure together with its LDPC property
and the parameter bounds guaranteed by [EKZ22, Theorem 1]. -/
structure BalancedCodeData (vp : ValidPrime) where
  /-- Number of X-type check rows of the balanced code. -/
  rX : ℕ
  /-- Number of Z-type check rows of the balanced code. -/
  rZ : ℕ
  /-- The CSS code produced by the EKZ distance balancing procedure.
  Its block length is `N = N₀ · n_c = codeLength(vp) · q²`. -/
  code : CSSCode (balancedCodeLength vp) rX rZ
  /-- Weight bound for the LDPC property of the balanced code. -/
  w : ℕ
  /-- The X-parity check matrix has bounded weight. -/
  isLDPC_HX : HasBoundedWeight code.HX w
  /-- The Z-parity check matrix has bounded weight. -/
  isLDPC_HZT : HasBoundedWeight code.HZT w
  /-- The number of logical qubits satisfies `K ≥ K₀ · k_c` where
  `K₀` is the subsystem code's logical qubit count and `k_c > n_c/2`
  is the classical code dimension from Gilbert–Varshamov (Thm_10). -/
  hK : code.logicalQubits ≥
    (balanced_product_construction vp).code.logicalQubits * (classicalCodeLength vp / 2 + 1)
  /-- The X-distance satisfies `D_X ≥ D_{X,0} · d_c` where `D_{X,0}` is the
  subsystem code's X-distance and `d_c ≥ δ·n_c` with `δ = 1/10`. -/
  hDX : code.dX ≥
    (balanced_product_construction vp).code.dX * (classicalCodeLength vp / 10)
  /-- Upper bound on K: `K ≤ K₀ · n_c`. Since `K = K₀ · k_c` and `k_c ≤ n_c`,
  this follows from the EKZ construction. -/
  hK_upper : code.logicalQubits ≤
    (balanced_product_construction vp).code.logicalQubits * classicalCodeLength vp
  /-- The Z-distance is preserved: `D_Z ≥ D_{Z,0}`. -/
  hDZ : code.dZ ≥ (balanced_product_construction vp).code.dZ

/-- **Evra–Kaufman–Zemor Distance Balancing** ([EKZ22, Theorem 1];
Evra, Kaufman, Zemor, "Decodable quantum LDPC codes beyond the √n distance barrier
using high-dimensional expanders", FOCS 2022).

Given the subsystem CSS code from Theorem 15 (with parameters
`[[N₀, K₀, D_{X,0}, D_{Z,0}]]`) and a classical `[n_c, k_c, d_c]`-code from
Gilbert–Varshamov (Theorem 10), the EKZ distance balancing procedure produces a
(non-subsystem) CSS code with:
- Block length `N = N₀ · n_c`
- Logical qubits `K ≥ K₀ · k_c`
- X-distance `D_X ≥ D_{X,0} · d_c`
- Z-distance `D_Z ≥ D_{Z,0}`
- LDPC property preserved (weight bounded by a constant). -/
axiom ekz_distance_balancing (vp : ValidPrime) : BalancedCodeData vp

/-- Satisfiability witness: the EKZ axiom's premise (a valid prime) is satisfiable. -/
lemma ekz_satisfiable : ∃ vp : ValidPrime, Nonempty (BalancedCodeData vp) :=
  let ⟨vp, _⟩ := infinitelyManyValidPrimes 0
  ⟨vp, ⟨ekz_distance_balancing vp⟩⟩

/-- The balanced code for a given valid prime. -/
def distanceBalancing (vp : ValidPrime) : BalancedCodeData vp :=
  ekz_distance_balancing vp

/-! ## Arithmetic Helper Lemmas -/

/-- For a valid prime, `q² / 2 + 1 ≥ 1`. -/
lemma classicalK_ge (vp : ValidPrime) :
    classicalCodeLength vp / 2 + 1 ≥ 1 := by omega

/-- For a valid prime (q ≥ 41), `q² / 2 + 1 ≥ q² / 4`. -/
lemma classicalK_lower (vp : ValidPrime) :
    (classicalCodeLength vp / 2 + 1 : ℝ) ≥ (vp.q : ℝ) ^ 2 / 4 := by
  unfold classicalCodeLength
  push_cast
  have : (0 : ℝ) ≤ (vp.q : ℝ) ^ 2 := by positivity
  linarith

/-- For a valid prime (q ≥ 41), `q² / 10 ≥ q² / 20`. -/
lemma classicalD_lower (vp : ValidPrime) :
    (classicalCodeLength vp / 10 : ℝ) ≥ (vp.q : ℝ) ^ 2 / 20 := by
  unfold classicalCodeLength
  push_cast
  have : (0 : ℝ) ≤ (vp.q : ℝ) ^ 2 := by positivity
  linarith

/-! ## N Bounds: N ∈ Θ(q⁵)

The balanced code length `N = codeLength(vp) · q²` satisfies `N ∈ Θ(q⁵)` since
`codeLength(vp) ∈ Θ(q³)`. -/

/-- `balancedCodeLength` expressed in terms of `codeLength` and `classicalCodeLength`. -/
lemma balancedCodeLength_eq (vp : ValidPrime) :
    balancedCodeLength vp = codeLength vp * classicalCodeLength vp := rfl

/-- **N lower bound**: `N = codeLength · q² ≥ c · q⁵` for a constant `c > 0`. -/
lemma balancedN_lower :
    ∃ (c : ℝ), 0 < c ∧
      ∀ vp : ValidPrime,
        c * (vp.q : ℝ) ^ 5 ≤ ((balancedCodeLength vp) : ℝ) := by
  refine ⟨3 * 201 / 2, by positivity, fun vp => ?_⟩
  simp only [balancedCodeLength, classicalCodeLength]
  have hq := validPrime_q_ge vp
  have hq_pos : (0 : ℝ) < (vp.q : ℝ) := by positivity
  have hN : (↑(codeLength vp * vp.q ^ 2) : ℝ) =
      (codeLength vp : ℝ) * (vp.q : ℝ) ^ 2 := by push_cast; ring
  rw [hN]
  have hcl := codeLength_eq_real vp
  rw [hcl]
  have hq_ge : (vp.q : ℝ) ≥ 41 := by exact_mod_cast hq
  have hq2 : (vp.q : ℝ) ^ 2 ≥ 41 ^ 2 := by nlinarith
  have hq2_sub : (vp.q : ℝ) ^ 2 - 1 ≥ (vp.q : ℝ) ^ 2 / 2 := by nlinarith
  nlinarith [mul_pos (by positivity : (0:ℝ) < 3 * 201) (mul_pos hq_pos (by nlinarith : (0:ℝ) < (vp.q : ℝ) ^ 2 - 1))]

/-- **N upper bound**: `N = codeLength · q² ≤ C · q⁵` for a constant `C > 0`. -/
lemma balancedN_upper :
    ∃ (C : ℝ), 0 < C ∧
      ∀ vp : ValidPrime,
        ((balancedCodeLength vp) : ℝ) ≤ C * (vp.q : ℝ) ^ 5 := by
  refine ⟨3 * 201, by positivity, fun vp => ?_⟩
  simp only [balancedCodeLength, classicalCodeLength]
  have hq := validPrime_q_ge vp
  have hN : (↑(codeLength vp * vp.q ^ 2) : ℝ) =
      (codeLength vp : ℝ) * (vp.q : ℝ) ^ 2 := by push_cast; ring
  rw [hN]
  have hcl := codeLength_eq_real vp
  rw [hcl]
  have hq_pos : (0 : ℝ) < (vp.q : ℝ) := by positivity
  have hsub : (vp.q : ℝ) ^ 2 - 1 ≤ (vp.q : ℝ) ^ 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hsub (by positivity : (0 : ℝ) ≤ 3 * 201 * (vp.q : ℝ) * (vp.q : ℝ) ^ 2)]

/-! ## K Bounds: K ∈ Θ(q⁴)

The logical qubit count `K` of the balanced code satisfies `K ∈ Θ(q⁴)`.
The lower bound uses `K ≥ K₀ · k_c` from the EKZ axiom, combined with
`K₀ ∈ Θ(q²)` from Thm_15 and `k_c ∈ Θ(q²)` from GV. -/

/-- **K lower bound**: `K ≥ c · q⁴` for a constant `c > 0`. -/
lemma balancedK_lower :
    ∃ (c : ℝ), 0 < c ∧
      ∀ vp : ValidPrime,
        c * (vp.q : ℝ) ^ 4 ≤ ((distanceBalancing vp).code.logicalQubits : ℝ) := by
  obtain ⟨c₀, hc₀, hc₀b⟩ := lps_K_lower_bound
  refine ⟨c₀ / 8, by positivity, fun vp => ?_⟩
  have hq := validPrime_q_ge vp
  have hq_pos : (0 : ℝ) < (vp.q : ℝ) := by positivity
  -- K ≥ K₀ · (n_c/2 + 1) from EKZ axiom
  have hEKZ := (distanceBalancing vp).hK
  -- K₀ ≥ c₀ · (q² - 1) from Thm_15
  have hK₀ := hc₀b vp
  -- n_c/2 + 1 ≥ q²/4
  have hn_c_cast : (↑(classicalCodeLength vp / 2 + 1) : ℝ) ≥ (vp.q : ℝ) ^ 2 / 4 := by
    have hcl : classicalCodeLength vp = vp.q ^ 2 := rfl
    have hstrong : 4 * (classicalCodeLength vp / 2 + 1) ≥ vp.q ^ 2 := by
      unfold classicalCodeLength; omega
    have : (4 : ℝ) * ↑(classicalCodeLength vp / 2 + 1) ≥ (vp.q : ℝ) ^ 2 := by
      exact_mod_cast hstrong
    linarith
  have hK₀_nn : (0 : ℝ) ≤ ↑(balanced_product_construction vp).code.logicalQubits :=
    Nat.cast_nonneg _
  have hK₀_cast : (↑(balanced_product_construction vp).code.logicalQubits : ℝ) ≥
      c₀ * ((vp.q : ℝ) ^ 2 - 1) := by linarith
  -- K₀ * (n_c/2+1) ≥ c₀(q²-1) * q²/4 ≥ c₀/8 * q⁴
  have hmul : (↑((balanced_product_construction vp).code.logicalQubits *
      (classicalCodeLength vp / 2 + 1)) : ℝ) ≥
      c₀ * ((vp.q : ℝ) ^ 2 - 1) * ((vp.q : ℝ) ^ 2 / 4) := by
    push_cast at hn_c_cast ⊢
    exact mul_le_mul (by linarith) (by linarith) (by positivity) hK₀_nn
  have hq2 : (vp.q : ℝ) ^ 2 - 1 ≥ (vp.q : ℝ) ^ 2 / 2 := by
    have : (vp.q : ℝ) ^ 2 ≥ 41 ^ 2 := by nlinarith [show (vp.q : ℝ) ≥ 41 from by exact_mod_cast hq]
    nlinarith
  have hfinal : c₀ * ((vp.q : ℝ) ^ 2 - 1) * ((vp.q : ℝ) ^ 2 / 4) ≥
      c₀ / 8 * (vp.q : ℝ) ^ 4 := by
    have : c₀ * ((vp.q : ℝ) ^ 2 - 1) * ((vp.q : ℝ) ^ 2 / 4) ≥
        c₀ * ((vp.q : ℝ) ^ 2 / 2) * ((vp.q : ℝ) ^ 2 / 4) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left hq2 (le_of_lt hc₀)
    have : c₀ * ((vp.q : ℝ) ^ 2 / 2) * ((vp.q : ℝ) ^ 2 / 4) = c₀ / 8 * (vp.q : ℝ) ^ 4 := by ring
    linarith
  -- Chain: K ≥ K₀ * (n_c/2+1) ≥ c₀(q²-1)(q²/4) ≥ c₀/8 * q⁴
  calc c₀ / 8 * (vp.q : ℝ) ^ 4
      ≤ (↑((balanced_product_construction vp).code.logicalQubits *
          (classicalCodeLength vp / 2 + 1)) : ℝ) := by linarith
    _ ≤ ((distanceBalancing vp).code.logicalQubits : ℝ) := by exact_mod_cast hEKZ

/-- **K upper bound**: `K ≤ C · q⁴` for a constant `C > 0`.
Uses `hK_upper`: `K ≤ K₀ · n_c` from the EKZ axiom, combined with
`K₀ ≤ C₀(q²-1)` from Thm_15 and `n_c = q²`. -/
lemma balancedK_upper :
    ∃ (C : ℝ), 0 < C ∧
      ∀ vp : ValidPrime,
        ((distanceBalancing vp).code.logicalQubits : ℝ) ≤ C * (vp.q : ℝ) ^ 4 := by
  obtain ⟨C₀, hC₀, hC₀b⟩ := lps_K_upper_bound
  refine ⟨C₀, hC₀, fun vp => ?_⟩
  have hq := validPrime_q_ge vp
  -- K ≤ K₀ · n_c from EKZ hK_upper
  have hEKZ := (distanceBalancing vp).hK_upper
  -- K₀ ≤ C₀ · (q² - 1) from Thm_15
  have hK₀ := hC₀b vp
  -- n_c = q²
  have hn_c : classicalCodeLength vp = vp.q ^ 2 := rfl
  -- n_c ≤ q²
  have hn_c_nat : classicalCodeLength vp ≤ vp.q ^ 2 := le_refl _
  have hn_c_cast : (↑(classicalCodeLength vp) : ℝ) ≤ (vp.q : ℝ) ^ 2 := by exact_mod_cast hn_c_nat
  have hK₀_nn : (0 : ℝ) ≤ ↑(balanced_product_construction vp).code.logicalQubits :=
    Nat.cast_nonneg _
  have hn_c_nn : (0 : ℝ) ≤ (↑(classicalCodeLength vp) : ℝ) := Nat.cast_nonneg _
  -- K ≤ K₀ * n_c ≤ C₀(q²-1) * q² ≤ C₀ * q⁴
  have hmul : (↑((balanced_product_construction vp).code.logicalQubits *
      classicalCodeLength vp) : ℝ) ≤ C₀ * ((vp.q : ℝ) ^ 2 - 1) * (vp.q : ℝ) ^ 2 := by
    push_cast
    exact mul_le_mul (by linarith) (by exact_mod_cast hn_c_nat) (by positivity) (by nlinarith)
  have hfinal : C₀ * ((vp.q : ℝ) ^ 2 - 1) * (vp.q : ℝ) ^ 2 ≤ C₀ * (vp.q : ℝ) ^ 4 := by
    nlinarith
  calc ((distanceBalancing vp).code.logicalQubits : ℝ)
      ≤ (↑((balanced_product_construction vp).code.logicalQubits *
          classicalCodeLength vp) : ℝ) := by exact_mod_cast hEKZ
    _ ≤ C₀ * ((vp.q : ℝ) ^ 2 - 1) * (vp.q : ℝ) ^ 2 := hmul
    _ ≤ C₀ * (vp.q : ℝ) ^ 4 := hfinal

/-! ## Distance Bounds: D_X, D_Z ∈ Ω(q³) -/

/-- **D_X lower bound**: `DX ≥ c · q³` for a constant `c > 0`. -/
lemma balancedDX_lower :
    ∃ (c : ℝ), 0 < c ∧
      ∀ vp : ValidPrime,
        c * (vp.q : ℝ) ^ 3 ≤ ((distanceBalancing vp).code.dX : ℝ) := by
  obtain ⟨c₀, hc₀, hc₀b⟩ := lps_DX_lower_bound
  refine ⟨c₀ / 20, by positivity, fun vp => ?_⟩
  have hq := validPrime_q_ge vp
  have hq_pos : (0 : ℝ) < (vp.q : ℝ) := by positivity
  -- DX ≥ dX₀ * (n_c / 10) from EKZ hDX
  have hEKZ := (distanceBalancing vp).hDX
  -- dX₀ ≥ c₀ * q from Thm_15
  have hDX₀ := hc₀b vp
  -- n_c / 10 ≥ q²/20
  have hn_c_nat : (↑(classicalCodeLength vp / 10) : ℝ) ≥ (vp.q : ℝ) ^ 2 / 20 := by
    unfold classicalCodeLength
    have hq2 : vp.q ^ 2 ≥ 41 ^ 2 := by nlinarith
    have h_nat : vp.q ^ 2 ≤ vp.q ^ 2 / 10 * 20 := by omega
    have h_cast := (Nat.cast_le (α := ℝ)).mpr h_nat
    push_cast [Nat.cast_mul, Nat.cast_pow] at h_cast ⊢
    linarith
  -- dX₀ * (n_c/10) ≥ c₀*q * q²/20 = c₀/20 * q³
  have hDX : (↑(balanced_product_construction vp).code.dX *
      ↑(classicalCodeLength vp / 10) : ℝ) ≥
      c₀ * (vp.q : ℝ) * ((vp.q : ℝ) ^ 2 / 20) := by
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hprod : c₀ * (vp.q : ℝ) * ((vp.q : ℝ) ^ 2 / 20) = c₀ / 20 * (vp.q : ℝ) ^ 3 := by ring
  calc c₀ / 20 * (vp.q : ℝ) ^ 3
      ≤ (↑(balanced_product_construction vp).code.dX *
          ↑(classicalCodeLength vp / 10) : ℝ) := by linarith [hprod]
    _ ≤ (↑((balanced_product_construction vp).code.dX *
          (classicalCodeLength vp / 10)) : ℝ) := by push_cast; linarith
    _ ≤ ((distanceBalancing vp).code.dX : ℝ) := by exact_mod_cast hEKZ

/-- **D_Z lower bound**: `DZ ≥ c · q³` for a constant `c > 0`. -/
lemma balancedDZ_lower :
    ∃ (c : ℝ), 0 < c ∧
      ∀ vp : ValidPrime,
        c * (vp.q : ℝ) ^ 3 ≤ ((distanceBalancing vp).code.dZ : ℝ) := by
  obtain ⟨c₀, hc₀, hc₀b⟩ := lps_DZ_lower_bound
  refine ⟨c₀ / 2, by positivity, fun vp => ?_⟩
  have hq := validPrime_q_ge vp
  have hq_pos : (0 : ℝ) < (vp.q : ℝ) := by positivity
  -- DZ ≥ dZ₀ from EKZ hDZ
  have hEKZ := (distanceBalancing vp).hDZ
  -- dZ₀ ≥ c₀ * q(q²-1) from Thm_15
  have hDZ := hc₀b vp
  -- q(q²-1) ≥ q³/2
  have hq2 : (vp.q : ℝ) ^ 2 - 1 ≥ (vp.q : ℝ) ^ 2 / 2 := by
    have : (vp.q : ℝ) ^ 2 ≥ 41 ^ 2 := by
      nlinarith [show (vp.q : ℝ) ≥ 41 from by exact_mod_cast hq]
    nlinarith
  have hprod : (vp.q : ℝ) * ((vp.q : ℝ) ^ 2 - 1) ≥ (vp.q : ℝ) ^ 3 / 2 := by
    have : (vp.q : ℝ) * ((vp.q : ℝ) ^ 2 / 2) = (vp.q : ℝ) ^ 3 / 2 := by ring
    nlinarith [mul_le_mul_of_nonneg_left hq2 (le_of_lt hq_pos)]
  have hchain : c₀ * ((vp.q : ℝ) * ((vp.q : ℝ) ^ 2 - 1)) ≥ c₀ / 2 * (vp.q : ℝ) ^ 3 := by
    nlinarith
  -- DZ ≥ dZ₀ ≥ c₀ * q(q²-1) ≥ c₀/2 * q³
  calc c₀ / 2 * (vp.q : ℝ) ^ 3
      ≤ (↑(balanced_product_construction vp).code.dZ : ℝ) := by linarith
    _ ≤ ((distanceBalancing vp).code.dZ : ℝ) := by exact_mod_cast hEKZ

/-! ## N Unbounded -/

/-- The family is infinite: for any `M`, there exists a valid prime with
the balanced code length exceeding `M`. -/
lemma balancedN_unbounded : ∀ M : ℕ, ∃ vp : ValidPrime,
    balancedCodeLength vp > M := by
  intro M
  obtain ⟨c, hc, hcbound⟩ := balancedN_lower
  obtain ⟨vp, hvp⟩ := infinitelyManyValidPrimes (Nat.ceil ((M + 1 : ℝ) / c) + 1)
  refine ⟨vp, ?_⟩
  have hq := validPrime_q_ge vp
  have hq_pos : (0 : ℝ) < (vp.q : ℝ) := by positivity
  have hcN := hcbound vp
  suffices h : (M : ℝ) < ((balancedCodeLength vp) : ℝ) by exact_mod_cast h
  calc (M : ℝ) < c * (vp.q : ℝ) ^ 5 := by
        have hvp_real : (vp.q : ℝ) > (↑(Nat.ceil ((↑M + 1 : ℝ) / c)) : ℝ) + 1 := by
          exact_mod_cast hvp
        have hceil : (↑(Nat.ceil ((↑M + 1 : ℝ) / c)) : ℝ) ≥ (↑M + 1) / c := by
          exact Nat.le_ceil _
        have hq_bound : (vp.q : ℝ) > (↑M + 1) / c := by linarith
        have : c * (vp.q : ℝ) > ↑M + 1 := by
          have := (div_lt_iff₀ hc).mp hq_bound
          linarith [mul_comm (vp.q : ℝ) c]
        have : c * (vp.q : ℝ) ^ 5 ≥ c * (vp.q : ℝ) := by
          have : (vp.q : ℝ) ^ 5 ≥ (vp.q : ℝ) ^ 1 := by
            exact pow_le_pow_right₀ (by linarith : 1 ≤ (vp.q : ℝ)) (by omega : 1 ≤ 5)
          have : (vp.q : ℝ) ^ 5 ≥ (vp.q : ℝ) := by linarith [show (vp.q : ℝ) ^ 1 = vp.q from pow_one _]
          nlinarith
        linarith
    _ ≤ ((balancedCodeLength vp) : ℝ) := hcN

/-! ## Main Theorem -/

/-- **Corollary 3: Distance-Balanced Family of Quantum Codes.**

There exists an explicit construction of a family of `[[N, K, D]]` LDPC quantum codes
(Def_5) with `K ∈ Θ(N^{4/5})` and `D = min(D_X, D_Z) ∈ Ω(N^{3/5})`.

The proof combines Theorem 15 (explicit family with unbalanced distances) with the
distance balancing procedure of Evra–Kaufman–Zemor [EKZ22, Theorem 1].

The balanced code for each valid prime `vp` is `(distanceBalancing vp).code`, a CSS
code of length `N = balancedCodeLength vp`. Since `N ∈ Θ(q⁵)`, we have
`q ∈ Θ(N^{1/5})`, giving `K ∈ Θ(q⁴) = Θ(N^{4/5})` and
`D ∈ Ω(q³) = Ω(N^{3/5})`. -/
theorem distanceBalancedFamily :
    -- Part 1: For each valid prime, there is an LDPC CSS code with balanced parameters
    (∀ vp : ValidPrime,
      ∃ (rX rZ : ℕ) (code : CSSCode (balancedCodeLength vp) rX rZ) (w : ℕ),
        HasBoundedWeight code.HX w ∧
        HasBoundedWeight code.HZT w) ∧
    -- Part 2: The family is infinite (arbitrarily large balanced code length)
    (∀ M : ℕ, ∃ vp : ValidPrime, balancedCodeLength vp > M) ∧
    -- Part 3: K ∈ Θ(q⁴), so K ∈ Θ(N^{4/5})
    (∃ (c C : ℝ), 0 < c ∧ 0 < C ∧
      ∀ vp : ValidPrime,
        c * (vp.q : ℝ) ^ 4 ≤ ((distanceBalancing vp).code.logicalQubits : ℝ) ∧
        ((distanceBalancing vp).code.logicalQubits : ℝ) ≤ C * (vp.q : ℝ) ^ 4) ∧
    -- Part 4: D = min(D_X, D_Z) ∈ Ω(q³), so D ∈ Ω(N^{3/5})
    (∃ (c : ℝ), 0 < c ∧
      ∀ vp : ValidPrime,
        c * (vp.q : ℝ) ^ 3 ≤ min ((distanceBalancing vp).code.dX : ℝ)
                                    ((distanceBalancing vp).code.dZ : ℝ)) ∧
    -- Part 5: N ∈ Θ(q⁵), establishing the N-to-q conversion
    (∃ (c C : ℝ), 0 < c ∧ 0 < C ∧
      ∀ vp : ValidPrime,
        c * (vp.q : ℝ) ^ 5 ≤ ((balancedCodeLength vp) : ℝ) ∧
        ((balancedCodeLength vp) : ℝ) ≤ C * (vp.q : ℝ) ^ 5) := by
  refine ⟨?_, balancedN_unbounded, ?_, ?_, ?_⟩
  -- Part 1: LDPC CSS code exists (from the EKZ balanced code)
  · intro vp
    let D := distanceBalancing vp
    exact ⟨D.rX, D.rZ, D.code, D.w, D.isLDPC_HX, D.isLDPC_HZT⟩
  -- Part 3: K ∈ Θ(q⁴)
  · obtain ⟨c, hc, hcb⟩ := balancedK_lower
    obtain ⟨C, hC, hCb⟩ := balancedK_upper
    exact ⟨c, C, hc, hC, fun vp => ⟨hcb vp, hCb vp⟩⟩
  -- Part 4: D = min(D_X, D_Z) ∈ Ω(q³)
  · obtain ⟨c₁, hc₁, hc₁b⟩ := balancedDX_lower
    obtain ⟨c₂, hc₂, hc₂b⟩ := balancedDZ_lower
    refine ⟨min c₁ c₂, lt_min hc₁ hc₂, fun vp => ?_⟩
    have hDX := hc₁b vp
    have hDZ := hc₂b vp
    have hq_pos : (0 : ℝ) < (vp.q : ℝ) := by
      have := validPrime_q_ge vp; exact_mod_cast Nat.lt_of_lt_pred (by omega)
    simp only [le_min_iff]
    constructor
    · calc min c₁ c₂ * (vp.q : ℝ) ^ 3
          ≤ c₁ * (vp.q : ℝ) ^ 3 := by
            apply mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ ≤ ((distanceBalancing vp).code.dX : ℝ) := hDX
    · calc min c₁ c₂ * (vp.q : ℝ) ^ 3
          ≤ c₂ * (vp.q : ℝ) ^ 3 := by
            apply mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ ≤ ((distanceBalancing vp).code.dZ : ℝ) := hDZ
  -- Part 5: N ∈ Θ(q⁵)
  · obtain ⟨c, hc, hcb⟩ := balancedN_lower
    obtain ⟨C, hC, hCb⟩ := balancedN_upper
    exact ⟨c, C, hc, hC, fun vp => ⟨hcb vp, hCb vp⟩⟩

end DistanceBalancedFamily

end
