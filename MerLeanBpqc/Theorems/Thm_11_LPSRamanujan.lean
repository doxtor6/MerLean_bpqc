import MerLeanBpqc.Definitions.Def_21_LPSExpanderGraphs
import MerLeanBpqc.Definitions.Def_14_GraphExpansion
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Theorem 11: LPS Graphs are Ramanujan

## Main Results
- `pgl2_card_ge_six`: PGL(2, q) has at least 6 elements for odd prime q ≥ 5.
- `psl2_card_ge_six`: PSL(2, q) has at least 6 elements for odd prime q ≥ 5.
- `lpsGraphPGL_card_ge_two`: The LPS graph on PGL has at least 2 vertices.
- `lpsGraphPSL_card_ge_two`: The LPS graph on PSL has at least 2 vertices.
- `lpsGraphPGL_lambda2_le`: Under Ramanujan + spectral hypotheses, λ₂ ≤ 2√p.
- `lpsGraphPSL_lambda2_le`: Under Ramanujan + spectral hypotheses, λ₂ ≤ 2√p.

The connectedness and Ramanujan properties of LPS graphs follow from deep results
in algebraic number theory (the Ramanujan–Petersson conjecture, proved via the Weil
conjectures by Deligne). These are taken as hypotheses in the main theorems, since
the required algebraic geometry is not available in Mathlib.
-/

open SimpleGraph Fintype GraphExpansion LPS CayleyGraph Matrix

noncomputable section

namespace LPSRamanujan

/-! ## Cardinality bounds: PGL and PSL have at least 6 elements -/

/-- A 2×2 matrix over a nontrivial commutative ring whose (0,1) entry is nonzero
cannot be a scalar matrix. -/
private lemma not_scalar_of_entry_01_ne {R : Type*} [CommRing R] [Nontrivial R]
    (M : Matrix (Fin 2) (Fin 2) R) (h : M 0 1 ≠ 0) :
    M ∉ Set.range (Matrix.scalar (Fin 2) : R → _) := by
  rintro ⟨a, ha⟩
  have := congr_fun (congr_fun ha 0) 1
  simp [Matrix.scalar, Matrix.diagonal] at this
  exact h this.symm

/-- Upper unipotent matrix [[1,a],[0,1]] has nonzero determinant. -/
private lemma det_unipotent_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    (a : R) : (!![(1 : R), a; 0, 1]).det ≠ 0 := by
  simp [det_fin_two]

/-- Swap matrix [[0,1],[-1,0]] has nonzero determinant. -/
private lemma det_swap_ne_zero {R : Type*} [CommRing R] [Nontrivial R] :
    (!![(0 : R), 1; -1, 0]).det ≠ 0 := by
  simp [det_fin_two]

/-- Upper unipotent GL element. -/
private def unipGL (q : ℕ) [Fact (Nat.Prime q)] (a : ZMod q) : GL (Fin 2) (ZMod q) :=
  matToGL q !![(1 : ZMod q), a; 0, 1] (det_unipotent_ne_zero a)

/-- Swap GL element. -/
private def swapGL (q : ℕ) [Fact (Nat.Prime q)] : GL (Fin 2) (ZMod q) :=
  matToGL q !![(0 : ZMod q), 1; -1, 0] det_swap_ne_zero

/-- Helper: commuting with E₁₂ = [[1,1],[0,1]] implies M(1,0) = 0. -/
private lemma comm_e12_entry10 {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (h : !![1, 1; (0 : R), 1] * M = M * !![1, 1; (0 : R), 1]) :
    M 1 0 = 0 := by
  have := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this

/-- Helper: commuting with E₁₂ implies M(0,0) = M(1,1). -/
private lemma comm_e12_diag {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (h : !![1, 1; (0 : R), 1] * M = M * !![1, 1; (0 : R), 1]) :
    M 0 0 = M 1 1 := by
  have := congr_fun (congr_fun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this; linear_combination -this

/-- Helper: commuting with E₂₁ = [[1,0],[1,1]] implies M(0,1) = 0. -/
private lemma comm_e21_entry01 {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (h : !![1, (0 : R); 1, 1] * M = M * !![1, (0 : R); 1, 1]) :
    M 0 1 = 0 := by
  have := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this

/-- The underlying matrix of `unipGL`. -/
@[simp] private lemma unipGL_val (q : ℕ) [Fact (Nat.Prime q)] (a : ZMod q) :
    (unipGL q a).val = !![(1 : ZMod q), a; 0, 1] := rfl

/-- The underlying matrix of `swapGL`. -/
@[simp] private lemma swapGL_val (q : ℕ) [Fact (Nat.Prime q)] :
    (swapGL q).val = !![(0 : ZMod q), 1; -1, 0] := rfl

/-- If two upper unipotent GL elements map to the same PGL2 coset, they are equal. -/
private lemma unipotent_pgl_injective (q : ℕ) [Fact (Nat.Prime q)]
    (a b : ZMod q)
    (h : projPGL q (unipGL q a) = projPGL q (unipGL q b)) : a = b := by
  rw [projPGL, QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨z, hz_mem, hz_eq⟩ := h
  -- hz_eq : (unipGL q a) * z = (unipGL q b)
  -- z ∈ center of GL, so z commutes with everything
  rw [Subgroup.mem_center_iff] at hz_mem
  -- Multiply out: (unipGL q a).val * z.val = (unipGL q b).val
  have hmul : (unipGL q a).val * z.val = (unipGL q b).val := by
    have := congr_arg Units.val hz_eq
    simpa [Units.val_mul] using this
  -- z commutes with E₁₂ in GL
  have e12_gl : (unipGL q 1) * z = z * (unipGL q 1) := by
    have := hz_mem (unipGL q 1)
    exact this
  have hcomm : (!![(1 : ZMod q), 1; 0, 1]) * z.val = z.val * !![(1 : ZMod q), 1; 0, 1] := by
    have := congr_arg Units.val e12_gl
    simpa [Units.val_mul, unipGL_val] using this
  have hz10 : z.val 1 0 = 0 := comm_e12_entry10 z.val hcomm
  have hz_diag : z.val 0 0 = z.val 1 1 := comm_e12_diag z.val hcomm
  -- Commute with E₂₁
  have e21_det : (!![(1 : ZMod q), (0 : ZMod q); 1, 1]).det ≠ 0 := by simp [det_fin_two]
  set e21_gl := matToGL q !![(1 : ZMod q), (0 : ZMod q); 1, 1] e21_det
  have e21_comm : e21_gl * z = z * e21_gl := by
    have := hz_mem e21_gl; exact this
  have hcomm21 : !![(1 : ZMod q), (0 : ZMod q); 1, 1] * z.val = z.val * !![(1 : ZMod q), (0 : ZMod q); 1, 1] := by
    have := congr_arg Units.val e21_comm
    simp [Units.val_mul] at this
    rw [matToGL_val] at this
    exact this
  have hz01 : z.val 0 1 = 0 := comm_e21_entry01 z.val hcomm21
  -- Now extract from hmul
  -- Rewrite hmul using the actual matrix values
  have hmul' : !![(1 : ZMod q), a; 0, 1] * z.val = !![(1 : ZMod q), b; 0, 1] := by
    rw [← unipGL_val, ← unipGL_val]; exact hmul
  have h00 := congr_fun (congr_fun hmul' 0) 0
  have h01_entry := congr_fun (congr_fun hmul' 0) 1
  simp [mul_apply, Fin.sum_univ_two] at h00 h01_entry
  -- h00 : ↑z 0 0 + a * ↑z 1 0 = 1
  -- h01_entry : ↑z 0 1 + a * ↑z 1 1 = b
  rw [hz10, mul_zero, add_zero] at h00
  rw [hz01, zero_add] at h01_entry
  -- h00 : ↑z 0 0 = 1, h01_entry : a * ↑z 1 1 = b
  rw [← hz_diag, h00, mul_one] at h01_entry
  exact h01_entry

/-- The swap GL element is not in the same PGL2 coset as any upper unipotent. -/
private lemma swap_ne_unipotent_pgl (q : ℕ) [Fact (Nat.Prime q)]
    (a : ZMod q) :
    projPGL q (swapGL q) ≠ projPGL q (unipGL q a) := by
  intro h
  rw [projPGL, QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨z, hz_mem, hz_eq⟩ := h
  rw [Subgroup.mem_center_iff] at hz_mem
  have hmul : (swapGL q).val * z.val = (unipGL q a).val := by
    have := congr_arg Units.val hz_eq
    simpa [Units.val_mul] using this
  -- z commutes with E₁₂
  have e12_comm : (unipGL q 1) * z = z * (unipGL q 1) := hz_mem (unipGL q 1)
  have hcomm : (!![(1 : ZMod q), 1; 0, 1]) * z.val = z.val * !![(1 : ZMod q), 1; 0, 1] := by
    have := congr_arg Units.val e12_comm
    simpa [Units.val_mul, unipGL_val] using this
  have hz10 : z.val 1 0 = 0 := comm_e12_entry10 z.val hcomm
  have hz_diag : z.val 0 0 = z.val 1 1 := comm_e12_diag z.val hcomm
  -- Commute with E₂₁
  have e21_det : (!![(1 : ZMod q), (0 : ZMod q); 1, 1]).det ≠ 0 := by simp [det_fin_two]
  set e21_gl := matToGL q !![(1 : ZMod q), (0 : ZMod q); 1, 1] e21_det
  have e21_comm : e21_gl * z = z * e21_gl := hz_mem e21_gl
  have hcomm21 : !![(1 : ZMod q), (0 : ZMod q); 1, 1] * z.val = z.val * !![(1 : ZMod q), (0 : ZMod q); 1, 1] := by
    have := congr_arg Units.val e21_comm
    simp [Units.val_mul] at this
    rw [matToGL_val] at this
    exact this
  have hz01 : z.val 0 1 = 0 := comm_e21_entry01 z.val hcomm21
  -- Now from hmul: [[0,1],[-1,0]] * z.val = [[1,a],[0,1]]
  have hmul' : !![(0 : ZMod q), 1; -1, 0] * z.val = !![(1 : ZMod q), a; 0, 1] := by
    rw [← swapGL_val, ← unipGL_val]; exact hmul
  have h10 := congr_fun (congr_fun hmul' 1) 0
  have h11 := congr_fun (congr_fun hmul' 1) 1
  simp [mul_apply, Fin.sum_univ_two] at h10 h11
  simp [hz10, hz01] at h10 h11

/-- The PGL(2, q) group has at least 6 elements when q ≥ 5. -/
theorem pgl2_card_ge_six (q : ℕ) [Fact (Nat.Prime q)] (_hoddq : q % 2 = 1)
    (hq_ge : q ≥ 5) :
    6 ≤ Fintype.card (PGL2 q) := by
  -- Construct injection from ZMod q ⊕ Unit → PGL2 q
  -- ZMod q has q elements, Unit has 1, total q + 1 ≥ 6
  have hinj : Function.Injective (fun x : ZMod q ⊕ Unit =>
    match x with
    | Sum.inl a => projPGL q (unipGL q a)
    | Sum.inr () => projPGL q (swapGL q)) := by
    intro x y hxy
    match x, y with
    | Sum.inl a, Sum.inl b => exact congr_arg _ (unipotent_pgl_injective q a b hxy)
    | Sum.inl a, Sum.inr () => exact absurd hxy.symm (swap_ne_unipotent_pgl q a)
    | Sum.inr (), Sum.inl b => exact absurd hxy (swap_ne_unipotent_pgl q b)
    | Sum.inr (), Sum.inr () => rfl
  have hcard_le := Fintype.card_le_of_injective _ hinj
  simp [Fintype.card_sum, ZMod.card] at hcard_le
  omega

/-- Upper unipotent SL element. -/
private def unipSL (q : ℕ) [Fact (Nat.Prime q)] (a : ZMod q) :
    SpecialLinearGroup (Fin 2) (ZMod q) :=
  ⟨!![(1 : ZMod q), a; 0, 1], by simp [det_fin_two]⟩

/-- E₁₂ SL element [[1,1],[0,1]]. -/
private def e12SL (q : ℕ) [Fact (Nat.Prime q)] :
    SpecialLinearGroup (Fin 2) (ZMod q) :=
  ⟨!![(1 : ZMod q), 1; 0, 1], by simp [det_fin_two]⟩

/-- E₂₁ SL element [[1,0],[1,1]]. -/
private def e21SL (q : ℕ) [Fact (Nat.Prime q)] :
    SpecialLinearGroup (Fin 2) (ZMod q) :=
  ⟨!![(1 : ZMod q), (0 : ZMod q); 1, 1], by simp [det_fin_two]⟩

@[simp] private lemma e12SL_val (q : ℕ) [Fact (Nat.Prime q)] :
    (e12SL q).1 = !![(1 : ZMod q), 1; 0, 1] := rfl

@[simp] private lemma e21SL_val (q : ℕ) [Fact (Nat.Prime q)] :
    (e21SL q).1 = !![(1 : ZMod q), (0 : ZMod q); 1, 1] := rfl

/-- Swap SL element. -/
private def swapSL (q : ℕ) [Fact (Nat.Prime q)] :
    SpecialLinearGroup (Fin 2) (ZMod q) :=
  ⟨!![(0 : ZMod q), 1; -1, 0], by simp [det_fin_two]⟩

/-- If two upper unipotent SL elements map to the same PSL2 coset, they are equal. -/
private lemma unipotent_psl_injective (q : ℕ) [Fact (Nat.Prime q)]
    (a b : ZMod q)
    (h : projPSL q (unipSL q a) = projPSL q (unipSL q b)) : a = b := by
  rw [projPSL, QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨z, hz_mem, hz_eq⟩ := h
  rw [Subgroup.mem_center_iff] at hz_mem
  -- hz_eq : (unipSL q a) * z = (unipSL q b)
  -- hz_mem : ∀ g, g * z = z * g
  have hmul : (unipSL q a).1 * z.1 = (unipSL q b).1 := by
    have := congr_arg Subtype.val hz_eq
    simpa [SpecialLinearGroup.coe_mul] using this
  -- z commutes with E₁₂ in SL:
  have e12_comm : e12SL q * z = z * e12SL q := hz_mem (e12SL q)
  have hcomm : (!![(1 : ZMod q), 1; 0, 1]) * z.1 = z.1 * !![(1 : ZMod q), 1; 0, 1] := by
    have := congr_arg Subtype.val e12_comm
    simpa [SpecialLinearGroup.coe_mul, e12SL_val] using this
  have hz10 : z.1 1 0 = 0 := comm_e12_entry10 z.1 hcomm
  have hz_diag : z.1 0 0 = z.1 1 1 := comm_e12_diag z.1 hcomm
  -- Similarly commute with E₂₁ to get z.1 0 1 = 0
  have e21_comm : e21SL q * z = z * e21SL q := hz_mem (e21SL q)
  have hcomm21 : !![(1 : ZMod q), (0 : ZMod q); 1, 1] * z.1 = z.1 * !![(1 : ZMod q), (0 : ZMod q); 1, 1] := by
    have := congr_arg Subtype.val e21_comm
    simpa [SpecialLinearGroup.coe_mul, e21SL_val] using this
  have hz01 : z.1 0 1 = 0 := comm_e21_entry01 z.1 hcomm21
  -- Now z.1 is diagonal with z.1 0 0 = z.1 1 1
  -- From hmul: [[1,a],[0,1]] * z.1 = [[1,b],[0,1]]
  have h00 := congr_fun (congr_fun hmul 0) 0
  have h01_entry := congr_fun (congr_fun hmul 0) 1
  simp [mul_apply, Fin.sum_univ_two, unipSL] at h00 h01_entry
  rw [hz10, mul_zero, add_zero] at h00
  rw [hz01, zero_add] at h01_entry
  -- h00 : ↑z 0 0 = 1, h01_entry : a * ↑z 1 1 = b
  rw [← hz_diag, h00, mul_one] at h01_entry
  exact h01_entry

/-- The swap SL element is not in the same PSL2 coset as any upper unipotent. -/
private lemma swap_ne_unipotent_psl (q : ℕ) [Fact (Nat.Prime q)]
    (a : ZMod q) :
    projPSL q (swapSL q) ≠ projPSL q (unipSL q a) := by
  intro h
  rw [projPSL, QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨z, hz_mem, hz_eq⟩ := h
  rw [Subgroup.mem_center_iff] at hz_mem
  -- hz_eq : (swapSL q) * z = (unipSL q a)
  have hmul : (swapSL q).1 * z.1 = (unipSL q a).1 := by
    have := congr_arg Subtype.val hz_eq
    simpa [SpecialLinearGroup.coe_mul] using this
  -- z commutes with E₁₂, so z is diagonal
  have e12_comm : e12SL q * z = z * e12SL q := hz_mem (e12SL q)
  have hcomm : (!![(1 : ZMod q), 1; 0, 1]) * z.1 = z.1 * !![(1 : ZMod q), 1; 0, 1] := by
    have := congr_arg Subtype.val e12_comm
    simpa [SpecialLinearGroup.coe_mul, e12SL_val] using this
  have hz10 : z.1 1 0 = 0 := comm_e12_entry10 z.1 hcomm
  have hz_diag : z.1 0 0 = z.1 1 1 := comm_e12_diag z.1 hcomm
  -- E₂₁ commutation
  have e21_comm : e21SL q * z = z * e21SL q := hz_mem (e21SL q)
  have hcomm21 : !![(1 : ZMod q), (0 : ZMod q); 1, 1] * z.1 = z.1 * !![(1 : ZMod q), (0 : ZMod q); 1, 1] := by
    have := congr_arg Subtype.val e21_comm
    simpa [SpecialLinearGroup.coe_mul, e21SL_val] using this
  have hz01 : z.1 0 1 = 0 := comm_e21_entry01 z.1 hcomm21
  -- Now from hmul: [[0,1],[-1,0]] * z.1 = [[1,a],[0,1]]
  have h10 := congr_fun (congr_fun hmul 1) 0
  have h11 := congr_fun (congr_fun hmul 1) 1
  simp [mul_apply, Fin.sum_univ_two, swapSL, unipSL] at h10 h11
  -- h10 : ↑z 0 0 = 0, h11 : -↑z 0 1 = 1
  rw [hz01] at h11
  simp at h11

/-- The PSL(2, q) group has at least 6 elements when q ≥ 5. -/
theorem psl2_card_ge_six (q : ℕ) [Fact (Nat.Prime q)] (_hoddq : q % 2 = 1)
    (hq_ge : q ≥ 5) :
    6 ≤ Fintype.card (PSL2 q) := by
  have hinj : Function.Injective (fun x : ZMod q ⊕ Unit =>
    match x with
    | Sum.inl a => projPSL q (unipSL q a)
    | Sum.inr () => projPSL q (swapSL q)) := by
    intro x y hxy
    match x, y with
    | Sum.inl a, Sum.inl b => exact congr_arg _ (unipotent_psl_injective q a b hxy)
    | Sum.inl a, Sum.inr () => exact absurd hxy.symm (swap_ne_unipotent_psl q a)
    | Sum.inr (), Sum.inl b => exact absurd hxy (swap_ne_unipotent_psl q b)
    | Sum.inr (), Sum.inr () => rfl
  have hcard_le := Fintype.card_le_of_injective _ hinj
  simp [Fintype.card_sum, ZMod.card] at hcard_le
  omega

/-- An odd prime q with q > 2√p for odd prime p ≥ 3 satisfies q ≥ 5. -/
lemma q_ge_five (q : ℕ) (p : ℕ) [Fact (Nat.Prime p)]
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1) [Fact (Nat.Prime q)]
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p) : q ≥ 5 := by
  by_contra h
  push_neg at h
  have hq_le : q ≤ 4 := by omega
  -- q is an odd prime ≤ 4, so q = 3
  have hq_prime := (Fact.out : Nat.Prime q)
  have hp_prime := (Fact.out : Nat.Prime p)
  -- p is an odd prime, so p ≥ 3
  have hp_ge : p ≥ 3 := by
    have : p ≥ 2 := hp_prime.two_le
    omega
  -- 2√p ≥ 2√3 > 3.4 > 3
  have : (q : ℝ) ≤ 4 := by exact_mod_cast hq_le
  have : (2 : ℝ) * Real.sqrt 3 ≤ 2 * Real.sqrt p := by
    apply mul_le_mul_of_nonneg_left
    · exact Real.sqrt_le_sqrt (by exact_mod_cast hp_ge)
    · linarith
  -- We have q > 2√p ≥ 2√3 > 3. So q ≥ 4.
  -- But also (q : ℝ) ≤ 4 and (2 : ℝ) * √3 ≤ (2 : ℝ) * √p < q ≤ 4
  -- So (2√3)² < q² ≤ 16, i.e., 12 < 16, which is fine.
  -- But we also need q > 2√p. Since p ≥ 3, 2√p ≥ 2√3 > 3.4.
  -- So q > 3.4, meaning q ≥ 4. But q is odd, so q ≥ 5. Contradiction with q ≤ 4.
  -- To formalize: q > 2√p and p ≥ 3 means q² > 4p ≥ 12.
  -- q ≤ 4 means q² ≤ 16. q is odd and prime and ≤ 4 means q ∈ {2,3}.
  -- q odd means q = 3. Then q² = 9 > 4p ≥ 12. But 9 < 12. Contradiction.
  -- Actually q > 2√p means q ≥ 4 (since 2√3 > 3.46), and q odd means q ≥ 5.
  have hq_ge2 := hq_prime.two_le
  -- q is odd and ≥ 2 and ≤ 4. q odd means q ∈ {3}. (2 is even, 4 is even)
  have hq3 : q = 3 := by omega
  subst hq3
  -- Now hq_gt : (3 : ℝ) > 2 * Real.sqrt p, and hp_ge : p ≥ 3
  -- So 9 > 4 * p ≥ 12, contradiction.
  -- hq_gt : (3 : ℝ) > 2 * √p, so 9 > (2√p)² = 4p ≥ 12. Contradiction.
  have hp_cast : (p : ℝ) ≥ 3 := by exact_mod_cast hp_ge
  have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg p
  -- From hq_gt : (3 : ℝ) > 2 * √p and hp_cast : (p : ℝ) ≥ 3
  -- We get 9 > 4p ≥ 12, contradiction
  have hsq : Real.sqrt p * Real.sqrt p = (p : ℝ) :=
    Real.mul_self_sqrt (by exact_mod_cast (Nat.zero_le p) : (0 : ℝ) ≤ (p : ℝ))
  have hq_gt' : (3 : ℝ) > 2 * Real.sqrt p := by exact_mod_cast hq_gt
  -- 3 > 2√p and 2√p ≥ 0, so (2√p)² < 9, i.e. 4p < 9, but 4p ≥ 12
  nlinarith [mul_self_nonneg (2 * Real.sqrt p - 3)]

/-- The LPS graph on PGL has at least 2 vertices. -/
theorem lpsGraphPGL_card_ge_two (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p) :
    2 ≤ Fintype.card (PGL2 q) := by
  have := pgl2_card_ge_six q hoddq (q_ge_five q p hoddp hoddq hq_gt)
  omega

/-- The LPS graph on PSL has at least 2 vertices. -/
theorem lpsGraphPSL_card_ge_two (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p) :
    2 ≤ Fintype.card (PSL2 q) := by
  have := psl2_card_ge_six q hoddq (q_ge_five q p hoddp hoddq hq_gt)
  omega

/-! ## Connectedness, Ramanujan property, and spectral bounds

The following deep results are taken as hypotheses in downstream theorems:
- **Connectedness** of LPS graphs follows from the fact that S_{p,q} generates PGL/PSL.
- **Ramanujan property** follows from the Ramanujan–Petersson conjecture for GL(2)/ℚ,
  proved by Eichler–Igusa (weight 2) building on the Weil conjectures (Deligne, 1974).
- **Spectral bound** |λ₂| < s for connected s-regular graphs follows from the
  Perron–Frobenius theorem for non-negative matrices.

These results require algebraic geometry and spectral theory not available in Mathlib.
They appear as explicit hypotheses `hconn`, `hram`, and `hspec` in the theorems below. -/

/-! ## Corollary: λ₂ ≤ 2√p -/

/-- The second-largest eigenvalue of the LPS graph on PGL satisfies `λ₂ ≤ 2√p`.
The Ramanujan property and the spectral bound `|λ₂| < s` for connected regular graphs
are deep results taken as hypotheses. -/
theorem lpsGraphPGL_lambda2_le (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (hram : IsRamanujan (lpsGraphPGL q p hpq hoddp hoddq hq_gt x y hxy) (p + 1)
      (lpsGraphPGL_card_ge_two q p hpq hoddp hoddq hq_gt))
    (hspec : |secondLargestEigenvalue (lpsGraphPGL q p hpq hoddp hoddq hq_gt x y hxy)
      (lpsGraphPGL_card_ge_two q p hpq hoddp hoddq hq_gt)| < (p + 1 : ℝ)) :
    secondLargestEigenvalue (lpsGraphPGL q p hpq hoddp hoddq hq_gt x y hxy)
      (lpsGraphPGL_card_ge_two q p hpq hoddp hoddq hq_gt) ≤ 2 * Real.sqrt p := by
  unfold IsRamanujan at hram
  unfold secondLargestEigenvalue at hspec ⊢
  set hcard := lpsGraphPGL_card_ge_two q p hpq hoddp hoddq hq_gt
  set idx : Fin (Fintype.card (PGL2 q)) := ⟨1, by omega⟩
  have h1 := hram idx
  rw [Nat.cast_add, Nat.cast_one] at h1
  have hle := h1 hspec
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hle
  exact le_trans (le_abs_self _) hle

/-- The second-largest eigenvalue of the LPS graph on PSL satisfies `λ₂ ≤ 2√p`.
The Ramanujan property and the spectral bound are taken as hypotheses. -/
theorem lpsGraphPSL_lambda2_le (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (hleg : legendreSym q (p : ℤ) = 1)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (hram : IsRamanujan (lpsGraphPSL q p hpq hoddp hoddq hq_gt hleg x y hxy) (p + 1)
      (lpsGraphPSL_card_ge_two q p hpq hoddp hoddq hq_gt))
    (hspec : |secondLargestEigenvalue (lpsGraphPSL q p hpq hoddp hoddq hq_gt hleg x y hxy)
      (lpsGraphPSL_card_ge_two q p hpq hoddp hoddq hq_gt)| < (p + 1 : ℝ)) :
    secondLargestEigenvalue (lpsGraphPSL q p hpq hoddp hoddq hq_gt hleg x y hxy)
      (lpsGraphPSL_card_ge_two q p hpq hoddp hoddq hq_gt) ≤ 2 * Real.sqrt p := by
  unfold IsRamanujan at hram
  unfold secondLargestEigenvalue at hspec ⊢
  set hcard := lpsGraphPSL_card_ge_two q p hpq hoddp hoddq hq_gt
  set idx : Fin (Fintype.card (PSL2 q)) := ⟨1, by omega⟩
  have h1 := hram idx
  rw [Nat.cast_add, Nat.cast_one] at h1
  have hle := h1 hspec
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hle
  exact le_trans (le_abs_self _) hle

/-! ## Combined result -/

/-- **LPS Ramanujan Theorem (PGL, combined).**
The LPS graph `X_{p,q}` on PGL(2,q) is (p+1)-regular and has ≥ 2 vertices (proved).
Under the hypotheses that the graph is connected and Ramanujan (deep results from
Lubotzky–Phillips–Sarnak requiring algebraic geometry not in Mathlib), the full
combined result holds. -/
theorem lpsRamanujan_PGL (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (hconn : (lpsGraphPGL q p hpq hoddp hoddq hq_gt x y hxy).Connected)
    (hram : IsRamanujan (lpsGraphPGL q p hpq hoddp hoddq hq_gt x y hxy) (p + 1)
      (lpsGraphPGL_card_ge_two q p hpq hoddp hoddq hq_gt)) :
    let G := lpsGraphPGL q p hpq hoddp hoddq hq_gt x y hxy
    G.Connected ∧
    G.IsRegularOfDegree (p + 1) ∧
    2 ≤ Fintype.card (PGL2 q) ∧
    IsRamanujan G (p + 1) (lpsGraphPGL_card_ge_two q p hpq hoddp hoddq hq_gt) := by
  exact ⟨hconn,
    lpsGraphPGL_isRegularOfDegree q p hpq hoddp hoddq hq_gt x y hxy,
    lpsGraphPGL_card_ge_two q p hpq hoddp hoddq hq_gt,
    hram⟩

/-- **LPS Ramanujan Theorem (PSL, combined).**
The LPS graph `X_{p,q}` on PSL(2,q) is (p+1)-regular and has ≥ 2 vertices (proved).
Under the hypotheses that the graph is connected and Ramanujan (deep results),
the full combined result holds. -/
theorem lpsRamanujan_PSL (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (hleg : legendreSym q (p : ℤ) = 1)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (hconn : (lpsGraphPSL q p hpq hoddp hoddq hq_gt hleg x y hxy).Connected)
    (hram : IsRamanujan (lpsGraphPSL q p hpq hoddp hoddq hq_gt hleg x y hxy) (p + 1)
      (lpsGraphPSL_card_ge_two q p hpq hoddp hoddq hq_gt)) :
    let G := lpsGraphPSL q p hpq hoddp hoddq hq_gt hleg x y hxy
    G.Connected ∧
    G.IsRegularOfDegree (p + 1) ∧
    2 ≤ Fintype.card (PSL2 q) ∧
    IsRamanujan G (p + 1) (lpsGraphPSL_card_ge_two q p hpq hoddp hoddq hq_gt) := by
  exact ⟨hconn,
    lpsGraphPSL_isRegularOfDegree q p hpq hoddp hoddq hq_gt hleg x y hxy,
    lpsGraphPSL_card_ge_two q p hpq hoddp hoddq hq_gt,
    hram⟩

end LPSRamanujan

end
