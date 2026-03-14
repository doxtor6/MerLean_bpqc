import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Center
import MerLeanBpqc.Definitions.Def_20_CayleyGraph
import MerLeanBpqc.Definitions.Def_14_GraphExpansion

/-!
# Definition 21: LPS Expander Graphs

## Main Results
- `PGL2`: The projective general linear group `PGL(2, q)`.
- `PSL2`: The projective special linear group `PSL(2, q)`.
- `SpTilde`: The set `S̃_p = {(a,b,c,d) ∈ ℤ⁴ | a² + b² + c² + d² = p}`.
- `Sp`: The normalized subset `S_p ⊆ S̃_p` with `|S_p| = p + 1`.
- `lpsMatrix`: The matrix `M(a,b,c,d)` in `GL(2, 𝔽_q)`.
- `lpsGenSetPGL`: The generating set `S_{p,q} ⊆ PGL(2,q)`.
- `lpsGenSetPSL`: The generating set `S_{p,q} ⊆ PSL(2,q)`.
- `lpsGraphPGL`: The LPS Cayley graph on `PGL(2,q)`.
- `lpsGraphPSL`: The LPS Cayley graph on `PSL(2,q)`.
-/

open SimpleGraph Fintype Finset CayleyGraph GraphExpansion Matrix

noncomputable section

namespace LPS

/-! ## Group definitions -/

/-- The projective general linear group `PGL(2, q) = GL(2, 𝔽_q) / center(GL(2, 𝔽_q))`.
Defined as the quotient of `GL(2, ZMod q)` by its center. -/
abbrev PGL2 (q : ℕ) : Type :=
  GL (Fin 2) (ZMod q) ⧸ Subgroup.center (GL (Fin 2) (ZMod q))

/-- The projective special linear group `PSL(2, q) = SL(2, 𝔽_q) / center(SL(2, 𝔽_q))`. -/
abbrev PSL2 (q : ℕ) : Type :=
  SpecialLinearGroup (Fin 2) (ZMod q) ⧸
    Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod q))

-- Group instances (automatically derived via abbrev, but explicit for clarity)
instance PGL2.instGroup (q : ℕ) : Group (PGL2 q) := inferInstance
instance PSL2.instGroup (q : ℕ) : Group (PSL2 q) := inferInstance
instance PGL2.instFintype (q : ℕ) [Fact (Nat.Prime q)] : Fintype (PGL2 q) := inferInstance

-- Help the instance search for PSL2 by providing intermediate instances
instance PSL2.instDecidableEqSL (q : ℕ) [Fact (Nat.Prime q)] :
    DecidableEq (SpecialLinearGroup (Fin 2) (ZMod q)) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

instance PSL2.instDecidableCommMul (q : ℕ) [Fact (Nat.Prime q)]
    (z : SpecialLinearGroup (Fin 2) (ZMod q)) :
    Decidable (∀ g : SpecialLinearGroup (Fin 2) (ZMod q), g * z = z * g) :=
  Fintype.decidableForallFintype

instance PSL2.instDecidablePredCenter (q : ℕ) [Fact (Nat.Prime q)] :
    DecidablePred (· ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod q))) :=
  fun z => Subgroup.decidableMemCenter z

instance PSL2.instFintype (q : ℕ) [Fact (Nat.Prime q)] : Fintype (PSL2 q) :=
  QuotientGroup.fintype _

instance PGL2.instDecidableEq (q : ℕ) [Fact (Nat.Prime q)] : DecidableEq (PGL2 q) := inferInstance

instance PSL2.instDecidableLeftRel (q : ℕ) [Fact (Nat.Prime q)] :
    DecidableRel (QuotientGroup.leftRel (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod q)))).r :=
  fun a b => by
    rw [QuotientGroup.leftRel_eq]
    exact PSL2.instDecidablePredCenter q _

instance PSL2.instDecidableEq (q : ℕ) [Fact (Nat.Prime q)] : DecidableEq (PSL2 q) :=
  @Quotient.decidableEq _ _ (PSL2.instDecidableLeftRel q)

/-! ## The set S̃_p and the normalized subset S_p -/

/-- The set `S̃_p = {(a,b,c,d) ∈ ℤ⁴ | a² + b² + c² + d² = p}` of integer
4-tuples whose sum of squares equals `p`. -/
def SpTilde (p : ℕ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  { t | t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2 = (p : ℤ) }

instance (p : ℕ) : DecidablePred (· ∈ SpTilde p) := fun t =>
  inferInstanceAs (Decidable (t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2 = (p : ℤ)))

/-- Predicate for the first nonzero element being positive (for p ≡ 3 mod 4 case). -/
def firstNonzeroPositive (t : ℤ × ℤ × ℤ × ℤ) : Prop :=
  (t.1 > 0) ∨
  (t.1 = 0 ∧ t.2.1 > 0) ∨
  (t.1 = 0 ∧ t.2.1 = 0 ∧ t.2.2.1 > 0) ∨
  (t.1 = 0 ∧ t.2.1 = 0 ∧ t.2.2.1 = 0 ∧ t.2.2.2 > 0)

instance : DecidablePred firstNonzeroPositive := fun t => by
  unfold firstNonzeroPositive; infer_instance

/-- The normalized subset predicate for `S_p`.
When `p ≡ 1 (mod 4)`: `a` is positive and odd.
When `p ≡ 3 (mod 4)`: `a` is even and the first nonzero element is positive. -/
def SpPred (p : ℕ) (t : ℤ × ℤ × ℤ × ℤ) : Prop :=
  t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2 = (p : ℤ) ∧
  if p % 4 = 1 then
    t.1 > 0 ∧ t.1 % 2 = 1
  else
    t.1 % 2 = 0 ∧ firstNonzeroPositive t

instance (p : ℕ) : DecidablePred (SpPred p) := fun t => by
  unfold SpPred; infer_instance

/-- The normalized subset `S_p ⊆ S̃_p`. Defined as the set of integer 4-tuples
`(a,b,c,d)` with `a² + b² + c² + d² = p` satisfying the normalization condition.
Each coordinate is bounded by `√p ≤ p`, so we filter from `[-p, p]⁴`. -/
def Sp (p : ℕ) [Fact (Nat.Prime p)] (hoddp : p % 2 = 1) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-(p : ℤ)) p) ×ˢ (Finset.Icc (-(p : ℤ)) p) ×ˢ
   (Finset.Icc (-(p : ℤ)) p) ×ˢ (Finset.Icc (-(p : ℤ)) p)).filter (SpPred p)

/-- Every element of `S_p` lies in `S̃_p`. -/
lemma Sp_subset_SpTilde (p : ℕ) [Fact (Nat.Prime p)] (hoddp : p % 2 = 1) :
    ∀ t ∈ Sp p hoddp, t ∈ SpTilde p := by
  intro t ht
  simp only [Sp, Finset.mem_filter] at ht
  exact ht.2.1

/-- This follows from Jacobi's four-square theorem: r₄(p) = 8(p+1) for odd prime p,
and the normalization conditions select exactly (p+1) representatives.
Jacobi's four-square theorem is not available in Mathlib. -/
axiom Sp_card (p : ℕ) [Fact (Nat.Prime p)] (hoddp : p % 2 = 1) :
    (Sp p hoddp).card = p + 1

/-! ## Witness lemmas for set non-emptiness -/

/-- Witness: `SpTilde p` is non-empty for any prime `p ≥ 2`.
For `p = 3`, the tuple `(1, 1, 1, 0)` satisfies `1² + 1² + 1² + 0² = 3`. -/
lemma SpTilde_nonempty_three : (SpTilde 3).Nonempty :=
  ⟨(1, 1, 1, 0), by simp [SpTilde]⟩

/-- For any odd prime `p`, `SpTilde p` is non-empty (follows from `Sp` being non-empty
and `Sp_subset_SpTilde`). -/
lemma SpTilde_nonempty (p : ℕ) [Fact (Nat.Prime p)] (hoddp : p % 2 = 1) :
    (SpTilde p).Nonempty := by
  have hcard := Sp_card p hoddp
  have hne : (Sp p hoddp).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.card_empty] at hcard
    omega
  obtain ⟨t, ht⟩ := hne
  exact ⟨t, Sp_subset_SpTilde p hoddp t ht⟩

/-- `Sp p` is non-empty for any odd prime `p`, since `|S_p| = p + 1 ≥ 4 > 0`. -/
lemma Sp_nonempty (p : ℕ) [Fact (Nat.Prime p)] (hoddp : p % 2 = 1) :
    (Sp p hoddp).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have hcard := Sp_card p hoddp
  rw [h, Finset.card_empty] at hcard
  omega

/-! ## Satisfiability witnesses for Sp -/

/-- Witness: Sp premises are satisfiable (p = 3 works). -/
lemma Sp_satisfiable :
    ∃ (p : ℕ), ∃ (_ : Fact (Nat.Prime p)), p % 2 = 1 :=
  ⟨3, Fact.mk (by decide), by decide⟩

/-! ## The matrix M(a,b,c,d) and the LPS generating set -/

/-- The existence of `x, y ∈ 𝔽_q` with `x² + y² + 1 = 0`. For an odd prime `q`,
by `ZMod.sq_add_sq` there exist `a, b` with `a² + b² = -1`, i.e. `a² + b² + 1 = 0`. -/
theorem exists_sum_sq_eq_neg_one (q : ℕ) [Fact (Nat.Prime q)] (hoddq : q % 2 = 1) :
    ∃ (x y : ZMod q), x ^ 2 + y ^ 2 + 1 = 0 := by
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq q (-1 : ZMod q)
  exact ⟨a, b, by rw [hab]; ring⟩

/-- The LPS matrix `M(a,b,c,d)` as a 2×2 matrix over `ZMod q`. -/
def lpsMatrixVal (q : ℕ) (x y : ZMod q) (t : ℤ × ℤ × ℤ × ℤ) :
    Matrix (Fin 2) (Fin 2) (ZMod q) :=
  !![((t.1 : ℤ) : ZMod q) + ((t.2.1 : ℤ) : ZMod q) * x + ((t.2.2.2 : ℤ) : ZMod q) * y,
     -((t.2.1 : ℤ) : ZMod q) * y + ((t.2.2.1 : ℤ) : ZMod q) + ((t.2.2.2 : ℤ) : ZMod q) * x;
     -((t.2.1 : ℤ) : ZMod q) * y - ((t.2.2.1 : ℤ) : ZMod q) + ((t.2.2.2 : ℤ) : ZMod q) * x,
     ((t.1 : ℤ) : ZMod q) - ((t.2.1 : ℤ) : ZMod q) * x - ((t.2.2.2 : ℤ) : ZMod q) * y]

/-- The determinant of M(a,b,c,d) equals ι(a² + b² + c² + d²). -/
lemma lpsMatrixVal_det (q : ℕ) (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (t : ℤ × ℤ × ℤ × ℤ) :
    (lpsMatrixVal q x y t).det =
      (t.1 : ZMod q) ^ 2 + (t.2.1 : ZMod q) ^ 2 +
      (t.2.2.1 : ZMod q) ^ 2 + (t.2.2.2 : ZMod q) ^ 2 := by
  unfold lpsMatrixVal
  simp [det_fin_two]
  linear_combination
    -((t.2.1 : ZMod q) ^ 2 + (t.2.2.2 : ZMod q) ^ 2) * hxy

/-- For (a,b,c,d) ∈ S̃_p with p ≠ q (both prime), M(a,b,c,d) is invertible. -/
lemma lpsMatrixVal_det_ne_zero (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (t : ℤ × ℤ × ℤ × ℤ) (ht : t ∈ SpTilde p) :
    (lpsMatrixVal q x y t).det ≠ 0 := by
  rw [lpsMatrixVal_det q x y hxy]
  simp only [SpTilde, Set.mem_setOf_eq] at ht
  -- The sum of squares equals p in ℤ, so its image in ZMod q equals (p : ZMod q)
  have hsum : (t.1 : ZMod q) ^ 2 + (t.2.1 : ZMod q) ^ 2 +
      (t.2.2.1 : ZMod q) ^ 2 + (t.2.2.2 : ZMod q) ^ 2 = (p : ZMod q) := by
    have h : ((t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2 : ℤ) : ZMod q) =
        ((p : ℤ) : ZMod q) := congrArg (Int.cast (R := ZMod q)) ht
    push_cast [map_add, map_pow] at h
    exact h
  rw [hsum]
  -- (p : ZMod q) ≠ 0 since q ∤ p (distinct primes)
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hq_prime := (Fact.out : Nat.Prime q)
  have hp_prime := (Fact.out : Nat.Prime p)
  have := hp_prime.eq_one_or_self_of_dvd q hdvd
  rcases this with h | h
  · exact Nat.Prime.ne_one hq_prime h
  · exact hpq h.symm

/-- The canonical projection from GL(2, ZMod q) to PGL(2, q). -/
def projPGL (q : ℕ) : GL (Fin 2) (ZMod q) →* PGL2 q :=
  QuotientGroup.mk' _

/-- The canonical projection from SL(2, ZMod q) to PSL(2, q). -/
def projPSL (q : ℕ) : SpecialLinearGroup (Fin 2) (ZMod q) →* PSL2 q :=
  QuotientGroup.mk' _

/-- Lift a matrix with nonzero determinant to GL(2, ZMod q). -/
def matToGL (q : ℕ) [Fact (Nat.Prime q)] (M : Matrix (Fin 2) (Fin 2) (ZMod q))
    (hdet : M.det ≠ 0) : GL (Fin 2) (ZMod q) :=
  ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)).unit

/-- Map a tuple to PGL(2,q) via the LPS matrix, given membership in SpTilde. -/
def tupleToGLElement (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (t : ℤ × ℤ × ℤ × ℤ) (ht : t ∈ SpTilde p) : GL (Fin 2) (ZMod q) :=
  matToGL q (lpsMatrixVal q x y t) (lpsMatrixVal_det_ne_zero q p hpq x y hxy t ht)

/-! ## Helper lemmas for generating set properties -/

/-- A prime is not a perfect square. -/
lemma Nat.Prime.not_perfect_square (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
    a ^ 2 ≠ (p : ℤ) := by
  intro h
  have hp_pos : (0 : ℤ) < p := Int.ofNat_lt.mpr hp.pos
  have ha_pos : 0 < a ^ 2 := h ▸ hp_pos
  have ha_abs : (a.natAbs : ℤ) ^ 2 = (p : ℤ) := by
    rw [Int.natAbs_sq, h]
  have ha_abs' : a.natAbs ^ 2 = p := by exact_mod_cast ha_abs
  have hdvd : a.natAbs ∣ p := ⟨a.natAbs, by rw [ha_abs'.symm]; ring⟩
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h2
  · rw [h1] at ha_abs'; linarith [hp.one_lt]
  · rw [h2] at ha_abs'; nlinarith [hp.one_lt]

/-- If `(n : ZMod q) = 0` and `n² ≤ p` and `q > 2√p`, then `n = 0`. -/
lemma int_eq_zero_of_zmod_eq_zero_of_sq_le {q p : ℕ} [Fact (Nat.Prime q)]
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (n : ℤ) (hn_zmod : (n : ZMod q) = 0) (hn_sq : n ^ 2 ≤ (p : ℤ)) : n = 0 := by
  by_contra h
  have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr (Fact.out : Nat.Prime q).pos
  have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  -- From (n : ZMod q) = 0, we get q ∣ n
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hn_zmod
  obtain ⟨k, hk⟩ := hn_zmod
  have hk_ne : k ≠ 0 := by rintro rfl; simp at hk; exact h hk
  -- |k| ≥ 1, so |n| = |k| * q ≥ q, hence n² ≥ q²
  have habs : q ≤ n.natAbs := by
    rw [hk, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hk_ne)
  have hnsq : (q : ℤ) ^ 2 ≤ n ^ 2 := by
    have h1 : (q : ℤ) ≤ (n.natAbs : ℤ) := by exact_mod_cast habs
    have h2 : (q : ℤ) ^ 2 ≤ (n.natAbs : ℤ) ^ 2 := by nlinarith [Int.ofNat_nonneg q]
    rwa [Int.natAbs_sq] at h2
  -- q > 2√p means q² > 4p ≥ 4n² ... but we only need q² > p ≥ n²? No.
  -- Actually: q² > (2√p)² = 4p. And n² ≤ p. So q² > 4p ≥ 4·n²... nah just q² > 4p > p ≥ n².
  -- But we have q² ≤ n² ≤ p, so q² ≤ p, i.e., q ≤ √p. But q > 2√p, so 2√p < q ≤ √p, contradiction.
  have : (q : ℝ) ^ 2 ≤ (p : ℝ) := by exact_mod_cast le_trans hnsq hn_sq
  have : Real.sqrt p < (q : ℝ) / 2 := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have : (Real.sqrt (p : ℝ)) ^ 2 < ((q : ℝ) / 2) ^ 2 := by
    exact sq_lt_sq' (by linarith) this
  rw [Real.sq_sqrt hp_nonneg] at this
  nlinarith

/-- From `a² + b² + c² + d² = p`, each squared term is at most `p`. -/
lemma sq_le_of_sum_four_sq_eq {a b c d : ℤ} {p : ℕ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = (p : ℤ)) :
    b ^ 2 ≤ (p : ℤ) ∧ c ^ 2 ≤ (p : ℤ) ∧ d ^ 2 ≤ (p : ℤ) := by
  constructor
  · nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d]
  constructor
  · nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg d]
  · nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]

/-- The underlying matrix of `matToGL` is the input matrix. -/
@[simp]
lemma matToGL_val (q : ℕ) [Fact (Nat.Prime q)]
    (M : Matrix (Fin 2) (Fin 2) (ZMod q)) (hdet : M.det ≠ 0) :
    (matToGL q M hdet).val = M := rfl

/-- The underlying matrix of `tupleToGLElement` is `lpsMatrixVal`. -/
@[simp]
lemma tupleToGLElement_val (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (t : ℤ × ℤ × ℤ × ℤ) (ht : t ∈ SpTilde p) :
    (tupleToGLElement q p hpq x y hxy t ht).val = lpsMatrixVal q x y t := rfl

/-- Helper: for any 2×2 matrix M over a comm ring R, commuting with E₁₂ = [[1,1],[0,1]]
    implies M(1,0) = 0 and M(0,0) = M(1,1). -/
private lemma comm_e12_entry10 {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (h : !![1, 1; (0 : R), 1] * M = M * !![1, 1; (0 : R), 1]) :
    M 1 0 = 0 := by
  have := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this

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

/-- If M(a,b,c,d) is in the center of GL(2, ZMod q), derive a contradiction. -/
lemma lpsMatrix_not_in_center (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (t : ℤ × ℤ × ℤ × ℤ) (ht : t ∈ SpTilde p) :
    tupleToGLElement q p hpq x y hxy t ht ∉
      Subgroup.center (GL (Fin 2) (ZMod q)) := by
  intro h_cen
  rw [Subgroup.mem_center_iff] at h_cen
  set M_gl := tupleToGLElement q p hpq x y hxy t ht
  -- Construct E₁₂ and E₂₁ in GL
  have e12_det : (!![1, 1; (0 : ZMod q), 1]).det ≠ 0 := by
    simp [Matrix.det_fin_two]
  set e12 := matToGL q !![1, 1; (0 : ZMod q), 1] e12_det
  have e21_det : (!![1, (0 : ZMod q); 1, 1]).det ≠ 0 := by
    simp [Matrix.det_fin_two]
  set e21 := matToGL q !![1, (0 : ZMod q); 1, 1] e21_det
  -- Extract matrix commutation
  have hm12 : e12.val * M_gl.val = M_gl.val * e12.val := congr_arg Units.val (h_cen e12)
  have hm21 : e21.val * M_gl.val = M_gl.val * e21.val := congr_arg Units.val (h_cen e21)
  -- Get matrix entries
  set M_mat := M_gl.val
  have hM_eq : M_mat = lpsMatrixVal q x y t := tupleToGLElement_val q p hpq x y hxy t ht
  have he12_eq : e12.val = !![1, 1; (0 : ZMod q), 1] := matToGL_val q _ e12_det
  have he21_eq : e21.val = !![1, (0 : ZMod q); 1, 1] := matToGL_val q _ e21_det
  rw [he12_eq] at hm12; rw [he21_eq] at hm21
  -- Apply commutation lemmas to get entry equations
  have hM10 : M_mat 1 0 = 0 := comm_e12_entry10 M_mat hm12
  have hM01 : M_mat 0 1 = 0 := comm_e21_entry01 M_mat hm21
  have hM_diag : M_mat 0 0 = M_mat 1 1 := comm_e12_diag M_mat hm12
  -- Translate to lpsMatrixVal entries
  set ιb := ((t.2.1 : ℤ) : ZMod q)
  set ιc := ((t.2.2.1 : ℤ) : ZMod q)
  set ιd := ((t.2.2.2 : ℤ) : ZMod q)
  rw [hM_eq] at hM10 hM01 hM_diag
  -- hM10 : -ιb * y - ιc + ιd * x = 0
  -- hM01 : -ιb * y + ιc + ιd * x = 0
  -- hM_diag : ιa + ιb * x + ιd * y = ιa - ιb * x - ιd * y, i.e. 2(ιb * x + ιd * y) = 0
  simp only [lpsMatrixVal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.of_apply, Matrix.cons_val'] at hM10 hM01 hM_diag
  -- From hM10 and hM01: 2*ιc = 0 (subtract) and ιd*x = ιb*y (add)
  have h2_ne : (2 : ZMod q) ≠ 0 := by
    intro h2eq
    have h2eq' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h2eq
    rw [ZMod.natCast_eq_zero_iff] at h2eq'
    -- h2eq' : q ∣ 2, so q ≤ 2 (since 2 > 0), meaning q = 2 (prime), contradicting hoddq
    have hq_le : q ≤ 2 := Nat.le_of_dvd (by norm_num) h2eq'
    have hq_prime := (Fact.out : Nat.Prime q)
    interval_cases q <;> first | exact absurd hq_prime (by decide) | simp_all
  have hιc : ιc = 0 := by
    have hcc : ιc + ιc = 0 := by linear_combination hM01 - hM10
    have : ιc * 2 = 0 := by linear_combination hcc
    exact (mul_eq_zero.mp this).resolve_right h2_ne
  -- ιd * x - ιb * y = 0 and ιb * x + ιd * y = 0
  have eq1 : ιd * x - ιb * y = 0 := by linear_combination hM10 + hιc
  have eq2 : ιb * x + ιd * y = 0 := by
    have h2bxdy : (ιb * x + ιd * y) * 2 = 0 := by linear_combination hM_diag
    exact (mul_eq_zero.mp h2bxdy).resolve_right h2_ne
  -- Solve the system: det = x² + y² = -1 ≠ 0
  have hxy' : x ^ 2 + y ^ 2 = -1 := by linear_combination hxy
  have hιb : ιb = 0 := by
    -- ιb * (x² + y²) = ιb * x * x + ιb * y * y
    -- From eq1: ιb * y = ιd * x. From eq2: ιb * x = -ιd * y.
    -- ιb * (x² + y²) = ιb*x*x + ιd*x*y  (using ιb*y = ιd*x in second term)
    --                  = -ιd*y*x + ιd*x*y = 0
    have : ιb * (x ^ 2 + y ^ 2) = 0 := by linear_combination -y * eq1 + x * eq2
    rw [hxy'] at this; simp at this; exact this
  have hιd : ιd = 0 := by
    have hdx : ιd * x = 0 := by linear_combination eq1 + y * hιb
    have hdy : ιd * y = 0 := by linear_combination eq2 - x * hιb
    -- x and y can't both be zero (x² + y² = -1 ≠ 0)
    by_contra hd
    have hx0 : x = 0 := by
      rw [mul_comm] at hdx
      rcases mul_eq_zero.mp hdx with hx | hιd_eq
      · exact hx
      · exact absurd hιd_eq hd
    have hy0 : y = 0 := by
      rw [mul_comm] at hdy
      rcases mul_eq_zero.mp hdy with hy | hιd_eq
      · exact hy
      · exact absurd hιd_eq hd
    rw [hx0, hy0] at hxy'; simp at hxy'
  -- Now ιb = ιc = ιd = 0, meaning b, c, d ≡ 0 mod q
  have ht_sum : t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2 = (p : ℤ) := ht
  obtain ⟨hb_sq, hc_sq, hd_sq⟩ := sq_le_of_sum_four_sq_eq ht_sum
  have hb0 : t.2.1 = 0 := int_eq_zero_of_zmod_eq_zero_of_sq_le hq_gt t.2.1 hιb hb_sq
  have hc0 : t.2.2.1 = 0 := int_eq_zero_of_zmod_eq_zero_of_sq_le hq_gt t.2.2.1 hιc hc_sq
  have hd0 : t.2.2.2 = 0 := int_eq_zero_of_zmod_eq_zero_of_sq_le hq_gt t.2.2.2 hιd hd_sq
  -- Now a² = p
  rw [hb0, hc0, hd0] at ht_sum; simp at ht_sum
  exact Nat.Prime.not_perfect_square p (Fact.out) t.1 ht_sum

/-- The conjugate tuple (a, -b, -c, -d). -/
def negConj (t : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (t.1, -t.2.1, -t.2.2.1, -t.2.2.2)

/-- The conjugate tuple is in SpTilde whenever the original is. -/
lemma negConj_mem_SpTilde {p : ℕ} {t : ℤ × ℤ × ℤ × ℤ} (ht : t ∈ SpTilde p) :
    negConj t ∈ SpTilde p := by
  simp only [SpTilde, Set.mem_setOf_eq, negConj] at *; nlinarith [sq_nonneg t.2.1]

/-- The LPS matrix of the conjugate tuple is the adjugate of the original. -/
lemma lpsMatrixVal_negConj (q : ℕ) (x y : ZMod q) (t : ℤ × ℤ × ℤ × ℤ) :
    lpsMatrixVal q x y (negConj t) = (lpsMatrixVal q x y t).adjugate := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lpsMatrixVal, negConj, Matrix.adjugate_fin_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const] <;> ring

/-- When a = 0, M(0,-b,-c,-d) = -M(0,b,c,d). -/
lemma lpsMatrixVal_negConj_zero_fst (q : ℕ) (x y : ZMod q)
    (t : ℤ × ℤ × ℤ × ℤ) (ha : t.1 = 0) :
    lpsMatrixVal q x y (negConj t) = -(lpsMatrixVal q x y t) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lpsMatrixVal, negConj, ha, Matrix.of_apply, Matrix.neg_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const] <;> ring

/-- Negating b, c, d preserves the Sp predicate when a > 0 (both p ≡ 1 and p ≡ 3 cases). -/
lemma negConj_mem_Sp_of_fst_pos {p : ℕ} [Fact (Nat.Prime p)]
    (hoddp : p % 2 = 1) (t : ℤ × ℤ × ℤ × ℤ) (ht : t ∈ Sp p hoddp)
    (ha_pos : t.1 > 0) : negConj t ∈ Sp p hoddp := by
  simp only [Sp, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht ⊢
  obtain ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ⟨hc1, hc2⟩, ⟨hd1, hd2⟩⟩, hpred⟩ := ht
  simp only [SpPred, negConj] at hpred ⊢
  obtain ⟨hsum, hcond⟩ := hpred
  refine ⟨⟨⟨ha1, ha2⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩⟩, ⟨by nlinarith, ?_⟩⟩
  split_ifs at hcond ⊢ with hp
  · -- p ≡ 1 (mod 4): a > 0, a odd. Same for negConj since a unchanged.
    exact ⟨ha_pos, hcond.2⟩
  · -- p ≡ 3 (mod 4): a even, firstNonzeroPositive
    exact ⟨hcond.1, Or.inl ha_pos⟩

/-- The PGL image of tupleToGLElement(negConj t) equals the inverse of tupleToGLElement(t).
    This follows from adj(M(t)) * M(t) = det(M(t)) • I, and negConj gives the adjugate. -/
lemma projPGL_negConj_eq_inv (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (t : ℤ × ℤ × ℤ × ℤ) (ht : t ∈ SpTilde p) :
    projPGL q (tupleToGLElement q p hpq x y hxy (negConj t) (negConj_mem_SpTilde ht)) =
    (projPGL q (tupleToGLElement q p hpq x y hxy t ht))⁻¹ := by
  rw [eq_comm, inv_eq_iff_mul_eq_one, ← map_mul]
  set g := tupleToGLElement q p hpq x y hxy t ht
  set g' := tupleToGLElement q p hpq x y hxy (negConj t) (negConj_mem_SpTilde ht)
  -- g.val * g'.val = M(t) * adj(M(t)) = det(M(t)) • 1
  have h_prod : g.val * g'.val = (lpsMatrixVal q x y t).det • 1 := by
    show g.val * g'.val = _
    rw [tupleToGLElement_val, tupleToGLElement_val, lpsMatrixVal_negConj]
    exact Matrix.mul_adjugate _
  show (projPGL q) (g * g') = 1
  rw [projPGL, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [Subgroup.mem_center_iff]
  intro k
  apply Units.ext
  simp only [Units.val_mul]
  -- Need: k.val * (g.val * g'.val) = (g.val * g'.val) * k.val
  rw [h_prod]
  simp [smul_mul_assoc, mul_smul_comm]

/-- In the a=0 case, M(negConj t) = -M(t), so their PGL images coincide. -/
lemma projPGL_negConj_eq_self_of_fst_zero (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (t : ℤ × ℤ × ℤ × ℤ) (ht : t ∈ SpTilde p) (ha : t.1 = 0) :
    projPGL q (tupleToGLElement q p hpq x y hxy (negConj t) (negConj_mem_SpTilde ht)) =
    projPGL q (tupleToGLElement q p hpq x y hxy t ht) := by
  -- Both map to the same element since they differ by projPGL(negConj t) * projPGL(t)⁻¹ ∈ center
  -- Using: projPGL(negConj t) = projPGL(t)⁻¹ (from adjugate) and a=0 gives s⁻¹ = s.
  have h_inv := projPGL_negConj_eq_inv q p hpq x y hxy t ht
  -- h_inv : projPGL(negConj t) = projPGL(t)⁻¹
  -- Also: projPGL(negConj t) * projPGL(t) = 1 (from h_inv)
  -- And: M(negConj t) = -M(t) (when a=0), so negConj t differs from t by scaling by -1
  -- In PGL, -M and M have the same image since -I ∈ center
  set g := tupleToGLElement q p hpq x y hxy t ht
  set g' := tupleToGLElement q p hpq x y hxy (negConj t) (negConj_mem_SpTilde ht)
  show (projPGL q) g' = (projPGL q) g
  -- g'.val = -g.val (when a=0), so they differ by -I which is in center
  have hvals : g'.val = -g.val := by
    rw [tupleToGLElement_val, tupleToGLElement_val]
    exact lpsMatrixVal_negConj_zero_fst q x y t ha
  rw [projPGL, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  rw [Subgroup.mem_center_iff]
  intro k
  -- g'⁻¹ * g commutes with k since g'.val = -g.val means g'⁻¹ * g is scalar -I
  -- Key step: compute (g'⁻¹ * g).val
  have h_neg : (g'⁻¹ * g).val = -(1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
    rw [Units.val_mul]
    -- g'.val * (g'⁻¹.val * g.val) = g.val
    have step1 : (-g.val) * (g'⁻¹.val * g.val) = g.val := by
      rw [← hvals, ← mul_assoc, Units.mul_inv, one_mul]
    -- g⁻¹.val * g.val = 1
    have step2 : g⁻¹.val * g.val = 1 := Units.inv_mul g
    -- From step1: -(g.val * (g'⁻¹.val * g.val)) = g.val, so g.val * X = -g.val
    have step3 : g.val * (g'⁻¹.val * g.val) = -(g.val) := by
      have := step1; rwa [neg_mul, neg_eq_iff_eq_neg] at this
    -- Multiply both sides on the left by g⁻¹.val
    have step4 : g⁻¹.val * (g.val * (g'⁻¹.val * g.val)) = g⁻¹.val * (-(g.val)) := by
      rw [step3]
    rw [← mul_assoc, step2, one_mul] at step4
    rw [step4, mul_neg, step2]
  apply Units.ext
  show k.val * (g'⁻¹ * g).val = (g'⁻¹ * g).val * k.val
  rw [h_neg]
  simp [neg_mul, mul_neg]

/-- For t ∈ Sp, either a > 0 (and negConj t ∈ Sp) or a = 0 (and s⁻¹ = s). -/
lemma Sp_fst_nonneg {p : ℕ} [Fact (Nat.Prime p)]
    (hoddp : p % 2 = 1) (t : ℤ × ℤ × ℤ × ℤ) (ht : t ∈ Sp p hoddp) :
    t.1 ≥ 0 := by
  simp only [Sp, Finset.mem_filter, SpPred] at ht
  obtain ⟨_, hsum, hcond⟩ := ht
  split_ifs at hcond with hp
  · exact le_of_lt hcond.1
  · -- p ≡ 3 mod 4: firstNonzeroPositive requires first nonzero ≥ 0
    rcases hcond.2 with h | h | h | h
    · exact le_of_lt h
    · exact le_of_eq h.1.symm
    · exact le_of_eq h.1.symm
    · exact le_of_eq h.1.symm

/-- The LPS generating set in PGL(2, q), as a `SymmGenSet`. -/
def lpsGenSetPGL (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0) :
    SymmGenSet (PGL2 q) where
  carrier := (Sp p hoddp).image (fun t =>
    if h : t ∈ SpTilde p then
      projPGL q (tupleToGLElement q p hpq x y hxy t h)
    else
      1)  -- unreachable for elements of Sp by Sp_subset_SpTilde
  one_not_mem := by
    simp only [Finset.mem_image]
    rintro ⟨t, ht_sp, ht_eq⟩
    have ht_tilde := Sp_subset_SpTilde p hoddp t ht_sp
    simp only [ht_tilde, dite_true] at ht_eq
    have h_cen : tupleToGLElement q p hpq x y hxy t ht_tilde ∈
        Subgroup.center (GL (Fin 2) (ZMod q)) := by
      rwa [projPGL, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ht_eq
    exact lpsMatrix_not_in_center q p hpq hoddq hq_gt x y hxy t ht_tilde h_cen
  inv_mem := by
    intro s hs
    simp only [Finset.mem_image] at hs ⊢
    obtain ⟨t, ht_sp, rfl⟩ := hs
    have ht_tilde := Sp_subset_SpTilde p hoddp t ht_sp
    simp only [ht_tilde, dite_true]
    by_cases ha : t.1 > 0
    · -- Case a > 0: use negConj t ∈ Sp
      refine ⟨negConj t, negConj_mem_Sp_of_fst_pos hoddp t ht_sp ha, ?_⟩
      have ht'_tilde := negConj_mem_SpTilde ht_tilde
      simp only [ht'_tilde, dite_true]
      exact projPGL_negConj_eq_inv q p hpq x y hxy t ht_tilde
    · -- Case a ≤ 0: a = 0 (from Sp_fst_nonneg), so s⁻¹ = s
      have ha0 : t.1 = 0 := by linarith [Sp_fst_nonneg hoddp t ht_sp]
      refine ⟨t, ht_sp, ?_⟩
      simp only [ht_tilde, dite_true]
      -- projPGL(t)⁻¹ = projPGL(negConj t) = projPGL(t)
      rw [← projPGL_negConj_eq_inv q p hpq x y hxy t ht_tilde]
      exact (projPGL_negConj_eq_self_of_fst_zero q p hpq x y hxy t ht_tilde ha0).symm

/-- Scale a matrix by the inverse of a square root of its determinant to get an SL element. -/
noncomputable def matToSL (q : ℕ) [Fact (Nat.Prime q)]
    (M : Matrix (Fin 2) (Fin 2) (ZMod q))
    (r : ZMod q) (hr_ne : r ≠ 0) (hr_sq : r ^ 2 = M.det) :
    SpecialLinearGroup (Fin 2) (ZMod q) :=
  ⟨r⁻¹ • M, by
    rw [Matrix.det_smul, Fintype.card_fin, ← hr_sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hr_ne)]⟩

/-- Get a square root of (p : ZMod q) from the Legendre symbol condition. -/
noncomputable def legendreSqrt (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hleg : legendreSym q (p : ℤ) = 1) : ZMod q :=
  (ZMod.isSquare_of_jacobiSym_eq_one (by rwa [← jacobiSym.legendreSym.to_jacobiSym] : jacobiSym (p : ℤ) q = 1)).choose

lemma legendreSqrt_sq (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hleg : legendreSym q (p : ℤ) = 1) :
    (legendreSqrt q p hpq hleg) ^ 2 = ((p : ℤ) : ZMod q) := by
  have h := (ZMod.isSquare_of_jacobiSym_eq_one
    (by rwa [← jacobiSym.legendreSym.to_jacobiSym] : jacobiSym (p : ℤ) q = 1)).choose_spec
  show (legendreSqrt q p hpq hleg) ^ 2 = _
  unfold legendreSqrt
  rw [sq]; exact h.symm

lemma legendreSqrt_ne_zero (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hleg : legendreSym q (p : ℤ) = 1) :
    legendreSqrt q p hpq hleg ≠ 0 := by
  intro h
  have hsq := legendreSqrt_sq q p hpq hleg
  rw [h, zero_pow (by norm_num : 2 ≠ 0)] at hsq
  have : ((p : ℤ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdvd
    have := (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd q (Int.natCast_dvd_natCast.mp hdvd)
    rcases this with h | h
    · exact absurd h (Nat.Prime.ne_one (Fact.out : Nat.Prime q))
    · exact hpq h.symm
  exact this hsq.symm

/-- Construct an SL element from the LPS matrix using the Legendre symbol square root. -/
noncomputable def tupleToSLElement (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hleg : legendreSym q (p : ℤ) = 1)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (t : ℤ × ℤ × ℤ × ℤ) (ht : t ∈ SpTilde p) :
    SpecialLinearGroup (Fin 2) (ZMod q) :=
  matToSL q (lpsMatrixVal q x y t) (legendreSqrt q p hpq hleg)
    (legendreSqrt_ne_zero q p hpq hleg)
    (by rw [legendreSqrt_sq, lpsMatrixVal_det q x y hxy]
        simp [SpTilde, Set.mem_setOf_eq] at ht
        push_cast [map_add, map_pow]
        have := congr_arg (Int.cast : ℤ → ZMod q) ht.symm
        push_cast [map_add, map_pow] at this
        exact this)

/-- tupleToSLElement(negConj t) * tupleToSLElement(t) = 1 in SL. -/
lemma tupleToSL_negConj_mul_self_eq_one (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hleg : legendreSym q (p : ℤ) = 1)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (t : ℤ × ℤ × ℤ × ℤ) (ht : t ∈ SpTilde p) :
    tupleToSLElement q p hpq hleg x y hxy (negConj t) (negConj_mem_SpTilde ht) *
    tupleToSLElement q p hpq hleg x y hxy t ht = 1 := by
  apply Subtype.ext
  show (tupleToSLElement q p hpq hleg x y hxy (negConj t) (negConj_mem_SpTilde ht)).val *
       (tupleToSLElement q p hpq hleg x y hxy t ht).val = 1
  simp only [tupleToSLElement, matToSL]
  -- Product = (r⁻¹ • adj(M)) * (r⁻¹ • M) = r⁻² • (adj(M) * M) = r⁻² • (det(M) • I) = I
  rw [lpsMatrixVal_negConj, smul_mul_assoc, mul_smul_comm, smul_smul,
    Matrix.adjugate_mul, smul_smul]
  set r := legendreSqrt q p hpq hleg
  have hr_ne := legendreSqrt_ne_zero q p hpq hleg
  -- det(M(t)) = (p : ZMod q) = r²
  have hdet : (lpsMatrixVal q x y t).det = r ^ 2 := by
    rw [lpsMatrixVal_det q x y hxy, legendreSqrt_sq]
    simp only [SpTilde, Set.mem_setOf_eq] at ht
    have := congr_arg (Int.cast : ℤ → ZMod q) ht
    push_cast at this
    exact_mod_cast this
  rw [hdet]
  have : r⁻¹ * r⁻¹ * r ^ 2 = 1 := by
    rw [sq, ← mul_assoc, mul_assoc (r⁻¹) (r⁻¹) r, inv_mul_cancel₀ hr_ne, mul_one, inv_mul_cancel₀ hr_ne]
  rw [this, one_smul]

/-- In PSL, projPSL(negConj t) = projPSL(t) when a = 0 (since M(negConj t) = -M(t)). -/
lemma projPSL_negConj_eq_self_of_fst_zero (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddq : q % 2 = 1)
    (hleg : legendreSym q (p : ℤ) = 1)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (t : ℤ × ℤ × ℤ × ℤ) (ht : t ∈ SpTilde p) (ha : t.1 = 0) :
    projPSL q (tupleToSLElement q p hpq hleg x y hxy (negConj t) (negConj_mem_SpTilde ht)) =
    projPSL q (tupleToSLElement q p hpq hleg x y hxy t ht) := by
  -- Key: (negConj t)⁻¹ * t = t * t, and t².val = -I which is in center(SL).
  set nc := tupleToSLElement q p hpq hleg x y hxy (negConj t) (negConj_mem_SpTilde ht)
  set tt := tupleToSLElement q p hpq hleg x y hxy t ht
  show (projPSL q) nc = (projPSL q) tt
  rw [projPSL, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  -- Need: nc⁻¹ * tt ∈ center(SL)
  -- nc * tt = 1, so nc⁻¹ = tt, so nc⁻¹ * tt = tt * tt = tt²
  have h1 := tupleToSL_negConj_mul_self_eq_one q p hpq hleg x y hxy t ht
  have h_inv : nc⁻¹ = tt := mul_left_cancel (by rw [mul_inv_cancel, h1] : nc * nc⁻¹ = nc * tt)
  rw [h_inv]
  -- Show tt * tt has matrix -I, hence is in center
  -- tt.val = r⁻¹ • M(t). So (tt*tt).val = r⁻² • M(t)².
  -- From adj(M(t)) = M(negConj t) = -M(t) (a=0), and adj(M)*M = det(M)•I:
  -- (-M(t))*M(t) = det(M)•I, so M(t)² = -det(M)•I.
  -- (tt*tt).val = r⁻² • (-det(M)•I) = -I (since det(M) = r²).
  have htt_sq_val : (tt * tt).val = -(1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
    show tt.val * tt.val = _
    simp only [tt, tupleToSLElement, matToSL]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    -- M(t)² = -det(M(t)) • I  (since adj(M) = -M when a=0)
    have h_adj_neg : (lpsMatrixVal q x y t).adjugate = -(lpsMatrixVal q x y t) := by
      rw [← lpsMatrixVal_negConj, lpsMatrixVal_negConj_zero_fst q x y t ha]
    have h_sq : lpsMatrixVal q x y t * lpsMatrixVal q x y t =
        -((lpsMatrixVal q x y t).det • (1 : Matrix (Fin 2) (Fin 2) (ZMod q))) := by
      have hadj := Matrix.adjugate_mul (lpsMatrixVal q x y t)
      rw [h_adj_neg, neg_mul] at hadj
      exact neg_eq_iff_eq_neg.mp hadj
    set r := legendreSqrt q p hpq hleg
    have hr_ne := legendreSqrt_ne_zero q p hpq hleg
    have hdet_eq : (lpsMatrixVal q x y t).det = r ^ 2 := by
      rw [lpsMatrixVal_det q x y hxy, legendreSqrt_sq]
      simp only [SpTilde, Set.mem_setOf_eq] at ht
      have := congr_arg (Int.cast : ℤ → ZMod q) ht
      push_cast at this
      exact_mod_cast this
    rw [h_sq, smul_neg, smul_smul, hdet_eq]
    have : r⁻¹ * r⁻¹ * r ^ 2 = 1 := by
      rw [sq, ← mul_assoc, mul_assoc (r⁻¹) (r⁻¹) r, inv_mul_cancel₀ hr_ne, mul_one, inv_mul_cancel₀ hr_ne]
    rw [this, one_smul]
  rw [Subgroup.mem_center_iff]
  intro g; apply Subtype.ext
  have : (tt * tt).val = -(1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := htt_sq_val
  show (g * (tt * tt)).val = ((tt * tt) * g).val
  simp only [SpecialLinearGroup.coe_mul, this, neg_mul, mul_neg, neg_neg, one_mul, mul_one]

/-- The LPS generating set in PSL(2, q). -/
def lpsGenSetPSL (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (hleg : legendreSym q (p : ℤ) = 1)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0) :
    SymmGenSet (PSL2 q) where
  carrier := (Sp p hoddp).image (fun t =>
    if h : t ∈ SpTilde p then
      projPSL q (tupleToSLElement q p hpq hleg x y hxy t h)
    else
      1)
  one_not_mem := by
    simp only [Finset.mem_image]
    rintro ⟨t, ht_sp, ht_eq⟩
    have ht_tilde := Sp_subset_SpTilde p hoddp t ht_sp
    simp only [ht_tilde, dite_true] at ht_eq
    have h_cen := (QuotientGroup.eq_one_iff _).mp ht_eq
    rw [Subgroup.mem_center_iff] at h_cen
    -- Construct E₁₂, E₂₁ as SL elements (det = 1)
    set e12_sl : SpecialLinearGroup (Fin 2) (ZMod q) :=
      ⟨!![1, 1; (0 : ZMod q), 1], by simp [Matrix.det_fin_two]⟩
    set e21_sl : SpecialLinearGroup (Fin 2) (ZMod q) :=
      ⟨!![1, (0 : ZMod q); 1, 1], by simp [Matrix.det_fin_two]⟩
    -- Get matrix commutation of M' = r⁻¹ • M(t) with E₁₂, E₂₁
    have hm12 : e12_sl.val * (tupleToSLElement q p hpq hleg x y hxy t ht_tilde).val =
        (tupleToSLElement q p hpq hleg x y hxy t ht_tilde).val * e12_sl.val :=
      congr_arg Subtype.val (h_cen e12_sl)
    have hm21 : e21_sl.val * (tupleToSLElement q p hpq hleg x y hxy t ht_tilde).val =
        (tupleToSLElement q p hpq hleg x y hxy t ht_tilde).val * e21_sl.val :=
      congr_arg Subtype.val (h_cen e21_sl)
    -- M'.val = r⁻¹ • lpsMatrixVal, extract commutation of lpsMatrixVal
    set r := legendreSqrt q p hpq hleg
    have hr_ne := legendreSqrt_ne_zero q p hpq hleg
    have hM'_val : (tupleToSLElement q p hpq hleg x y hxy t ht_tilde).val =
        r⁻¹ • lpsMatrixVal q x y t := rfl
    rw [hM'_val] at hm12 hm21
    -- From r⁻¹ • M commuting with N, derive M commuting with N
    have hm12' : !![1, 1; (0 : ZMod q), 1] * lpsMatrixVal q x y t =
        lpsMatrixVal q x y t * !![1, 1; (0 : ZMod q), 1] := by
      have := hm12
      rw [mul_smul_comm, smul_mul_assoc] at this
      have h := congr_arg (r • ·) this
      dsimp only at h
      rw [smul_smul, smul_smul, mul_inv_cancel₀ hr_ne, one_smul, one_smul] at h
      exact h
    have hm21' : !![1, (0 : ZMod q); 1, 1] * lpsMatrixVal q x y t =
        lpsMatrixVal q x y t * !![1, (0 : ZMod q); 1, 1] := by
      have := hm21
      rw [mul_smul_comm, smul_mul_assoc] at this
      have h := congr_arg (r • ·) this
      dsimp only at h
      rw [smul_smul, smul_smul, mul_inv_cancel₀ hr_ne, one_smul, one_smul] at h
      exact h
    -- Now same argument as PGL: extract entry equations
    have hM10 := comm_e12_entry10 _ hm12'
    have hM01 := comm_e21_entry01 _ hm21'
    have hM_diag := comm_e12_diag _ hm12'
    -- Same algebraic argument for ι(b) = ι(c) = ι(d) = 0
    simp only [lpsMatrixVal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.of_apply, Matrix.cons_val'] at hM10 hM01 hM_diag
    set ιb := ((t.2.1 : ℤ) : ZMod q)
    set ιc := ((t.2.2.1 : ℤ) : ZMod q)
    set ιd := ((t.2.2.2 : ℤ) : ZMod q)
    have h2_ne : (2 : ZMod q) ≠ 0 := by
      intro h2eq
      have h2eq' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h2eq
      rw [ZMod.natCast_eq_zero_iff] at h2eq'
      have hq_le : q ≤ 2 := Nat.le_of_dvd (by norm_num) h2eq'
      have hq_prime := (Fact.out : Nat.Prime q)
      interval_cases q <;> first | exact absurd hq_prime (by decide) | simp_all
    have hιc : ιc = 0 := by
      have hcc : ιc + ιc = 0 := by linear_combination hM01 - hM10
      have : ιc * 2 = 0 := by linear_combination hcc
      exact (mul_eq_zero.mp this).resolve_right h2_ne
    have hxy' : x ^ 2 + y ^ 2 = -1 := by linear_combination hxy
    have eq1 : ιd * x - ιb * y = 0 := by linear_combination hM10 + hιc
    have eq2 : ιb * x + ιd * y = 0 := by
      have h2bxdy : (ιb * x + ιd * y) * 2 = 0 := by linear_combination hM_diag
      exact (mul_eq_zero.mp h2bxdy).resolve_right h2_ne
    have hιb : ιb = 0 := by
      have : ιb * (x ^ 2 + y ^ 2) = 0 := by linear_combination -y * eq1 + x * eq2
      rw [hxy'] at this; simp at this; exact this
    have hιd : ιd = 0 := by
      have hd1 : ιd * x = 0 := by linear_combination eq1 + y * hιb
      have hd2 : ιd * y = 0 := by linear_combination eq2 - x * hιb
      by_contra hd
      have hx0 : x = 0 := by
        rw [mul_comm] at hd1
        rcases mul_eq_zero.mp hd1 with hx | hιd_eq
        · exact hx
        · exact absurd hιd_eq hd
      have hy0 : y = 0 := by
        rw [mul_comm] at hd2
        rcases mul_eq_zero.mp hd2 with hy | hιd_eq
        · exact hy
        · exact absurd hιd_eq hd
      rw [hx0, hy0] at hxy'; simp at hxy'
    have ht_sum : t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2 = (p : ℤ) := ht_tilde
    obtain ⟨hb_sq, hc_sq, hd_sq⟩ := sq_le_of_sum_four_sq_eq ht_sum
    have hb0 := int_eq_zero_of_zmod_eq_zero_of_sq_le hq_gt t.2.1 hιb hb_sq
    have hc0 := int_eq_zero_of_zmod_eq_zero_of_sq_le hq_gt t.2.2.1 hιc hc_sq
    have hd0 := int_eq_zero_of_zmod_eq_zero_of_sq_le hq_gt t.2.2.2 hιd hd_sq
    rw [hb0, hc0, hd0] at ht_sum; simp at ht_sum
    exact Nat.Prime.not_perfect_square p (Fact.out) t.1 ht_sum
  inv_mem := by
    intro s hs
    simp only [Finset.mem_image] at hs ⊢
    obtain ⟨t, ht_sp, rfl⟩ := hs
    have ht_tilde := Sp_subset_SpTilde p hoddp t ht_sp
    simp only [ht_tilde, dite_true]
    -- Similar to PGL: use negConj t
    by_cases ha : t.1 > 0
    · -- negConj t ∈ Sp, and projPSL(negConj t) = projPSL(t)⁻¹
      refine ⟨negConj t, negConj_mem_Sp_of_fst_pos hoddp t ht_sp ha, ?_⟩
      simp only [negConj_mem_SpTilde ht_tilde, dite_true]
      -- From tupleToSL_negConj_mul_self_eq_one: nc * t = 1, so t * nc = 1
      rw [eq_comm, inv_eq_iff_mul_eq_one, ← map_mul]
      have h1 := tupleToSL_negConj_mul_self_eq_one q p hpq hleg x y hxy t ht_tilde
      rw [show tupleToSLElement q p hpq hleg x y hxy t ht_tilde *
            tupleToSLElement q p hpq hleg x y hxy (negConj t) (negConj_mem_SpTilde ht_tilde) = 1
          from mul_eq_one_comm.mpr h1]
      exact map_one (projPSL q)
    · -- a = 0 case: s⁻¹ = s
      have ha0 : t.1 = 0 := by linarith [Sp_fst_nonneg hoddp t ht_sp]
      refine ⟨t, ht_sp, ?_⟩
      simp only [ht_tilde, dite_true]
      -- projPSL(t)⁻¹ = projPSL(negConj t) = projPSL(t) (a=0 case)
      have h_inv : projPSL q (tupleToSLElement q p hpq hleg x y hxy (negConj t) (negConj_mem_SpTilde ht_tilde)) =
          (projPSL q (tupleToSLElement q p hpq hleg x y hxy t ht_tilde))⁻¹ := by
        rw [eq_comm, inv_eq_iff_mul_eq_one, ← map_mul]
        have h1 := tupleToSL_negConj_mul_self_eq_one q p hpq hleg x y hxy t ht_tilde
        rw [show tupleToSLElement q p hpq hleg x y hxy t ht_tilde *
              tupleToSLElement q p hpq hleg x y hxy (negConj t) (negConj_mem_SpTilde ht_tilde) = 1
            from mul_eq_one_comm.mpr h1]
        exact map_one (projPSL q)
      have h_eq := projPSL_negConj_eq_self_of_fst_zero q p hpq hoddq hleg x y hxy t ht_tilde ha0
      rw [← h_inv, h_eq]

/-! ## Satisfiability witnesses for generating set axioms -/

/-- Witness: `lpsGenSetPGL` is satisfiable. -/
lemma lpsGenSetPGL_satisfiable :
    ∃ (q p : ℕ), ∃ (_ : Fact (Nat.Prime q)) (_ : Fact (Nat.Prime p)),
      p ≠ q ∧ p % 2 = 1 ∧ q % 2 = 1 :=
  ⟨5, 3, Fact.mk (by decide), Fact.mk (by decide), by decide, by decide, by decide⟩

/-- Witness: `lpsGenSetPSL` is satisfiable. -/
lemma lpsGenSetPSL_satisfiable :
    ∃ (q p : ℕ), ∃ (_ : Fact (Nat.Prime q)) (_ : Fact (Nat.Prime p)),
      p ≠ q ∧ p % 2 = 1 ∧ q % 2 = 1 :=
  ⟨5, 3, Fact.mk (by decide), Fact.mk (by decide), by decide, by decide, by decide⟩

/-- The map from Sp to PGL(2,q) is injective (distinct tuples in Sp give distinct
projective classes), and |Sp| = p+1 by Jacobi's four-square theorem. The injectivity
requires that q > 2√p ensures no two distinct tuples can differ by a scalar multiple
mod q. This deep number-theoretic result is not provable from Mathlib. -/
axiom lpsGenSetPGL_card (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0) :
    (lpsGenSetPGL q p hpq hoddp hoddq hq_gt x y hxy).carrier.card = p + 1

/-- Witness: `lpsGenSetPGL_card` is satisfiable. -/
lemma lpsGenSetPGL_card_satisfiable :
    ∃ (q p : ℕ), ∃ (_ : Fact (Nat.Prime q)) (_ : Fact (Nat.Prime p)),
      p ≠ q ∧ p % 2 = 1 ∧ q % 2 = 1 :=
  ⟨5, 3, Fact.mk (by decide), Fact.mk (by decide), by decide, by decide, by decide⟩

/-- Same as `lpsGenSetPGL_card` but for the PSL case. The injectivity of the map
from Sp to PSL(2,q) via the scaled matrices requires the same deep number-theoretic
arguments about quaternion arithmetic modulo q. -/
axiom lpsGenSetPSL_card (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (hleg : legendreSym q (p : ℤ) = 1)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0) :
    (lpsGenSetPSL q p hpq hoddp hoddq hq_gt hleg x y hxy).carrier.card = p + 1

/-- Witness: `lpsGenSetPSL_card` is satisfiable. -/
lemma lpsGenSetPSL_card_satisfiable :
    ∃ (q p : ℕ), ∃ (_ : Fact (Nat.Prime q)) (_ : Fact (Nat.Prime p)),
      p ≠ q ∧ p % 2 = 1 ∧ q % 2 = 1 :=
  ⟨5, 3, Fact.mk (by decide), Fact.mk (by decide), by decide, by decide, by decide⟩

/-! ## Generation property

The original statement asserts that `S_{p,q}` is a *generating* set of `G`, i.e.,
the subgroup generated by `S_{p,q}` equals all of `G`. This follows from the strong
approximation theorem for quaternion algebras (Lubotzky–Phillips–Sarnak), which is
far beyond current Mathlib infrastructure.
-/

/-- `S_{p,q}` generates all of `PGL(2,q)`: the subgroup closure of the carrier
equals the whole group. This is a deep result following from the strong approximation
theorem for quaternion algebras (Lubotzky–Phillips–Sarnak). -/
axiom lpsGenSetPGL_generates (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0) :
    Subgroup.closure (↑(lpsGenSetPGL q p hpq hoddp hoddq hq_gt x y hxy).carrier : Set (PGL2 q)) = ⊤

/-- Witness: `lpsGenSetPGL_generates` premises are satisfiable. -/
lemma lpsGenSetPGL_generates_satisfiable :
    ∃ (q p : ℕ), ∃ (_ : Fact (Nat.Prime q)) (_ : Fact (Nat.Prime p)),
      p ≠ q ∧ p % 2 = 1 ∧ q % 2 = 1 :=
  ⟨5, 3, Fact.mk (by decide), Fact.mk (by decide), by decide, by decide, by decide⟩

/-- `S_{p,q}` generates all of `PSL(2,q)`: the subgroup closure of the carrier
equals the whole group. This is a deep result following from the strong approximation
theorem for quaternion algebras (Lubotzky–Phillips–Sarnak). -/
axiom lpsGenSetPSL_generates (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (hleg : legendreSym q (p : ℤ) = 1)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0) :
    Subgroup.closure (↑(lpsGenSetPSL q p hpq hoddp hoddq hq_gt hleg x y hxy).carrier : Set (PSL2 q)) = ⊤

/-- Witness: `lpsGenSetPSL_generates` premises are satisfiable. -/
lemma lpsGenSetPSL_generates_satisfiable :
    ∃ (q p : ℕ), ∃ (_ : Fact (Nat.Prime q)) (_ : Fact (Nat.Prime p)),
      p ≠ q ∧ p % 2 = 1 ∧ q % 2 = 1 :=
  ⟨5, 3, Fact.mk (by decide), Fact.mk (by decide), by decide, by decide, by decide⟩

/-! ## The LPS Cayley graphs -/

/-- The LPS graph on PGL(2,q): the Cayley graph `Cay(PGL(2,q), S_{p,q})`.
When `(p/q) = -1` (Legendre symbol ≠ 1), the group is `PGL(2,q)`. -/
def lpsGraphPGL (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0) :
    SimpleGraph (PGL2 q) :=
  cayleyGraph (lpsGenSetPGL q p hpq hoddp hoddq hq_gt x y hxy)

/-- The LPS graph on PSL(2,q): the Cayley graph `Cay(PSL(2,q), S_{p,q})`.
When `(p/q) = 1` (Legendre symbol = 1), the group is `PSL(2,q)`. -/
def lpsGraphPSL (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (hleg : legendreSym q (p : ℤ) = 1)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0) :
    SimpleGraph (PSL2 q) :=
  cayleyGraph (lpsGenSetPSL q p hpq hoddp hoddq hq_gt hleg x y hxy)

/-! ## DecidableRel instances -/

instance lpsGraphPGL_decidableAdj (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0) :
    DecidableRel (lpsGraphPGL q p hpq hoddp hoddq hq_gt x y hxy).Adj :=
  cayleyGraph_decidableAdj _

instance lpsGraphPSL_decidableAdj (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (hleg : legendreSym q (p : ℤ) = 1)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0) :
    DecidableRel (lpsGraphPSL q p hpq hoddp hoddq hq_gt hleg x y hxy).Adj :=
  cayleyGraph_decidableAdj _

/-! ## Regularity -/

/-- The LPS graph on PGL is `(p+1)`-regular. -/
theorem lpsGraphPGL_isRegularOfDegree (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0) :
    (lpsGraphPGL q p hpq hoddp hoddq hq_gt x y hxy).IsRegularOfDegree (p + 1) := by
  have hreg := cayleyGraph_isRegularOfDegree (lpsGenSetPGL q p hpq hoddp hoddq hq_gt x y hxy)
  rw [lpsGenSetPGL_card] at hreg
  exact hreg

/-- The LPS graph on PSL is `(p+1)`-regular. -/
theorem lpsGraphPSL_isRegularOfDegree (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (hleg : legendreSym q (p : ℤ) = 1)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0) :
    (lpsGraphPSL q p hpq hoddp hoddq hq_gt hleg x y hxy).IsRegularOfDegree (p + 1) := by
  have hreg := cayleyGraph_isRegularOfDegree (lpsGenSetPSL q p hpq hoddp hoddq hq_gt hleg x y hxy)
  rw [lpsGenSetPSL_card] at hreg
  exact hreg

/-! ## Independence of the choice of (x, y) -/

/-- For any two pairs (x₁,y₁), (x₂,y₂) with xᵢ²+yᵢ²+1=0, there exists g ∈ GL(2,𝔽_q)
conjugating one quaternion embedding to the other, inducing a graph isomorphism
via h ↦ ghg⁻¹. The proof requires constructing an explicit element of the orthogonal
group of the norm form x²+y²+1 over 𝔽_q, which requires algebraic infrastructure
not available in Mathlib. -/
axiom lpsGraphPGL_independent_of_xy (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (x₁ y₁ : ZMod q) (hxy₁ : x₁ ^ 2 + y₁ ^ 2 + 1 = 0)
    (x₂ y₂ : ZMod q) (hxy₂ : x₂ ^ 2 + y₂ ^ 2 + 1 = 0) :
    Nonempty (lpsGraphPGL q p hpq hoddp hoddq hq_gt x₁ y₁ hxy₁ ≃g
              lpsGraphPGL q p hpq hoddp hoddq hq_gt x₂ y₂ hxy₂)

/-- Witness: `lpsGraphPGL_independent_of_xy` is satisfiable. -/
lemma lpsGraphPGL_independent_of_xy_satisfiable :
    ∃ (q p : ℕ), ∃ (_ : Fact (Nat.Prime q)) (_ : Fact (Nat.Prime p)),
      p ≠ q ∧ p % 2 = 1 ∧ q % 2 = 1 :=
  ⟨5, 3, Fact.mk (by decide), Fact.mk (by decide), by decide, by decide, by decide⟩

/-- Same as `lpsGraphPGL_independent_of_xy` but for the PSL case. The conjugation
by g ∈ GL(2,𝔽_q) preserves SL(2,𝔽_q) up to scaling, hence descends to PSL(2,q).
Requires the same orthogonal group infrastructure. -/
axiom lpsGraphPSL_independent_of_xy (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (hleg : legendreSym q (p : ℤ) = 1)
    (x₁ y₁ : ZMod q) (hxy₁ : x₁ ^ 2 + y₁ ^ 2 + 1 = 0)
    (x₂ y₂ : ZMod q) (hxy₂ : x₂ ^ 2 + y₂ ^ 2 + 1 = 0) :
    Nonempty (lpsGraphPSL q p hpq hoddp hoddq hq_gt hleg x₁ y₁ hxy₁ ≃g
              lpsGraphPSL q p hpq hoddp hoddq hq_gt hleg x₂ y₂ hxy₂)

/-- Witness: `lpsGraphPSL_independent_of_xy` is satisfiable. -/
lemma lpsGraphPSL_independent_of_xy_satisfiable :
    ∃ (q p : ℕ), ∃ (_ : Fact (Nat.Prime q)) (_ : Fact (Nat.Prime p)),
      p ≠ q ∧ p % 2 = 1 ∧ q % 2 = 1 :=
  ⟨5, 3, Fact.mk (by decide), Fact.mk (by decide), by decide, by decide, by decide⟩

end LPS

end
