import MerLeanBpqc.Definitions.Def_21_LPSExpanderGraphs
import MerLeanBpqc.Definitions.Def_24_QuotientGraphTrivialization
import MerLeanBpqc.Definitions.Def_20_CayleyGraph
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Definition 30: Unipotent Subgroup for LPS Graphs

For the LPS graph `X_{p,q} = Cay(PGL(2,q), S_{p,q})`, we define the unipotent subgroup
`H = {[[1,x],[0,1]] | x ∈ 𝔽_q} ⊂ PGL(2,q)`, which is isomorphic to `(𝔽_q, +) ≅ ℤ_q`.

## Main Definitions
- `unipotentGL`: The map `x ↦ [[1,x],[0,1]]` into `GL(2, 𝔽_q)`.
- `unipotentPGL`: The composition with the projection to `PGL(2,q)`.
- `unipotentSubgroup`: The subgroup `H ⊂ PGL(2,q)`.

## Main Results
- `unipotentPGL_injective`: The map `x ↦ [[1,x],[0,1]]` is injective into PGL.
- `unipotentSubgroup_card`: `|H| = q`.
- `lpsGenSet_disjoint_unipotentSubgroup`: `S_{p,q} ∩ H = ∅`.
-/

open SimpleGraph Fintype Finset CayleyGraph Matrix LPS

noncomputable section

namespace LPS

variable (q : ℕ) [Fact (Nat.Prime q)]

/-! ## Unipotent GL elements -/

/-- The upper triangular unipotent matrix `[[1,x],[0,1]]` in `GL(2, 𝔽_q)`. -/
def unipotentGL (x : ZMod q) : GL (Fin 2) (ZMod q) := by
  refine ⟨!![1, x; 0, 1], !![1, -x; 0, 1], ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma unipotentGL_val (x : ZMod q) :
    (unipotentGL q x).val = !![1, x; 0, 1] := rfl

@[simp]
lemma unipotentGL_inv_val (x : ZMod q) :
    (unipotentGL q x)⁻¹.val = !![1, -x; 0, 1] := rfl

/-- The unipotent map sends `0` to `1`. -/
lemma unipotentGL_zero : unipotentGL q 0 = 1 := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotentGL_val]

/-- The unipotent map sends `a + b` to `unipotentGL a * unipotentGL b`. -/
lemma unipotentGL_add (a b : ZMod q) :
    unipotentGL q (a + b) = unipotentGL q a * unipotentGL q b := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentGL_val, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The unipotent element projected to `PGL(2,q)`. -/
def unipotentPGL (x : ZMod q) : PGL2 q :=
  projPGL q (unipotentGL q x)

/-- The map `x ↦ [[1,x],[0,1]]` as a group homomorphism `Multiplicative(ZMod q) →* PGL(2,q)`. -/
def unipotentPGLHom : Multiplicative (ZMod q) →* PGL2 q where
  toFun x := unipotentPGL q (Multiplicative.toAdd x)
  map_one' := by
    simp only [toAdd_one, unipotentPGL]
    rw [unipotentGL_zero]
    simp [projPGL, QuotientGroup.mk'_apply]
  map_mul' a b := by
    simp only [toAdd_mul, unipotentPGL]
    rw [unipotentGL_add]
    exact map_mul (projPGL q) _ _

lemma unipotentPGLHom_apply (x : ZMod q) :
    unipotentPGLHom q (Multiplicative.ofAdd x) = unipotentPGL q x := by
  simp [unipotentPGLHom]

/-! ## Injectivity of the unipotent map -/

/-- Two unipotent GL elements that map to the same PGL coset must be equal.
    If `[[1,a],[0,1]]` and `[[1,b],[0,1]]` differ by a scalar in GL, then `a = b`. -/
lemma unipotentPGL_injective : Function.Injective (unipotentPGL q) := by
  intro a b hab
  simp only [unipotentPGL, projPGL] at hab
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
  -- (unipotentGL a)⁻¹ * (unipotentGL b) ∈ center(GL(2, ZMod q))
  rw [Subgroup.mem_center_iff] at hab
  set z := (unipotentGL q a)⁻¹ * (unipotentGL q b)
  -- z.val = [[1, -a],[0, 1]] * [[1, b],[0, 1]] = [[1, b-a],[0, 1]]
  have hz_val : z.val = !![1, b - a; 0, 1] := by
    show ((unipotentGL q a)⁻¹ * (unipotentGL q b)).val = _
    rw [Units.val_mul, unipotentGL_inv_val, unipotentGL_val]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  -- z commutes with all of GL(2, ZMod q)
  -- In particular, z commutes with E₂₁ = [[1,0],[1,1]]
  -- Use comm_e12/comm_e21 style argument to show z is scalar
  -- z.val 1 0 = 0 already. For z scalar, need z.val 0 1 = 0, i.e. b - a = 0.
  -- z commutes with [[0,1],[-1,0]] (swap matrix) if it exists in GL
  -- Actually, easier: z is in center means z.val * M = M * z.val for all M
  -- Take M with M 1 0 = 1, M 0 0 = 0, etc.
  -- z.val = [[1, c],[0, 1]] where c = b - a. For this to be in center:
  -- [[1,c],[0,1]] * [[a₀₀,a₀₁],[a₁₀,a₁₁]] = [[a₀₀,a₀₁],[a₁₀,a₁₁]] * [[1,c],[0,1]]
  -- LHS row 0: [a₀₀ + c*a₁₀, a₀₁ + c*a₁₁]
  -- RHS row 0: [a₀₀, a₀₀*c + a₀₁]
  -- So a₀₀ + c*a₁₀ = a₀₀ → c*a₁₀ = 0 for all a₁₀
  -- Taking a₁₀ = 1: c = 0, i.e. b = a
  -- We can instantiate with the swap matrix or E₂₁
  have hq_prime := (Fact.out : Nat.Prime q)
  -- Take E₂₁ = [[1,0],[1,1]] in GL(2, ZMod q)
  have hdet_e21 : ((!![1, 0; (1 : ZMod q), 1]) : Matrix (Fin 2) (Fin 2) (ZMod q)).det ≠ 0 := by
    simp [Matrix.det_fin_two]
  set e21 := matToGL q !![1, 0; (1 : ZMod q), 1] hdet_e21
  have hcomm := hab e21
  -- hab gives: e21 * z = z * e21
  have h1 : e21.val * z.val = z.val * e21.val := by
    have := congr_arg Units.val hcomm
    simpa [Units.val_mul] using this
  rw [hz_val, matToGL_val] at h1
  -- Extract (0,0) entry: LHS = 1, RHS = 1 + (b - a)
  have h00 := congr_fun (congr_fun h1 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
  -- h00 : b - a = 0
  exact (sub_eq_zero.mp h00).symm

/-! ## The unipotent subgroup -/

/-- The unipotent subgroup `H = {[[1,x],[0,1]] | x ∈ 𝔽_q} ⊂ PGL(2,q)`.
    Isomorphic to `(𝔽_q, +) ≅ ℤ_q`. -/
def unipotentSubgroup : Subgroup (PGL2 q) :=
  (unipotentPGLHom q).range

lemma mem_unipotentSubgroup (g : PGL2 q) :
    g ∈ unipotentSubgroup q ↔ ∃ x : ZMod q, unipotentPGL q x = g := by
  simp [unipotentSubgroup, MonoidHom.mem_range, unipotentPGLHom_apply]

instance : Fintype (unipotentSubgroup q) :=
  MonoidHom.fintypeRange (unipotentPGLHom q)

/-- The cardinality of the unipotent subgroup is `q`. -/
theorem unipotentSubgroup_card : Fintype.card (unipotentSubgroup q) = q := by
  have hinj : Function.Injective (unipotentPGLHom q) := by
    intro a b hab
    simp only [unipotentPGLHom, MonoidHom.coe_mk, OneHom.coe_mk] at hab
    have := unipotentPGL_injective q hab
    exact Multiplicative.toAdd.injective this
  have equiv : Multiplicative (ZMod q) ≃ (unipotentSubgroup q) :=
    Equiv.ofBijective (fun x => ⟨unipotentPGLHom q x, ⟨x, rfl⟩⟩)
      ⟨fun a b h => hinj (Subtype.mk.inj h), fun ⟨y, hy⟩ =>
        let ⟨x, hx⟩ := hy; ⟨x, Subtype.ext hx⟩⟩
  rw [Fintype.card_congr equiv.symm, Fintype.card_multiplicative, ZMod.card]

/-- The order of `H` is odd (since `q` is an odd prime). -/
theorem unipotentSubgroup_card_odd
    (hoddq : q % 2 = 1) : Odd (Fintype.card (unipotentSubgroup q)) := by
  rw [unipotentSubgroup_card]
  rw [Nat.odd_iff]
  exact hoddq

/-! ## Disjointness: S_{p,q} ∩ H = ∅ -/

/-- The determinant of a unipotent GL element is 1. -/
@[simp]
lemma unipotentGL_det (x : ZMod q) :
    (unipotentGL q x).val.det = 1 := by
  simp [Matrix.det_fin_two, unipotentGL_val]

/-- The LPS matrix `M(a,b,c,d)` has determinant `a² + b² + c² + d² = p` in `ZMod q`.
    For `(a,b,c,d) ∈ S̃_p`, `det M = p`. -/
lemma lpsMatrixVal_det_eq_p (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (t : ℤ × ℤ × ℤ × ℤ) (ht : t ∈ SpTilde p) :
    (lpsMatrixVal q x y t).det = (p : ZMod q) := by
  rw [lpsMatrixVal_det q x y hxy t]
  simp only [SpTilde, Set.mem_setOf_eq] at ht
  have := congr_arg (Int.cast : ℤ → ZMod q) ht
  push_cast at this
  exact this

/- In PGL(2,q), the "determinant mod squares" distinguishes elements: if `g ∈ GL(2,q)` has
    `det(g) = c`, then in PGL the determinant class is `c mod (𝔽_q^×)²`. Elements of `H`
    have determinant class `1`, while elements of `S_{p,q}` have determinant class `p`.
    Since `(p/q) = -1`, `p` is not a square mod `q`, so `p ≢ 1 mod (𝔽_q^×)²`. -/

/-- The determinant of a tupleToGLElement is `p` (mod q). -/
lemma tupleToGLElement_det (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (t : ℤ × ℤ × ℤ × ℤ) (ht : t ∈ SpTilde p) :
    (tupleToGLElement q p hpq x y hxy t ht).val.det = (p : ZMod q) := by
  rw [tupleToGLElement_val]
  exact lpsMatrixVal_det_eq_p q p hpq x y hxy t ht

/-- Key lemma: if `g ∈ H` (unipotent subgroup), then any GL lift of `g` has determinant
    that is a perfect square in `𝔽_q^×`. Specifically, `g = projPGL(unipGL(x))` where
    `det(unipGL(x)) = 1 = 1²`. -/
lemma unipotentSubgroup_det_is_square (g : PGL2 q)
    (hg : g ∈ unipotentSubgroup q) :
    ∃ x : ZMod q, unipotentPGL q x = g := by
  rwa [mem_unipotentSubgroup] at hg

/-- If `p ≠ q` are primes, then `(p : ZMod q) ≠ 0`. -/
lemma natCast_prime_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q) :
    (p : ZMod q) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  -- q | p with both prime implies q = p
  have hq_prime := (Fact.out : Nat.Prime q)
  have hp_prime := (Fact.out : Nat.Prime p)
  exact hpq ((hp_prime.eq_one_or_self_of_dvd q h).resolve_left hq_prime.one_lt.ne').symm

/-- `p` is not a square in `ZMod q` when `legendreSym q p = -1`. Uses
    `ZMod.nonsquare_of_jacobiSym_eq_neg_one` via the Legendre-to-Jacobi conversion. -/
lemma not_isSquare_of_legendreSym_neg_one (p : ℕ) [Fact (Nat.Prime p)]
    (hleg : legendreSym q (p : ℤ) = -1) :
    ¬ IsSquare ((p : ℤ) : ZMod q) := by
  rw [jacobiSym.legendreSym.to_jacobiSym] at hleg
  exact ZMod.nonsquare_of_jacobiSym_eq_neg_one hleg


/-- The generating set `S_{p,q}` is disjoint from the unipotent subgroup `H`.
    This follows because elements of `S_{p,q}` have determinant `p` (not a QR mod `q`),
    while elements of `H` have determinant `1` (a QR). In PGL, two GL elements project
    to the same class iff they differ by a scalar, so their determinants differ by a
    perfect square. Since `(p/q) = -1`, `p` is not a QR — contradiction. -/
theorem lpsGenSet_disjoint_unipotentSubgroup
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (hleg : legendreSym q (p : ℤ) = -1) :
    ∀ s ∈ (lpsGenSetPGL q p hpq hoddp hoddq hq_gt x y hxy).carrier,
      s ∉ unipotentSubgroup q := by
  intro s hs hmem
  rw [mem_unipotentSubgroup] at hmem
  obtain ⟨a, rfl⟩ := hmem
  simp only [lpsGenSetPGL, SymmGenSet.carrier, Finset.mem_image] at hs
  obtain ⟨t, ht_sp, ht_eq⟩ := hs
  have ht_tilde := Sp_subset_SpTilde p hoddp t ht_sp
  simp only [ht_tilde, dite_true] at ht_eq
  -- ht_eq : projPGL(tupleToGLElement t) = projPGL(unipotentGL a)
  rw [unipotentPGL, projPGL, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at ht_eq
  rw [Subgroup.mem_center_iff] at ht_eq
  set z := (tupleToGLElement q p hpq x y hxy t ht_tilde)⁻¹ * (unipotentGL q a)
  -- z is in center of GL(2,q): commutes with all elements
  have hz_center : ∀ k : GL (Fin 2) (ZMod q), k * z = z * k := ht_eq
  -- Show z is scalar by commuting with E₁₂ and E₂₁
  have hdet_e12 : ((!![1, 1; (0 : ZMod q), 1]) : Matrix (Fin 2) (Fin 2) (ZMod q)).det ≠ 0 := by
    simp [Matrix.det_fin_two]
  have hdet_e21 : ((!![1, 0; (1 : ZMod q), 1]) : Matrix (Fin 2) (Fin 2) (ZMod q)).det ≠ 0 := by
    simp [Matrix.det_fin_two]
  set e12 := matToGL q !![1, 1; (0 : ZMod q), 1] hdet_e12
  set e21 := matToGL q !![1, 0; (1 : ZMod q), 1] hdet_e21
  have hv12 : e12.val * z.val = z.val * e12.val := by
    have := congr_arg Units.val (hz_center e12); simpa [Units.val_mul] using this
  have hv21 : e21.val * z.val = z.val * e21.val := by
    have := congr_arg Units.val (hz_center e21); simpa [Units.val_mul] using this
  rw [matToGL_val] at hv12 hv21
  have hz10 : z.val 1 0 = 0 := by
    have h := congr_fun (congr_fun hv12 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    exact h
  have hz_diag : z.val 0 0 = z.val 1 1 := by
    have h := congr_fun (congr_fun hv12 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    -- h : z.val 0 1 + z.val 1 1 = z.val 0 0 + z.val 0 1
    have h' : z.val 0 1 + z.val 1 1 = z.val 0 1 + z.val 0 0 := by rw [h, add_comm]
    exact (add_left_cancel h').symm
  have hz01 : z.val 0 1 = 0 := by
    have h := congr_fun (congr_fun hv21 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    exact h
  -- z is scalar: det(z) = c² where c = z.val 0 0
  have hz_det : z.val.det = (z.val 0 0) ^ 2 := by
    simp [Matrix.det_fin_two, hz10, hz01, hz_diag, sq]
  -- det(z) = p⁻¹ (det of tupleToGLElement is p, det of unipotentGL is 1)
  have hp_ne : (p : ZMod q) ≠ 0 := natCast_prime_ne_zero q p hpq
  have hz_det2 : z.val.det = ((p : ZMod q))⁻¹ := by
    show ((tupleToGLElement q p hpq x y hxy t ht_tilde)⁻¹ * (unipotentGL q a)).val.det = _
    rw [Units.val_mul, Matrix.det_mul, unipotentGL_det, mul_one]
    set g := tupleToGLElement q p hpq x y hxy t ht_tilde
    have hg_det : g.val.det = (p : ZMod q) := by
      rw [tupleToGLElement_val]; exact lpsMatrixVal_det_eq_p q p hpq x y hxy t ht_tilde
    -- det(g⁻¹) · det(g) = det(g⁻¹ · g) = det(1) = 1
    have h1 : g⁻¹.val.det * g.val.det = 1 := by
      have : g⁻¹.val * g.val = 1 := by
        show (g⁻¹ * g).val = 1
        rw [inv_mul_cancel]; rfl
      rw [← Matrix.det_mul, this, Matrix.det_one]
    rw [hg_det] at h1
    -- From a · p = 1, deduce a = p⁻¹
    exact mul_right_cancel₀ hp_ne (h1.trans (inv_mul_cancel₀ hp_ne).symm)
  -- So p⁻¹ = c², meaning p⁻¹ is a perfect square
  rw [hz_det2] at hz_det
  have hp_inv_sq : IsSquare ((p : ZMod q)⁻¹) :=
    ⟨z.val 0 0, by rw [hz_det]; ring⟩
  -- p⁻¹ square ⟹ p square (isSquare_inv gives the iff)
  have hp_sq : IsSquare ((p : ZMod q)) := isSquare_inv.mp hp_inv_sq
  -- But legendreSym q p = -1 means p is not a square mod q
  have hp_not_sq : ¬ IsSquare ((p : ℤ) : ZMod q) :=
    not_isSquare_of_legendreSym_neg_one q p hleg
  -- Connect (p : ZMod q) with ((p : ℤ) : ZMod q)
  rw [Int.cast_natCast] at hp_not_sq
  exact hp_not_sq hp_sq

/-- Elements of the center of `GL(2, ZMod q)` are scalar matrices, hence have square det. -/
lemma center_GL2_det_isSquare (z : GL (Fin 2) (ZMod q))
    (hz : z ∈ Subgroup.center (GL (Fin 2) (ZMod q))) :
    IsSquare z.val.det := by
  rw [Subgroup.mem_center_iff] at hz
  have hdet_e12 : ((!![1, 1; (0 : ZMod q), 1]) : Matrix (Fin 2) (Fin 2) (ZMod q)).det ≠ 0 := by
    simp [Matrix.det_fin_two]
  have hdet_e21 : ((!![1, 0; (1 : ZMod q), 1]) : Matrix (Fin 2) (Fin 2) (ZMod q)).det ≠ 0 := by
    simp [Matrix.det_fin_two]
  set e12 := matToGL q !![1, 1; (0 : ZMod q), 1] hdet_e12
  set e21 := matToGL q !![1, 0; (1 : ZMod q), 1] hdet_e21
  have hv12 : e12.val * z.val = z.val * e12.val := by
    have := congr_arg Units.val (hz e12); simpa [Units.val_mul] using this
  have hv21 : e21.val * z.val = z.val * e21.val := by
    have := congr_arg Units.val (hz e21); simpa [Units.val_mul] using this
  rw [matToGL_val] at hv12 hv21
  -- From E₁₂ commutation: z₁₀ = 0 and z₀₀ = z₁₁
  have hz10 : z.val 1 0 = 0 := by
    have h := congr_fun (congr_fun hv12 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h; exact h
  have hz_diag : z.val 0 0 = z.val 1 1 := by
    have h := congr_fun (congr_fun hv12 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    have h' : z.val 0 1 + z.val 1 1 = z.val 0 1 + z.val 0 0 := by rw [h, add_comm]
    exact (add_left_cancel h').symm
  -- From E₂₁ commutation: z₀₁ = 0
  have hz01 : z.val 0 1 = 0 := by
    have h := congr_fun (congr_fun hv21 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h; exact h
  -- z is scalar: det = (z₀₀)²
  exact ⟨z.val 0 0, by simp [Matrix.det_fin_two, hz10, hz01, hz_diag, sq]⟩

/-- The stronger disjointness: `S_{p,q} ∩ gHg⁻¹ = ∅` for all `g ∈ PGL(2,q)`.
    This follows from the determinant argument: conjugation preserves determinant class,
    so elements of `gHg⁻¹` still have determinant class `1`, while elements of `S_{p,q}`
    have determinant class `p ≠ 1` mod squares. -/
theorem lpsGenSet_disjoint_conjugate
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (hleg : legendreSym q (p : ℤ) = -1)
    (g : PGL2 q) (s : PGL2 q)
    (hs : s ∈ (lpsGenSetPGL q p hpq hoddp hoddq hq_gt x y hxy).carrier)
    (h : PGL2 q) (hh : h ∈ unipotentSubgroup q) :
    s ≠ g * h * g⁻¹ := by
  intro heq
  obtain ⟨a, rfl⟩ := (mem_unipotentSubgroup q h).mp hh
  -- Get the GL lift of s from the generating set
  simp only [lpsGenSetPGL, SymmGenSet.carrier, Finset.mem_image] at hs
  obtain ⟨t, ht_sp, ht_eq⟩ := hs
  have ht_tilde := Sp_subset_SpTilde p hoddp t ht_sp
  simp only [ht_tilde, dite_true] at ht_eq
  -- Lift g from PGL to GL
  obtain ⟨G, rfl⟩ := QuotientGroup.mk'_surjective _ g
  -- In PGL: projPGL(tupleToGLElement t) = projPGL(G) * projPGL(unipotentGL a) * projPGL(G)⁻¹
  --       = projPGL(G * unipotentGL a * G⁻¹)
  change s = (projPGL q) G * unipotentPGL q a * ((projPGL q) G)⁻¹ at heq
  rw [← ht_eq, unipotentPGL, ← map_inv, ← map_mul, ← map_mul] at heq
  -- heq : projPGL(tupleToGLElement t) = projPGL(G * unipotentGL a * G⁻¹)
  rw [projPGL, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at heq
  -- z = (tupleToGLElement t)⁻¹ * (G * unipotentGL a * G⁻¹) ∈ center
  set S_lift := tupleToGLElement q p hpq x y hxy t ht_tilde
  set z := S_lift⁻¹ * (G * unipotentGL q a * G⁻¹)
  -- det(z) is a square (z is in center, hence scalar)
  have hz_sq := center_GL2_det_isSquare q z heq
  -- det(z) = det(S_lift)⁻¹ * det(G * unipotentGL a * G⁻¹) = p⁻¹ * 1 = p⁻¹
  have hp_ne : (p : ZMod q) ≠ 0 := natCast_prime_ne_zero q p hpq
  have hz_det : z.val.det = ((p : ZMod q))⁻¹ := by
    show (S_lift⁻¹ * (G * unipotentGL q a * G⁻¹)).val.det = _
    rw [Units.val_mul, Matrix.det_mul]
    -- det(G * unipotentGL a * G⁻¹) = det(G) * det(unipotentGL a) * det(G⁻¹) = 1
    have hconj_det : (G * unipotentGL q a * G⁻¹).val.det = 1 := by
      simp only [Units.val_mul, Matrix.det_mul, unipotentGL_det, mul_one]
      have : G⁻¹.val.det * G.val.det = 1 := by
        rw [← Matrix.det_mul]; show (G⁻¹ * G).val.det = 1
        rw [inv_mul_cancel]; simp [Units.val_one, Matrix.det_one]
      rw [mul_comm G⁻¹.val.det G.val.det] at this; exact this
    rw [hconj_det, mul_one]
    -- det(S_lift⁻¹) = (det S_lift)⁻¹ = p⁻¹
    have hS_det : S_lift.val.det = (p : ZMod q) := by
      rw [tupleToGLElement_val]; exact lpsMatrixVal_det_eq_p q p hpq x y hxy t ht_tilde
    have h1 : S_lift⁻¹.val.det * S_lift.val.det = 1 := by
      rw [← Matrix.det_mul]; show (S_lift⁻¹ * S_lift).val.det = 1
      rw [inv_mul_cancel]; simp [Units.val_one, Matrix.det_one]
    rw [hS_det] at h1
    exact mul_right_cancel₀ hp_ne (h1.trans (inv_mul_cancel₀ hp_ne).symm)
  -- p⁻¹ is a square → p is a square → contradiction with Legendre symbol
  rw [hz_det] at hz_sq
  have hp_sq : IsSquare ((p : ZMod q)) := isSquare_inv.mp hz_sq
  have hp_not_sq : ¬ IsSquare ((p : ℤ) : ZMod q) :=
    not_isSquare_of_legendreSym_neg_one q p hleg
  rw [Int.cast_natCast] at hp_not_sq
  exact hp_not_sq hp_sq

/-- Satisfiability: the premises of `lpsGenSet_disjoint_conjugate` are satisfiable. -/
lemma lpsGenSet_disjoint_conjugate_satisfiable :
    ∃ (q p : ℕ), ∃ (_ : Fact (Nat.Prime q)) (_ : Fact (Nat.Prime p)),
      p ≠ q ∧ p % 2 = 1 ∧ q % 2 = 1 :=
  lpsGenSetPGL_satisfiable

/-! ## Witness lemmas -/

lemma unipotentSubgroup_nonempty : (unipotentSubgroup q : Set (PGL2 q)).Nonempty := ⟨1, (unipotentSubgroup q).one_mem⟩

lemma unipotentSubgroup_satisfiable :
    ∃ q : ℕ, ∃ _ : Fact (Nat.Prime q), Nonempty (unipotentSubgroup q) := by
  exact ⟨3, ⟨by decide⟩, ⟨⟨1, (unipotentSubgroup 3).one_mem⟩⟩⟩

end LPS
