import MerLeanBpqc.Definitions.Def_7_CellComplex
import MerLeanBpqc.Definitions.Def_3_ClassicalCode
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Definition 8: Cycle Graph

The cycle graph `C_ℓ` (for `ℓ ≥ 3`) is a cell complex (Def_7) with `ℓ` 1-cells (edges)
`σ_1, ..., σ_ℓ` and `ℓ` 0-cells (vertices) `τ_1, ..., τ_ℓ` such that
`∂σ_i = {τ_i, τ_{i+1}}` where indices are taken modulo `ℓ`.

Its chain complex is `C_1 →[∂_1] C_0` where `C_1 ≅ 𝔽₂^ℓ` and `C_0 ≅ 𝔽₂^ℓ`,
and `∂_1` is the `ℓ × ℓ` circulant matrix with two 1-entries per column.

The kernel `ker(∂_1)` is the repetition code `span{(1,...,1)}` of dimension 1.
The homology satisfies `dim H_1(C_ℓ) = 1` and `dim H_0(C_ℓ) = 1`.

## Main Definitions
- `CycleGraph.cycleGraph` — the cycle graph cell complex `C_ℓ` (as a `CellComplex`, Def_7)
- `CycleGraph.differential` — the algebraic differential `∂_1 : 𝔽₂^ℓ → 𝔽₂^ℓ`
- `CycleGraph.differentialMap_eq_differential` — cell complex differential agrees with `∂_1`
- `CycleGraph.ker_differential_eq_span` — `ker(∂_1) = span{(1,...,1)}`
- `CycleGraph.finrank_ker_differential` — `dim ker(∂_1) = 1`
- `CycleGraph.finrank_range_differential` — `dim im(∂_1) = ℓ - 1`
- `CycleGraph.dim_H1_cycleGraph` — `dim H_1(C_ℓ) = 1`
- `CycleGraph.dim_H0_cycleGraph` — `dim H_0(C_ℓ) = 1`
- `CycleGraph.repetitionCode` — the repetition code as a `ClassicalCode` (Def_3)
-/

open CategoryTheory Finset

/-! ## The cycle graph differential as a linear map on Fin ℓ → 𝔽₂ -/

namespace CycleGraph

variable (ℓ : ℕ) [NeZero ℓ]

/-- The differential `∂_1 : 𝔽₂^ℓ → 𝔽₂^ℓ` of the cycle graph, defined by
`(∂_1 f)(i) = f(i) + f((i + ℓ - 1) % ℓ)`. On basis vectors `e_j`,
`∂_1(e_j) = e_j + e_{(j+1) % ℓ}`, so column `j` of the matrix has 1-entries
in rows `j` and `(j+1) % ℓ` (the boundary relation `∂σ_j = {τ_j, τ_{j+1}}`).
The `i`-th entry of `∂_1(f)` counts how many edges incident to vertex `i`
have nonzero coefficient in `f`, modulo 2. -/
noncomputable def differential : (Fin ℓ → 𝔽₂) →ₗ[𝔽₂] (Fin ℓ → 𝔽₂) where
  toFun f i := f i + f ⟨(i.val + ℓ - 1) % ℓ, Nat.mod_lt _ (NeZero.pos ℓ)⟩
  map_add' f g := by ext i; simp [Pi.add_apply]; ring
  map_smul' c f := by ext i; simp [Pi.smul_apply, smul_eq_mul]; ring

/-- The all-ones vector `(1, 1, ..., 1) ∈ 𝔽₂^ℓ`. -/
def onesVec : Fin ℓ → 𝔽₂ := fun _ => 1

/-- The differential maps the all-ones vector to zero. -/
lemma differential_onesVec : differential ℓ (onesVec ℓ) = 0 := by
  ext i
  simp only [differential, onesVec, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  exact 𝔽₂.add_self_eq_zero 1

/-- Apply formula for the differential. -/
@[simp]
lemma differential_apply (f : Fin ℓ → 𝔽₂) (i : Fin ℓ) :
    differential ℓ f i = f i + f ⟨(i.val + ℓ - 1) % ℓ, Nat.mod_lt _ (NeZero.pos ℓ)⟩ := by
  simp [differential]

/-! ## Kernel of the differential equals span of the all-ones vector -/

/-- Helper: from the kernel condition, `f(i+1) = f(i)` for `i+1 < ℓ`. -/
lemma ker_differential_succ (f : Fin ℓ → 𝔽₂) (hf : differential ℓ f = 0)
    (i : ℕ) (hi : i + 1 < ℓ) :
    f ⟨i + 1, hi⟩ = f ⟨i, by omega⟩ := by
  have h := congr_fun hf ⟨i + 1, hi⟩
  simp only [differential_apply, Pi.zero_apply] at h
  have hmod : (i + 1 + ℓ - 1) % ℓ = i := by
    have : i + 1 + ℓ - 1 = i + ℓ := by omega
    rw [this, Nat.add_mod, Nat.mod_self, add_zero,
        Nat.mod_eq_of_lt (Nat.mod_lt i (NeZero.pos ℓ)),
        Nat.mod_eq_of_lt (by omega : i < ℓ)]
  have heq : (⟨(i + 1 + ℓ - 1) % ℓ, Nat.mod_lt _ (NeZero.pos ℓ)⟩ : Fin ℓ) =
              ⟨i, by omega⟩ := Fin.ext hmod
  rw [heq] at h
  -- h : f ⟨i+1, _⟩ + f ⟨i, _⟩ = 0, so f ⟨i+1, _⟩ = f ⟨i, _⟩ in 𝔽₂
  rw [← sub_eq_zero]
  rw [𝔽₂.sub_eq_add]
  exact h

/-- If `f` is in the kernel of the differential, then `f i = f 0` for all `i`. -/
lemma ker_differential_const (f : Fin ℓ → 𝔽₂) (hf : differential ℓ f = 0) (i : Fin ℓ) :
    f i = f ⟨0, NeZero.pos ℓ⟩ := by
  obtain ⟨n, hn⟩ := i
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [ker_differential_succ ℓ f hf k hn]
    exact ih (by omega)

/-- The kernel of the differential is exactly `span{onesVec}`. -/
theorem ker_differential_eq_span :
    LinearMap.ker (differential ℓ) =
    Submodule.span 𝔽₂ {onesVec ℓ} := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hf
    use f 0
    ext i
    simp only [onesVec, Pi.smul_apply, smul_eq_mul, mul_one]
    exact (ker_differential_const ℓ f hf i).symm
  · rintro ⟨c, rfl⟩
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, differential_apply, onesVec, mul_one]
    exact 𝔽₂.add_self_eq_zero c

omit [NeZero ℓ] in
/-- The all-ones vector is nonzero when `ℓ ≥ 1`. -/
lemma onesVec_ne_zero (hℓ1 : ℓ ≥ 1) : onesVec ℓ ≠ 0 := by
  intro h
  have : (onesVec ℓ) ⟨0, hℓ1⟩ = (0 : Fin ℓ → 𝔽₂) ⟨0, hℓ1⟩ := congr_fun h _
  simp [onesVec] at this

/-- The kernel of the differential has dimension 1 (assuming `ℓ ≥ 1`). -/
theorem finrank_ker_differential (hℓ1 : ℓ ≥ 1) :
    Module.finrank 𝔽₂ (LinearMap.ker (differential ℓ)) = 1 := by
  rw [ker_differential_eq_span]
  exact _root_.finrank_span_singleton (onesVec_ne_zero ℓ hℓ1)

/-! ## The cycle graph as a cell complex (Def_7) -/

/-- The type of `n`-cells for the cycle graph: `Fin ℓ` in dimensions 0 and 1,
`PEmpty` elsewhere. Uses `match` on the integer dimension. -/
def cellType : ℤ → Type
  | (0 : ℤ) => Fin ℓ
  | (1 : ℤ) => Fin ℓ
  | _ => PEmpty

noncomputable instance cellType_fintype : ∀ n, Fintype (cellType ℓ n)
  | (0 : ℤ) => Fin.fintype ℓ
  | (1 : ℤ) => Fin.fintype ℓ
  | (Int.ofNat (_ + 2)) => inferInstanceAs (Fintype PEmpty)
  | (Int.negSucc _) => inferInstanceAs (Fintype PEmpty)

instance cellType_deceq : ∀ n, DecidableEq (cellType ℓ n)
  | (0 : ℤ) => inferInstanceAs (DecidableEq (Fin ℓ))
  | (1 : ℤ) => inferInstanceAs (DecidableEq (Fin ℓ))
  | (Int.ofNat (_ + 2)) => inferInstanceAs (DecidableEq PEmpty)
  | (Int.negSucc _) => inferInstanceAs (DecidableEq PEmpty)

/-- The boundary map for the cycle graph. For a 1-cell `σ_i`, `∂σ_i = {τ_i, τ_{(i+1) % ℓ}}`.
For all other cells, the boundary is empty. -/
def cellBdry : {n : ℤ} → cellType ℓ n → Finset (cellType ℓ (n - 1))
  | (1 : ℤ), (i : Fin ℓ) =>
    -- ∂σ_i = {τ_i, τ_{(i+1) % ℓ}} where 1 - 1 = 0, so cellType ℓ 0 = Fin ℓ
    ({i, ⟨(i.val + 1) % ℓ, Nat.mod_lt _ (NeZero.pos ℓ)⟩} : Finset (Fin ℓ))
  | (0 : ℤ), _ =>
    -- 0 - 1 = -1, cellType ℓ (-1) = PEmpty
    (∅ : Finset PEmpty)
  | (Int.ofNat (_ + 2)), (σ : PEmpty) => σ.elim
  | (Int.negSucc _), (σ : PEmpty) => σ.elim

/-- The chain complex condition for the cycle graph is vacuously true since
for the only nontrivial boundary (n=1), the target `cells(n-1-1) = cells(-1) = PEmpty`
makes the condition vacuous. -/
theorem cellBdry_bdry :
    ∀ (n : ℤ) (σ : cellType ℓ n) (ρ : cellType ℓ (n - 1 - 1)),
    Even (Finset.card (Finset.filter (fun τ : cellType ℓ (n - 1) => ρ ∈ cellBdry ℓ τ)
      (cellBdry ℓ σ)))
  | (1 : ℤ), _, (ρ : PEmpty) => ρ.elim
  | (0 : ℤ), _, (ρ : PEmpty) => ρ.elim
  | (Int.ofNat (_ + 2)), (σ : PEmpty), _ => σ.elim
  | (Int.negSucc 0), (σ : PEmpty), _ => σ.elim
  | (Int.negSucc (_ + 1)), (σ : PEmpty), _ => σ.elim

/-- The cycle graph `C_ℓ` as a cell complex (Def_7). The 1-cells and 0-cells are
both indexed by `Fin ℓ`, with boundary `∂σ_i = {τ_i, τ_{(i+1) % ℓ}}`.
All other cell sets are empty. The chain complex condition is vacuously true. -/
noncomputable def cycleGraph : CellComplex where
  cells := cellType ℓ
  cells_fintype := cellType_fintype ℓ
  cells_deceq := cellType_deceq ℓ
  bdry := cellBdry ℓ
  bdry_bdry := cellBdry_bdry ℓ

/-! ## Cells of the cycle graph are `Fin ℓ` -/

/-- The 1-cells of the cycle graph are `Fin ℓ` (definitionally). -/
theorem cycleGraph_cells_one : (cycleGraph ℓ).cells 1 = Fin ℓ := rfl

/-- The 0-cells of the cycle graph are `Fin ℓ` (definitionally). -/
theorem cycleGraph_cells_zero : (cycleGraph ℓ).cells 0 = Fin ℓ := rfl

omit [NeZero ℓ] in
/-- Helper: `((i+ℓ-1)%ℓ + 1)%ℓ = i` for `i : Fin ℓ`. -/
lemma pred_mod_succ (hℓ : ℓ ≥ 1) (i : Fin ℓ) :
    ((i.val + ℓ - 1) % ℓ + 1) % ℓ = i.val := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have : i.val + ℓ - 1 + 1 = i.val + 1 * ℓ := by omega
  rw [this, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt i.isLt

omit [NeZero ℓ] in
/-- For `ℓ ≥ 2`, an element `x : Fin ℓ` is never equal to `(x+1) % ℓ`. -/
lemma fin_ne_succ_mod (hℓ : ℓ ≥ 2) (x : Fin ℓ) :
    x ≠ ⟨(x.val + 1) % ℓ, Nat.mod_lt _ (by omega)⟩ := by
  intro h
  have hext := Fin.ext_iff.mp h
  simp only [Fin.val_mk] at hext
  rcases Nat.lt_or_ge (x.val + 1) ℓ with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hext; omega
  · have hxl : x.val + 1 = ℓ := by omega
    rw [hxl, Nat.mod_self] at hext; omega

omit [NeZero ℓ] in
/-- For `ℓ ≥ 2`, `i ≠ pred(i) mod ℓ`. -/
lemma fin_ne_pred_mod (hℓ : ℓ ≥ 2) (i : Fin ℓ) :
    i ≠ (⟨(i.val + ℓ - 1) % ℓ, Nat.mod_lt _ (by omega)⟩ : Fin ℓ) := by
  intro h
  have hext := Fin.ext_iff.mp h
  simp only [Fin.val_mk] at hext
  -- hext : i.val = (i.val + ℓ - 1) % ℓ
  -- Case split on i.val = 0 or i.val ≥ 1
  rcases Nat.eq_or_lt_of_le (Nat.zero_le i.val) with h0 | h0
  · -- i.val = 0: (0 + ℓ - 1) % ℓ = (ℓ - 1) % ℓ = ℓ - 1 (since ℓ ≥ 2)
    rw [← h0, Nat.zero_add] at hext
    rw [Nat.mod_eq_of_lt (by omega : ℓ - 1 < ℓ)] at hext
    omega
  · -- i.val ≥ 1: i.val + ℓ - 1 = (i.val - 1) + ℓ
    have hrewrite : i.val + ℓ - 1 = (i.val - 1) + 1 * ℓ := by omega
    rw [hrewrite, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (by omega : i.val - 1 < ℓ)] at hext
    omega

/-- Helper: the filter set {σ | i ∈ bdry σ} for the cycle graph equals {i, pred(i)}. -/
lemma differentialMap_filter_eq (hℓ : ℓ ≥ 2) (i : Fin ℓ) :
    let j : Fin ℓ := ⟨(i.val + ℓ - 1) % ℓ, Nat.mod_lt _ (NeZero.pos ℓ)⟩
    Finset.univ.filter (fun σ : (cycleGraph ℓ).cells 1 =>
      i ∈ (cycleGraph ℓ).bdry σ) = {i, j} := by
  intro j
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  -- (cycleGraph ℓ).bdry σ for σ : cells 1 unfolds to cellBdry ℓ σ = {σ, ⟨(σ.val+1)%ℓ, _⟩}
  -- i ∈ {σ, ⟨(σ.val+1)%ℓ, _⟩} iff i = σ or i = ⟨(σ.val+1)%ℓ, _⟩
  change i ∈ ({σ, ⟨(σ.val + 1) % ℓ, _⟩} : Finset (Fin ℓ)) ↔ _
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    cases h with
    | inl h => left; exact h.symm
    | inr h =>
      right; apply Fin.ext
      -- Goal: ↑σ = ↑j where j = ⟨(↑i + ℓ - 1) % ℓ, _⟩
      -- h : i = ⟨(↑σ + 1) % ℓ, _⟩, so i.val = (σ.val+1)%ℓ
      have hext := Fin.ext_iff.mp h; simp only [Fin.val_mk] at hext
      -- hext : ↑i = (↑σ + 1) % ℓ
      change σ.val = (i.val + ℓ - 1) % ℓ
      rw [hext]
      -- Goal: σ.val = ((σ.val + 1) % ℓ + ℓ - 1) % ℓ
      rcases Nat.lt_or_ge (σ.val + 1) ℓ with h1 | h1
      · rw [Nat.mod_eq_of_lt h1]
        rw [show σ.val + 1 + ℓ - 1 = σ.val + 1 * ℓ from by omega,
            Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt σ.isLt]
      · have : σ.val + 1 = ℓ := by omega
        rw [this, Nat.mod_self, Nat.zero_add,
            Nat.mod_eq_of_lt (by omega : ℓ - 1 < ℓ)]
        omega
  · intro h
    cases h with
    | inl h => left; exact h.symm
    | inr h =>
      right; rw [h]; apply Fin.ext
      -- Goal: ↑i = (↑j + 1) % ℓ where j = ⟨(↑i + ℓ - 1) % ℓ, _⟩
      change i.val = (j.val + 1) % ℓ
      exact (pred_mod_succ ℓ (by omega) i).symm

/-- The cell complex differential `∂_1` from degree 1 to degree 0 agrees with
`CycleGraph.differential`: both map `f ↦ (i ↦ f(i) + f((i + ℓ - 1) % ℓ))`.
Requires `ℓ ≥ 2` so that each edge has two distinct boundary vertices. -/
theorem differentialMap_eq_differential (hℓ : ℓ ≥ 2) :
    (cycleGraph ℓ).differentialMap 1 = differential ℓ := by
  apply LinearMap.ext; intro f
  apply funext; intro i
  rw [CellComplex.differentialMap_apply]
  simp only [differential, LinearMap.coe_mk, AddHom.coe_mk]
  -- Goal: ∑ σ ∈ univ.filter (fun σ => i ∈ bdry σ), f σ = f i + f ⟨(i.val+ℓ-1)%ℓ, _⟩
  set j : Fin ℓ := ⟨(i.val + ℓ - 1) % ℓ, Nat.mod_lt _ (NeZero.pos ℓ)⟩
  rw [differentialMap_filter_eq ℓ hℓ i]
  have hij : i ≠ j := fin_ne_pred_mod ℓ hℓ i
  exact Finset.sum_pair hij

/-! ## Rank of the image and homology dimensions -/

omit [NeZero ℓ] in
/-- The dimension of `𝔽₂^ℓ` is `ℓ`. -/
lemma finrank_F2_fin :
    Module.finrank 𝔽₂ (Fin ℓ → 𝔽₂) = ℓ :=
  Module.finrank_fin_fun 𝔽₂

/-- The rank of the image of `∂_1` is `ℓ - 1`, by rank-nullity. -/
theorem finrank_range_differential (hℓ1 : ℓ ≥ 1) :
    Module.finrank 𝔽₂ (LinearMap.range (differential ℓ)) = ℓ - 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (differential ℓ)
  rw [finrank_F2_fin, finrank_ker_differential ℓ hℓ1] at hrn
  omega

/-! ## Homology dimensions -/

/-- `dim H_1(C_ℓ) = 1`: Since there are no 2-cells, `im(∂_2) = 0` and
`H_1 = ker(∂_1) / 0 ≅ ker(∂_1)`, which has dimension 1.
Here we express this purely in terms of the differential, since the
cycle graph has only degrees 0 and 1. -/
theorem dim_H1_cycleGraph (hℓ1 : ℓ ≥ 1) :
    Module.finrank 𝔽₂ (LinearMap.ker (differential ℓ)) = 1 :=
  finrank_ker_differential ℓ hℓ1

/-- `dim H_0(C_ℓ) = 1`: We have `ker(∂_0) = C_0 = 𝔽₂^ℓ` (since ∂_0 = 0)
and `im(∂_1)` has dimension `ℓ - 1`, so `H_0 = C_0 / im(∂_1)` has
dimension `ℓ - (ℓ - 1) = 1`. We express H_0 as the quotient
`(Fin ℓ → 𝔽₂) ⧸ im(∂_1)`. -/
theorem dim_H0_cycleGraph (hℓ1 : ℓ ≥ 1) :
    Module.finrank 𝔽₂
      ((Fin ℓ → 𝔽₂) ⧸ LinearMap.range (differential ℓ)) = 1 := by
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range (differential ℓ))
  rw [finrank_F2_fin, finrank_range_differential ℓ hℓ1] at hq
  omega

/-! ## Classical code interpretation -/

/-- The repetition code of length `ℓ`: the classical code with codeword space
`ker(∂_1) = span{(1,...,1)} ⊆ 𝔽₂^ℓ`. -/
noncomputable def repetitionCode : ClassicalCode ℓ :=
  ClassicalCode.ofParityCheck (differential ℓ)

/-- The repetition code equals `ker(∂_1)`. -/
theorem repetitionCode_eq_ker :
    (repetitionCode ℓ).code = LinearMap.ker (differential ℓ) :=
  rfl

/-- The repetition code has dimension 1. -/
theorem repetitionCode_dimension (hℓ1 : ℓ ≥ 1) :
    (repetitionCode ℓ).dimension = 1 := by
  unfold ClassicalCode.dimension
  rw [repetitionCode_eq_ker]
  exact finrank_ker_differential ℓ hℓ1

end CycleGraph
