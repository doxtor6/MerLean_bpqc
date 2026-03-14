import MerLeanBpqc.Definitions.Def_2_CochainsCohomology
import MerLeanBpqc.Definitions.Def_3_ClassicalCode
import Mathlib.Algebra.Homology.Double
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Definition 4: CSS Code

A CSS (Calderbank-Shor-Steane) quantum code is defined by a chain complex (Def_1) of length
two over `𝔽₂`: `C₁ →[H_Z^T] C₀ →[H_X] C_{-1}` where `H_X ∘ H_Z^T = 0`.

The matrices `H_X ∈ 𝔽₂^{r_X × n}` and `H_Z ∈ 𝔽₂^{r_Z × n}` are the X-type and Z-type
parity check matrices, so that `C₀ = 𝔽₂^n`, `C_{-1} = 𝔽₂^{r_X}`, and `C₁ = 𝔽₂^{r_Z}`.

## Code Parameters
- `n = dim C₀`: number of physical qubits
- `k = dim H₀(C) = dim(ker H_X / im H_Z^T)`: number of logical qubits
- `d_X`: minimum Hamming weight of a nontrivial element of `H₀(C) = ker H_X / im H_Z^T`
- `d_Z`: minimum Hamming weight of a nontrivial element of `H⁰(C) = ker H_Z / im H_X^T`
- `d = min(d_X, d_Z)`: overall distance

## Main Definitions
- `CSSCode` — a CSS quantum code specified by parity check matrices `H_X` and `H_Z`
- `CSSCode.complex` — the three-term chain complex `C₁ →[H_Z^T] C₀ →[H_X] C_{-1}`
- `CSSCode.numQubits` — the number of physical qubits `n`
- `CSSCode.logicalQubits` — the number of logical qubits `k = dim H₀(C)`
- `CSSCode.dX` — the X-distance
- `CSSCode.dZ` — the Z-distance
- `CSSCode.distance` — the overall distance `d = min(d_X, d_Z)`
- `CSSCode.IsNKDCode` — the property of being an `[[n, k, d]]`-code
- `CSSCode.IsNKDXZCode` — the property of being an `[[n, k, d_X, d_Z]]`-code
-/

open CategoryTheory CategoryTheory.Limits ZeroObject

/-! ## CSS Code Structure -/

/-- A CSS (Calderbank-Shor-Steane) quantum code is defined by parity check matrices
`H_X : 𝔽₂^n → 𝔽₂^{r_X}` and `H_Z : 𝔽₂^n → 𝔽₂^{r_Z}` satisfying the CSS condition
`H_X ∘ H_Z^T = 0`. Here `H_Z^T : 𝔽₂^{r_Z} → 𝔽₂^n` is the transpose of `H_Z`,
which serves as the differential from degree 1 to degree 0 in the chain complex
`C₁ →[H_Z^T] C₀ →[H_X] C_{-1}`. -/
structure CSSCode (n rX rZ : ℕ) where
  /-- The X-type parity check matrix `H_X : 𝔽₂^n → 𝔽₂^{r_X}`. -/
  HX : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin rX → 𝔽₂)
  /-- The Z-type parity check matrix transpose `H_Z^T : 𝔽₂^{r_Z} → 𝔽₂^n`.
  This is the differential from degree 1 to degree 0 in the chain complex. -/
  HZT : (Fin rZ → 𝔽₂) →ₗ[𝔽₂] (Fin n → 𝔽₂)
  /-- The CSS condition: `H_X ∘ H_Z^T = 0`, ensuring `∂² = 0`. -/
  css_condition : HX.comp HZT = 0

namespace CSSCode

variable {n rX rZ : ℕ} (Q : CSSCode n rX rZ)

/-! ## Three-term chain complex

We construct the three-term chain complex `C₁ →[H_Z^T] C₀ →[H_X] C_{-1}` directly
as a `HomologicalComplex (ModuleCat 𝔽₂) (ComplexShape.down ℤ)`.

The objects are defined by an `if`-cascade on the degree:
- degree `0`: `ModuleCat.of 𝔽₂ (Fin n → 𝔽₂)`
- degree `1`: `ModuleCat.of 𝔽₂ (Fin rZ → 𝔽₂)`
- degree `-1`: `ModuleCat.of 𝔽₂ (Fin rX → 𝔽₂)`
- otherwise: `0`

The differentials use `eqToHom` to transport between the `if`-defined objects
and the concrete `ModuleCat.of` types, following the pattern of `HomologicalComplex.double`.
-/

-- Helper: object function for the chain complex
private noncomputable def complexObj (i : ℤ) : ModuleCat 𝔽₂ :=
  if i = 0 then ModuleCat.of 𝔽₂ (Fin n → 𝔽₂)
  else if i = 1 then ModuleCat.of 𝔽₂ (Fin rZ → 𝔽₂)
  else if i = -1 then ModuleCat.of 𝔽₂ (Fin rX → 𝔽₂)
  else 0

private lemma complexObj_zero : complexObj (n := n) (rX := rX) (rZ := rZ) 0 =
    ModuleCat.of 𝔽₂ (Fin n → 𝔽₂) :=
  if_pos rfl

private lemma complexObj_one : complexObj (n := n) (rX := rX) (rZ := rZ) 1 =
    ModuleCat.of 𝔽₂ (Fin rZ → 𝔽₂) := by
  unfold complexObj
  rw [if_neg (by omega : (1 : ℤ) ≠ 0), if_pos rfl]

private lemma complexObj_neg_one : complexObj (n := n) (rX := rX) (rZ := rZ) (-1) =
    ModuleCat.of 𝔽₂ (Fin rX → 𝔽₂) := by
  unfold complexObj
  rw [if_neg (by omega : (-1 : ℤ) ≠ 0), if_neg (by omega : (-1 : ℤ) ≠ 1), if_pos rfl]

/-- The three-term chain complex `C₁ →[H_Z^T] C₀ →[H_X] C_{-1}` associated to a CSS code.
The objects are `𝔽₂^{r_Z}` in degree 1, `𝔽₂^n` in degree 0, `𝔽₂^{r_X}` in degree -1,
and `0` elsewhere. The differentials are `H_Z^T` from degree 1 to 0 and `H_X` from
degree 0 to -1. -/
noncomputable def complex : ChainComplex𝔽₂ where
  X := complexObj (n := n) (rX := rX) (rZ := rZ)
  d i j :=
    if hi : i = 1 ∧ j = 0 then
      eqToHom (by rw [show i = 1 from hi.1]; exact complexObj_one) ≫
        ModuleCat.ofHom Q.HZT ≫
        eqToHom (by rw [show j = 0 from hi.2]; exact complexObj_zero.symm)
    else if hi : i = 0 ∧ j = -1 then
      eqToHom (by rw [show i = 0 from hi.1]; exact complexObj_zero) ≫
        ModuleCat.ofHom Q.HX ≫
        eqToHom (by rw [show j = -1 from hi.2]; exact complexObj_neg_one.symm)
    else 0
  shape i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    split_ifs with h1 h2
    · exact absurd (by omega : j + 1 = i) hij
    · exact absurd (by omega : j + 1 = i) hij
    · rfl
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.down_Rel] at hij hjk
    -- hij : j + 1 = i, hjk : k + 1 = j
    -- The only nontrivial case is i=1, j=0, k=-1
    by_cases h10 : i = 1 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h10
      have hk : k = -1 := by omega
      subst hk
      -- d(1,0) is the first branch, d(0,-1) is the second branch
      rw [dif_pos ⟨rfl, rfl⟩, dif_neg (by omega : ¬((0 : ℤ) = 1 ∧ (-1 : ℤ) = 0)),
          dif_pos ⟨rfl, rfl⟩]
      -- (eqToHom _ ≫ HZT ≫ eqToHom _) ≫ (eqToHom _ ≫ HX ≫ eqToHom _) = 0
      simp only [Category.assoc]
      -- Compose middle eqToHom's: eqToHom h.symm ≫ eqToHom h' = eqToHom (h.symm.trans h')
      rw [← Category.assoc (eqToHom _) (eqToHom _) _]
      rw [eqToHom_trans]
      simp only [eqToHom_refl, Category.id_comp]
      -- Now: eqToHom _ ≫ (HZT ≫ HX) ≫ eqToHom _ = 0
      rw [← Category.assoc (ModuleCat.ofHom Q.HZT) (ModuleCat.ofHom Q.HX) _]
      -- HZT ≫ HX = 0 from the CSS condition
      have hcomp : ModuleCat.ofHom Q.HZT ≫ ModuleCat.ofHom Q.HX = 0 := by
        rw [← ModuleCat.ofHom_comp Q.HZT Q.HX, Q.css_condition]
        rfl
      rw [hcomp]
      simp
    · -- The first differential d(i,j) is zero (not the 1→0 case)
      -- Either d(i,j) = 0 directly, or we need to show the composition is zero
      by_cases h1 : i = 1
      · -- i = 1 but j ≠ 0, contradicts hij: j + 1 = 1 implies j = 0
        omega
      · -- i ≠ 1
        rw [dif_neg (by tauto : ¬(i = 1 ∧ j = 0))]
        by_cases h0neg1 : i = 0 ∧ j = -1
        · -- d(i,j) = H_X branch, d(j,k) = d(-1, k) where k = j-1 = -2
          obtain ⟨rfl, rfl⟩ := h0neg1
          have hk : k = -2 := by omega
          subst hk
          rw [dif_pos ⟨rfl, rfl⟩]
          -- d(-1, -2): neither 1→0 nor 0→-1
          rw [dif_neg (by omega : ¬((-1 : ℤ) = 1 ∧ (-2 : ℤ) = 0)),
              dif_neg (by omega : ¬((-1 : ℤ) = 0 ∧ (-2 : ℤ) = -1))]
          simp
        · -- d(i,j) = 0, so composition is 0
          rw [dif_neg (by tauto : ¬(i = 0 ∧ j = -1))]
          simp

/-! ## Code parameters -/

/-- The number of physical qubits `n = dim C₀`. -/
def numQubits : ℕ := n

/-- The number of logical qubits `k = dim H₀(C) = dim(ker H_X / im H_Z^T)`.
The homology at degree 0 of the chain complex is `ker H_X / im H_Z^T`, which
counts the number of independent logical qubits. -/
noncomputable def logicalQubits : ℕ :=
  Module.finrank 𝔽₂ (↥(LinearMap.ker Q.HX) ⧸
    (LinearMap.range Q.HZT).comap (LinearMap.ker Q.HX).subtype)

/-- The X-distance `d_X` is the minimum Hamming weight of a representative of a
non-trivial element of `H₀(C) = ker H_X / im H_Z^T`. Equivalently, this is the
minimum Hamming weight of any vector in `ker H_X` that is not in `im H_Z^T`.
By convention (following `ClassicalCode.distance`), `d_X = 0` when the homology
is trivial (i.e., `ker H_X = im H_Z^T`). -/
noncomputable def dX : ℕ :=
  sInf {w : ℕ | ∃ x : Fin n → 𝔽₂,
    x ∈ LinearMap.ker Q.HX ∧ x ∉ LinearMap.range Q.HZT ∧ hammingWeight x = w}

/-- The Z-distance `d_Z` is the minimum Hamming weight of a representative of a
non-trivial element of `H⁰(C) = ker H_Z / im H_X^T` (Def_2). Since `H_Z = (H_Z^T)^T`
and `H_X^T` is the transpose of `H_X`, we define this using `dualMap`:
- `ker H_Z` corresponds to `ker (dualMap H_Z^T)` in the dual of `C₀`
- `im H_X^T` corresponds to `range (dualMap H_X)` in the dual of `C₀`

Over `𝔽₂` with canonical bases, `Dual(𝔽₂^n) ≅ 𝔽₂^n` via `dotProductEquiv`.
We use this identification to define the Hamming weight of dual functionals.
By convention, `d_Z = 0` when the cohomology is trivial. -/
noncomputable def dZ : ℕ :=
  sInf {w : ℕ | ∃ φ : Module.Dual 𝔽₂ (Fin n → 𝔽₂),
    φ ∈ LinearMap.ker (Q.HZT.dualMap) ∧
    φ ∉ LinearMap.range (Q.HX.dualMap) ∧
    hammingNorm ((dotProductEquiv 𝔽₂ (Fin n)).symm φ) = w}

/-- The overall distance `d = min(d_X, d_Z)`. -/
noncomputable def distance : ℕ := min Q.dX Q.dZ

/-! ## Code parameter predicates -/

/-- A CSS code is an `[[n, k, d]]`-code if it has `k` logical qubits and distance `d`. -/
def IsNKDCode (k d : ℕ) : Prop :=
  Q.logicalQubits = k ∧ Q.distance = d

/-- A CSS code is an `[[n, k, d_X, d_Z]]`-code when X- and Z-distances differ. -/
def IsNKDXZCode (k dX_val dZ_val : ℕ) : Prop :=
  Q.logicalQubits = k ∧ Q.dX = dX_val ∧ Q.dZ = dZ_val

end CSSCode
