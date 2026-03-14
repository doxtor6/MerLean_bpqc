import MerLeanBpqc.Remarks.Rem_1_BaseField
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Matrix.Mul

/-!
# Remark 3: Expanding Matrix Definition

A matrix `A ∈ 𝔽₂^{m × n}` is called `(α, β)`-expanding, where `α ∈ (0, 1]` and `β > 0`,
if for any `x ∈ 𝔽₂^n` with `|x| ≤ α n` we have `|Ax| ≥ β |x|`, where `|·|` denotes
the Hamming weight.

## Main Definitions
- `hammingWeight`: abbreviation for `hammingNorm` applied to vectors over `𝔽₂`
- `IsExpanding`: the `(α, β)`-expanding property for a matrix over `𝔽₂`
-/

open Matrix

/-! ## Hamming weight -/

/-- The Hamming weight of a vector `x : Fin n → 𝔽₂`, i.e., the number of nonzero entries.
This is `hammingNorm` from Mathlib specialized to vectors over `𝔽₂`. -/
abbrev hammingWeight {n : ℕ} (x : Fin n → 𝔽₂) : ℕ := hammingNorm x

/-! ## Expanding matrix definition -/

/-- A matrix `A ∈ 𝔽₂^{m × n}` is `(α, β)`-expanding, where `α ∈ (0, 1]` and `β > 0`,
if for any vector `x ∈ 𝔽₂^n` with Hamming weight `|x| ≤ α · n`, we have
`|A x| ≥ β · |x|`, where `|·|` denotes the Hamming weight.

The parameters `α` and `β` are real numbers with `0 < α ≤ 1` and `0 < β`. -/
def IsExpanding {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝔽₂) (α β : ℝ) : Prop :=
  0 < α ∧ α ≤ 1 ∧ 0 < β ∧
  ∀ x : Fin n → 𝔽₂, (hammingWeight x : ℝ) ≤ α * n →
    (hammingWeight (A.mulVec x) : ℝ) ≥ β * (hammingWeight x : ℝ)
