import MerLeanBpqc.Remarks.Rem_2_NotationConventions
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Definition 1: Chain Complex

A chain complex of vector spaces over `𝔽₂` is a sequence `C = (C_•, ∂)` consisting of
`𝔽₂`-vector spaces `C_i` for `i ∈ ℤ` equipped with `𝔽₂`-linear maps `∂_i : C_i → C_{i-1}`
(called differentials) satisfying `∂_{i-1} ∘ ∂_i = 0` for all `i`.

We define:
- **Cycles**: `Z_i(C) = ker ∂_i ⊂ C_i`
- **Boundaries**: `B_i(C) = im ∂_{i+1} ⊂ C_i`
- **Homology**: `H_i(C) = Z_i(C) / B_i(C)`

The chain complex type itself is `ChainComplex𝔽₂` from `Rem_2_NotationConventions`.
Here we provide concrete `Submodule`-level definitions of cycles, boundaries, and homology,
and prove `B_i(C) ⊆ Z_i(C)`.

## Main Definitions
- `ChainComplex𝔽₂.differential` — the differential `∂_i : C_i → C_{i-1}` as a linear map
- `ChainComplex𝔽₂.cycles` — cycles `Z_i(C) = ker ∂_i` as a submodule of `C_i`
- `ChainComplex𝔽₂.boundaries` — boundaries `B_i(C) = im ∂_{i+1}` as a submodule of `C_i`
- `ChainComplex𝔽₂.boundariesSubCycles` — `B_i(C)` as a submodule of `Z_i(C)`
- `ChainComplex𝔽₂.homology'` — homology `H_i(C) = Z_i(C) / B_i(C)` as a quotient module
- `ChainComplex𝔽₂.boundaries_le_cycles` — `B_i(C) ⊆ Z_i(C)`
-/

open CategoryTheory

namespace ChainComplex𝔽₂

variable (C : ChainComplex𝔽₂)

/-! ## The differential as a linear map -/

/-- The differential `∂_i : C_i → C_{i-1}` extracted as an `𝔽₂`-linear map.
We use `C.d i (i - 1)` which is the Mathlib differential for `ComplexShape.down ℤ`. -/
noncomputable def differential (i : ℤ) : ↥(C.X i) →ₗ[𝔽₂] ↥(C.X (i - 1)) :=
  (C.d i (i - 1)).hom

/-- The incoming differential `∂_{i+1} : C_{i+1} → C_i`, extracted as a linear map.
This uses `C.d (i + 1) i`, which avoids issues with `(i + 1) - 1` vs `i`. -/
noncomputable def incomingDifferential (i : ℤ) : ↥(C.X (i + 1)) →ₗ[𝔽₂] ↥(C.X i) :=
  (C.d (i + 1) i).hom

/-! ## Cycles -/

/-- The cycles `Z_i(C) = ker ∂_i`, i.e., the kernel of the differential `∂_i : C_i → C_{i-1}`,
as a submodule of `C_i`. -/
noncomputable def cycles (i : ℤ) : Submodule 𝔽₂ ↥(C.X i) :=
  LinearMap.ker (C.differential i)

/-! ## Boundaries -/

/-- The boundaries `B_i(C) = im ∂_{i+1}`, i.e., the image of `∂_{i+1} : C_{i+1} → C_i`,
as a submodule of `C_i`. -/
noncomputable def boundaries (i : ℤ) : Submodule 𝔽₂ ↥(C.X i) :=
  LinearMap.range (C.incomingDifferential i)

/-! ## Boundaries ⊆ Cycles -/

/-- The chain complex condition `∂_i ∘ ∂_{i+1} = 0` as a composition of linear maps. -/
theorem differential_comp_incomingDifferential (i : ℤ) :
    (C.differential i).comp (C.incomingDifferential i) = 0 := by
  ext x
  simp only [differential, incomingDifferential, LinearMap.comp_apply, LinearMap.zero_apply]
  have h := C.d_comp_d (i + 1) i (i - 1)
  have : (C.d (i + 1) i ≫ C.d i (i - 1)) x = 0 := by
    rw [h]; simp
  rwa [ModuleCat.comp_apply] at this

/-- `B_i(C) ⊆ Z_i(C)`: every boundary is a cycle, since `∂_i ∘ ∂_{i+1} = 0`. -/
theorem boundaries_le_cycles (i : ℤ) : C.boundaries i ≤ C.cycles i := by
  rw [boundaries, cycles]
  rw [LinearMap.range_le_ker_iff]
  exact C.differential_comp_incomingDifferential i

/-! ## Boundaries as a submodule of cycles, and homology -/

/-- `B_i(C)` viewed as a submodule of `Z_i(C)`, using the inclusion `B_i ⊆ Z_i`.
This is the preimage of `B_i(C)` under the subtype embedding `Z_i(C) ↪ C_i`. -/
noncomputable def boundariesSubCycles (i : ℤ) : Submodule 𝔽₂ ↥(C.cycles i) :=
  (C.boundaries i).comap (C.cycles i).subtype

/-- The `i`-th homology `H_i(C) = Z_i(C) / B_i(C)`. Since `B_i(C) ⊆ Z_i(C)`, the boundaries
form a submodule of the cycles, and the homology is the quotient module. -/
noncomputable def homology' (i : ℤ) : Type _ :=
  ↥(C.cycles i) ⧸ C.boundariesSubCycles i

end ChainComplex𝔽₂
