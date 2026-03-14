import MerLeanBpqc.Remarks.Rem_1_BaseField
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.Homology.TotalComplex

/-!
# Remark 2: Notation Conventions

We establish the following notation conventions used throughout this formalization:

- `∂` (boundary/differential): In Mathlib, this is `HomologicalComplex.d i j` for a
  homological complex. For chain complexes (`ComplexShape.down ℤ`), `d i j` maps
  from degree `i` to degree `j = i - 1`.

- `δ` (coboundary/transpose of `∂`): For cochain complexes (`ComplexShape.up ℤ`),
  the differential `d i j` maps from degree `i` to degree `j = i + 1`. The transpose
  of a linear map is `Module.Dual.transpose`.

- `im` (image of a linear map): `LinearMap.range f` in Mathlib.

- `id` (identity map): `LinearMap.id` in Mathlib.

- `Tot` (total complex functor): `HomologicalComplex.total` in Mathlib.

- `Z_i(C)` (cycles) = `ker ∂_i`: In Mathlib, `HomologicalComplex.cycles C i`.

- `B_i(C)` (boundaries) = `im ∂_{i+1}`: In Mathlib, `HomologicalComplex.opcycles C i`
  captures the cokernel side; boundaries are the image of the incoming differential.

- `H_i(C)` (homology) = `Z_i(C)/B_i(C)`: In Mathlib, `HomologicalComplex.homology C i`.

- Similarly for cochains: `Z^i`, `B^i`, `H^i` use the same Mathlib API applied to
  cochain complexes (`CochainComplex`).

## Main Definitions
- `ChainComplex𝔽₂`: chain complexes of 𝔽₂-modules indexed by ℤ
- `CochainComplex𝔽₂`: cochain complexes of 𝔽₂-modules indexed by ℤ

## Key Mathlib Correspondences
- `HomologicalComplex.d` — differential (∂ or δ depending on chain/cochain)
- `HomologicalComplex.cycles` — cycles (Z_i or Z^i)
- `HomologicalComplex.homology` — homology (H_i or H^i)
- `LinearMap.range` — image of a linear map (im)
- `Module.Dual.transpose` — transpose/coboundary construction (δ = ∂ᵀ)
- `LinearMap.id` — identity map (id)
-/

open CategoryTheory

/-! ## Chain and cochain complexes over 𝔽₂ -/

/-- A chain complex of 𝔽₂-vector spaces indexed by ℤ. The differential `d i j`
maps from degree `i` to degree `j` where `j + 1 = i` (i.e., `j = i - 1`).
This corresponds to the paper's `(C_•, ∂)`. -/
abbrev ChainComplex𝔽₂ := ChainComplex (ModuleCat 𝔽₂) ℤ

/-- A cochain complex of 𝔽₂-vector spaces indexed by ℤ. The differential `d i j`
maps from degree `i` to degree `j` where `i + 1 = j`. In the paper, the coboundary
`δ^i : C^i → C^{i+1}` is the transpose of `∂_{i+1}`. -/
abbrev CochainComplex𝔽₂ := CochainComplex (ModuleCat 𝔽₂) ℤ

/-! ## Notation dictionary

The following section documents the precise correspondence between paper notation
and Mathlib definitions. We provide abbreviations for frequently used constructions.
-/

namespace NotationConventions

/-- The boundary/differential map `∂_i : C_i → C_{i-1}` in a chain complex is
`C.d i j` in Mathlib where `(ComplexShape.down ℤ).Rel i j`. -/
abbrev boundary (C : ChainComplex𝔽₂) (i j : ℤ) := C.d i j

/-- The coboundary map `δ^i : C^i → C^{i+1}` in a cochain complex is
`C.d i j` in Mathlib where `(ComplexShape.up ℤ).Rel i j`. -/
abbrev coboundary (C : CochainComplex𝔽₂) (i j : ℤ) := C.d i j

/-- The image of a linear map `f`, denoted `im f` in the paper,
corresponds to `LinearMap.range f` in Mathlib. -/
abbrev im {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module 𝔽₂ M] [Module 𝔽₂ N] (f : M →ₗ[𝔽₂] N) := LinearMap.range f

/-- The identity linear map, denoted `id` in the paper,
corresponds to `LinearMap.id` in Mathlib. -/
abbrev idMap (M : Type*) [AddCommMonoid M] [Module 𝔽₂ M] := @LinearMap.id 𝔽₂ M _ _ _

/-- The transpose (dual) of a linear map `f : M → N` is
`Module.Dual.transpose f : N* → M*`. In the paper, `δ = ∂ᵀ`. -/
abbrev transpose {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module 𝔽₂ M] [Module 𝔽₂ N] (f : M →ₗ[𝔽₂] N) := Module.Dual.transpose f

/-! ## Basic properties connecting paper notation to Mathlib -/

/-- The differential in a chain complex satisfies `∂² = 0`, i.e., `d ≫ d = 0`. -/
theorem boundary_comp_boundary (C : ChainComplex𝔽₂) (i j k : ℤ) :
    C.d i j ≫ C.d j k = 0 :=
  C.d_comp_d i j k

/-- The differential in a cochain complex satisfies `δ² = 0`, i.e., `d ≫ d = 0`. -/
theorem coboundary_comp_coboundary (C : CochainComplex𝔽₂) (i j k : ℤ) :
    C.d i j ≫ C.d j k = 0 :=
  C.d_comp_d i j k

/-- The image of a linear map equals its range: `im f = LinearMap.range f`. -/
theorem im_eq_range {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module 𝔽₂ M] [Module 𝔽₂ N] (f : M →ₗ[𝔽₂] N) :
    im f = LinearMap.range f :=
  rfl

/-- The identity map is `LinearMap.id`. -/
theorem idMap_eq_id (M : Type*) [AddCommMonoid M] [Module 𝔽₂ M] :
    idMap M = LinearMap.id :=
  rfl

end NotationConventions
