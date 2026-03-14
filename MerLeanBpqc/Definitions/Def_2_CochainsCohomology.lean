import MerLeanBpqc.Definitions.Def_1_ChainComplex
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Definition 2: Cochains and Cohomology

Given a chain complex `C = (C_•, ∂)` (Def_1) where each `C_i` is finite-dimensional,
we identify `C^i = C_i` using the `𝔽₂`-scalar product. We define:

- **Coboundary maps**: `δ^i = (∂_{i+1})^tr : C^i → C^{i+1}`, where the transpose is
  `LinearMap.dualMap` (= `Module.Dual.transpose`).
- **Cocycles**: `Z^i(C) = ker δ^i ⊂ Dual C_i`
- **Coboundaries**: `B^i(C) = im δ^{i-1} ⊂ Dual C_i`
- **Cohomology**: `H^i(C) = Z^i(C) / B^i(C)`

The key relation `B^i(C) = (Z_i(C))^{ann}` holds, where the dual annihilator
corresponds to the orthogonal complement under the `𝔽₂`-scalar product
(using `im(A^tr) = (ker A)^⊥` for finite-dimensional `𝔽₂`-vector spaces).

This induces an isomorphism `H_i(C) ≅ H^i(C)`.

## Main Definitions
- `ChainComplex𝔽₂.coboundaryMap` — the coboundary `δ^i = (∂_{i+1})^tr`
- `ChainComplex𝔽₂.incomingCoboundaryMap` — the incoming coboundary `δ^{i-1} = (∂_i)^tr`
- `ChainComplex𝔽₂.cocycles` — cocycles `Z^i(C) = ker δ^i`
- `ChainComplex𝔽₂.coboundaries` — coboundaries `B^i(C) = im δ^{i-1}`
- `ChainComplex𝔽₂.coboundariesSubCocycles` — `B^i(C)` as a submodule of `Z^i(C)`
- `ChainComplex𝔽₂.cohomology` — cohomology `H^i(C) = Z^i(C) / B^i(C)`

## Main Theorems
- `ChainComplex𝔽₂.coboundaries_eq_dualAnnihilator_cycles` — `B^i(C) = Z_i(C)^{ann}`
- `ChainComplex𝔽₂.cocycles_eq_dualAnnihilator_boundaries` — `Z^i(C) = B_i(C)^{ann}`
- `ChainComplex𝔽₂.homologyCohomologyEquiv` — `H_i(C) ≃ₗ[𝔽₂] H^i(C)`
-/

open CategoryTheory

namespace ChainComplex𝔽₂

variable (C : ChainComplex𝔽₂)

/-! ## Coboundary maps -/

/-- The coboundary map `δ^i = (∂_{i+1})^tr : Dual C_i → Dual C_{i+1}`.
Here `∂_{i+1}` is the incoming differential `C.incomingDifferential i`, and the
transpose is `LinearMap.dualMap`. -/
noncomputable def coboundaryMap (i : ℤ) :
    Module.Dual 𝔽₂ ↥(C.X i) →ₗ[𝔽₂] Module.Dual 𝔽₂ ↥(C.X (i + 1)) :=
  (C.incomingDifferential i).dualMap

/-- The incoming coboundary `δ^{i-1} = (∂_i)^tr : Dual C_{i-1} → Dual C_i`.
This is the coboundary map landing in degree `i`, defined using `C.differential i`
to avoid index arithmetic issues. -/
noncomputable def incomingCoboundaryMap (i : ℤ) :
    Module.Dual 𝔽₂ ↥(C.X (i - 1)) →ₗ[𝔽₂] Module.Dual 𝔽₂ ↥(C.X i) :=
  (C.differential i).dualMap

/-! ## Cocycles -/

/-- The cocycles `Z^i(C) = ker δ^i`, i.e., the kernel of the coboundary map
`δ^i : Dual C_i → Dual C_{i+1}`, as a submodule of `Dual C_i`. -/
noncomputable def cocycles (i : ℤ) : Submodule 𝔽₂ (Module.Dual 𝔽₂ ↥(C.X i)) :=
  LinearMap.ker (C.coboundaryMap i)

/-! ## Coboundaries -/

/-- The coboundaries `B^i(C) = im δ^{i-1}`, i.e., the image (range) of the
incoming coboundary `δ^{i-1} : Dual C_{i-1} → Dual C_i`,
as a submodule of `Dual C_i`. -/
noncomputable def coboundaries (i : ℤ) : Submodule 𝔽₂ (Module.Dual 𝔽₂ ↥(C.X i)) :=
  LinearMap.range (C.incomingCoboundaryMap i)

/-! ## Coboundary composition δ² = 0 -/

/-- The coboundary maps satisfy `δ^i ∘ δ^{i-1} = 0`, dual to `∂_i ∘ ∂_{i+1} = 0`. -/
theorem coboundaryMap_comp_incomingCoboundaryMap (i : ℤ) :
    (C.coboundaryMap i).comp (C.incomingCoboundaryMap i) = 0 := by
  simp only [coboundaryMap, incomingCoboundaryMap]
  rw [LinearMap.dualMap_comp_dualMap]
  have h := C.differential_comp_incomingDifferential i
  rw [h]
  exact map_zero _

/-! ## Coboundaries ⊆ Cocycles -/

/-- `B^i(C) ⊆ Z^i(C)`: every coboundary is a cocycle, since `δ^i ∘ δ^{i-1} = 0`. -/
theorem coboundaries_le_cocycles (i : ℤ) : C.coboundaries i ≤ C.cocycles i := by
  rw [coboundaries, cocycles]
  rw [LinearMap.range_le_ker_iff]
  exact C.coboundaryMap_comp_incomingCoboundaryMap i

/-! ## Coboundaries as a submodule of cocycles, and cohomology -/

/-- `B^i(C)` viewed as a submodule of `Z^i(C)`, using the inclusion `B^i ⊆ Z^i`.
This is the preimage of `B^i(C)` under the subtype embedding `Z^i(C) ↪ Dual C_i`. -/
noncomputable def coboundariesSubCocycles (i : ℤ) : Submodule 𝔽₂ ↥(C.cocycles i) :=
  (C.coboundaries i).comap (C.cocycles i).subtype

/-- The `i`-th cohomology `H^i(C) = Z^i(C) / B^i(C)`. Since `B^i(C) ⊆ Z^i(C)`,
the coboundaries form a submodule of the cocycles, and the cohomology is the
quotient module. -/
noncomputable abbrev cohomology (i : ℤ) : Type :=
  ↥(C.cocycles i) ⧸ C.coboundariesSubCocycles i

/-! ## Key relations: dual annihilator characterizations

Over a field, the dual annihilator satisfies `im(f^tr) = (ker f)^{ann}` and
`ker(f^tr) = (im f)^{ann}`. These give the fundamental identities
`B^i = (Z_i)^{ann}` and `Z^i = (B_i)^{ann}`. -/

/-- The cocycles are the dual annihilator of the boundaries:
`Z^i(C) = ker δ^i = (im ∂_{i+1})^{ann} = B_i(C)^{ann}`.
This follows from `ker(f^tr) = (im f)^{ann}` (which holds over any commutative ring). -/
theorem cocycles_eq_dualAnnihilator_boundaries (i : ℤ) :
    C.cocycles i = (C.boundaries i).dualAnnihilator := by
  simp only [cocycles, coboundaryMap, boundaries]
  exact (C.incomingDifferential i).ker_dualMap_eq_dualAnnihilator_range

/-- The coboundaries are the dual annihilator of the cycles:
`B^i(C) = im δ^{i-1} = (ker ∂_i)^{ann} = Z_i(C)^{ann}`.
This follows from `im(f^tr) = (ker f)^{ann}` for vector spaces over a field. -/
theorem coboundaries_eq_dualAnnihilator_cycles (i : ℤ)
    [FiniteDimensional 𝔽₂ ↥(C.X i)] [FiniteDimensional 𝔽₂ ↥(C.X (i - 1))] :
    C.coboundaries i = (C.cycles i).dualAnnihilator := by
  simp only [coboundaries, incomingCoboundaryMap, cycles, differential]
  exact LinearMap.range_dualMap_eq_dualAnnihilator_ker _

/-! ## Homology-cohomology isomorphism

The isomorphism `H_i(C) ≅ H^i(C)` uses the canonical pairing between a
finite-dimensional vector space and its dual. Over `𝔽₂`, identifying `C^i = C_i`
via the scalar product, the dual annihilator gives the orthogonal complement,
and the quotient `Z_i / B_i` is canonically isomorphic to `Z^i / B^i`.

The proof proceeds by showing both quotients have the same `finrank`, using
the dual annihilator dimension formula: `dim W + dim W^{ann} = dim V`. -/

/-- The `finrank` of `boundariesSubCycles` equals the `finrank` of `boundaries`,
since the comap of boundaries under the cycles inclusion maps to `cycles ⊓ boundaries = boundaries`
(as `B_i ⊆ Z_i`). -/
lemma finrank_boundariesSubCycles_eq (i : ℤ) [FiniteDimensional 𝔽₂ ↥(C.X i)]
    [FiniteDimensional 𝔽₂ ↥(C.X (i + 1))] :
    Module.finrank 𝔽₂ ↥(C.boundariesSubCycles i) = Module.finrank 𝔽₂ ↥(C.boundaries i) := by
  have h_le := C.boundaries_le_cycles i
  rw [boundariesSubCycles]
  -- finrank (comap subtype B) = finrank (map subtype (comap subtype B)) by finrank_map_subtype_eq
  rw [← Submodule.finrank_map_subtype_eq (C.cycles i)]
  -- map subtype (comap subtype B) = cycles ⊓ B
  rw [Submodule.map_comap_subtype]
  -- cycles ⊓ B = B since B ≤ cycles
  rw [inf_eq_right.mpr h_le]

/-- The `finrank` of `coboundariesSubCocycles` equals the `finrank` of `coboundaries`,
since `B^i ⊆ Z^i`. -/
lemma finrank_coboundariesSubCocycles_eq (i : ℤ)
    [FiniteDimensional 𝔽₂ ↥(C.X i)] [FiniteDimensional 𝔽₂ ↥(C.X (i - 1))]
    [FiniteDimensional 𝔽₂ ↥(C.X (i + 1))] :
    Module.finrank 𝔽₂ ↥(C.coboundariesSubCocycles i) =
    Module.finrank 𝔽₂ ↥(C.coboundaries i) := by
  have h_le := C.coboundaries_le_cocycles i
  rw [coboundariesSubCocycles]
  rw [← Submodule.finrank_map_subtype_eq (C.cocycles i)]
  rw [Submodule.map_comap_subtype]
  rw [inf_eq_right.mpr h_le]

/-- The homology `H_i(C) = Z_i/B_i` and cohomology `H^i(C) = Z^i/B^i` have the
same `finrank`. This follows from the dual annihilator dimension formula:
`dim W + dim W^{ann} = dim V`. -/
-- Helper: finrank of cocycles equals finrank of dualAnnihilator of boundaries
private lemma finrank_cocycles_eq (i : ℤ) :
    Module.finrank 𝔽₂ ↥(C.cocycles i) =
    Module.finrank 𝔽₂ ↥((C.boundaries i).dualAnnihilator) := by
  rw [C.cocycles_eq_dualAnnihilator_boundaries i]

-- Helper: finrank of coboundaries equals finrank of dualAnnihilator of cycles
private lemma finrank_coboundaries_eq (i : ℤ)
    [FiniteDimensional 𝔽₂ ↥(C.X i)] [FiniteDimensional 𝔽₂ ↥(C.X (i - 1))] :
    Module.finrank 𝔽₂ ↥(C.coboundaries i) =
    Module.finrank 𝔽₂ ↥((C.cycles i).dualAnnihilator) := by
  rw [C.coboundaries_eq_dualAnnihilator_cycles i]

theorem finrank_homology_eq_finrank_cohomology (i : ℤ)
    [FiniteDimensional 𝔽₂ ↥(C.X i)] [FiniteDimensional 𝔽₂ ↥(C.X (i - 1))]
    [FiniteDimensional 𝔽₂ ↥(C.X (i + 1))] :
    Module.finrank 𝔽₂ (↥(C.cycles i) ⧸ C.boundariesSubCycles i) =
    Module.finrank 𝔽₂ (↥(C.cocycles i) ⧸ C.coboundariesSubCocycles i) := by
  -- Use finrank (M ⧸ N) + finrank N = finrank M
  have hH := Submodule.finrank_quotient_add_finrank (C.boundariesSubCycles i)
  have hCo := Submodule.finrank_quotient_add_finrank (C.coboundariesSubCocycles i)
  -- Replace finranks of sub-submodules by finranks of actual submodules
  rw [C.finrank_boundariesSubCycles_eq i] at hH
  rw [C.finrank_coboundariesSubCocycles_eq i] at hCo
  -- Use finrank W + finrank W^{ann} = finrank V for boundaries and cycles
  have hB := Subspace.finrank_add_finrank_dualAnnihilator_eq (C.boundaries i)
  have hZ := Subspace.finrank_add_finrank_dualAnnihilator_eq (C.cycles i)
  -- Replace cocycles/coboundaries finranks with annihilator finranks
  have hCocycles := C.finrank_cocycles_eq i
  have hCoboundaries := C.finrank_coboundaries_eq i
  omega

/-- The isomorphism `H_i(C) ≃ₗ[𝔽₂] H^i(C)` between homology and cohomology.
This follows from the fact that both are finite-dimensional vector spaces of the
same dimension over `𝔽₂`, using the dual annihilator dimension formula. -/
noncomputable def homologyCohomologyEquiv (i : ℤ)
    [FiniteDimensional 𝔽₂ ↥(C.X i)] [FiniteDimensional 𝔽₂ ↥(C.X (i - 1))]
    [FiniteDimensional 𝔽₂ ↥(C.X (i + 1))] :
    (↥(C.cycles i) ⧸ C.boundariesSubCycles i) ≃ₗ[𝔽₂]
    (↥(C.cocycles i) ⧸ C.coboundariesSubCocycles i) :=
  LinearEquiv.ofFinrankEq _ _ (C.finrank_homology_eq_finrank_cohomology i)

end ChainComplex𝔽₂
