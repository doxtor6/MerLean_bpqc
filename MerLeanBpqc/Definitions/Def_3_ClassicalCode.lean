import MerLeanBpqc.Definitions.Def_1_ChainComplex
import MerLeanBpqc.Remarks.Rem_3_ExpandingMatrixDefinition
import Mathlib.Algebra.Homology.Double
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Definition 3: Classical Code

A classical, linear, binary code `𝒞` is a subspace of `𝔽₂^n`. The number of encodable bits
is `k = dim 𝒞`. The distance `d` is the minimum Hamming weight of any non-zero element of `𝒞`
(with the convention `d = 0` if `𝒞 = {0}`). We call such a code an `[n, k, d]`-code.

A code can be specified as `𝒞 = ker ∂^C` where `∂^C : 𝔽₂^n → 𝔽₂^m` is the parity check
matrix (an `𝔽₂`-linear map), viewing the code as a two-term chain complex
`C = (C₁ →[∂^C] C₀)` with `C₁ = 𝔽₂^n` and `C₀ = 𝔽₂^m`, so `𝒞 = Z₁(C) = ker ∂^C`.

## Main Definitions
- `ClassicalCode` — a classical linear binary code: a subspace of `𝔽₂^n`
- `ClassicalCode.dimension` — the number of encodable bits `k = dim 𝒞`
- `ClassicalCode.distance` — the minimum Hamming weight of nonzero codewords
- `ClassicalCode.IsNKDCode` — the property of being an `[n, k, d]`-code
- `ClassicalCode.ofParityCheck` — construct a code from a parity check linear map
- `ClassicalCode.parityCheckComplex` — the two-term chain complex `C₁ →[∂^C] C₀`
- `ClassicalCode.code_eq_ker` — `𝒞 = ker ∂^C` (definitional)
- `ClassicalCode.code_eq_cycles_map` — `𝒞 = Z₁(C)` via the canonical iso
-/

open CategoryTheory

/-! ## Classical code as a subspace of 𝔽₂^n -/

/-- A classical, linear, binary code is a subspace `𝒞 ⊆ 𝔽₂^n`. -/
structure ClassicalCode (n : ℕ) where
  /-- The code as a submodule of `𝔽₂^n`. -/
  code : Submodule 𝔽₂ (Fin n → 𝔽₂)

namespace ClassicalCode

variable {n : ℕ} (𝒞 : ClassicalCode n)

/-! ## Code parameters -/

/-- The number of encodable bits `k = dim 𝒞`. -/
noncomputable def dimension : ℕ :=
  Module.finrank 𝔽₂ 𝒞.code

/-- The distance of a code `𝒞`: the minimum Hamming weight of any non-zero codeword.
By convention, `d = 0` when `𝒞 = {0}` (the trivial code). We use `sInf` on `ℕ`,
where `sInf ∅ = 0` gives the correct convention for the trivial code. -/
noncomputable def distance : ℕ :=
  sInf {w : ℕ | ∃ x : Fin n → 𝔽₂, x ∈ 𝒞.code ∧ x ≠ 0 ∧ hammingWeight x = w}

/-- A code is an `[n, k, d]`-code if it has dimension `k` and distance `d`. -/
def IsNKDCode (k d : ℕ) : Prop :=
  𝒞.dimension = k ∧ 𝒞.distance = d

/-! ## Code from parity check matrix -/

/-- Construct a classical code from a parity check linear map `∂^C : 𝔽₂^n → 𝔽₂^m`.
The code is `ker ∂^C`. -/
def ofParityCheck {m : ℕ} (parityCheck : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) :
    ClassicalCode n where
  code := LinearMap.ker parityCheck

/-- The code `ker parityCheck` is definitionally the kernel of the parity check map. -/
theorem code_eq_ker {m : ℕ}
    (parityCheck : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) :
    (ofParityCheck parityCheck).code = LinearMap.ker parityCheck :=
  rfl

/-! ## Two-term chain complex from parity check -/

/-- The two-term chain complex `C = (C₁ →[∂^C] C₀)` associated to a parity check
linear map `∂^C : 𝔽₂^n → 𝔽₂^m`. This uses `HomologicalComplex.double` from Mathlib
with `C₁ = ModuleCat.of 𝔽₂ (Fin n → 𝔽₂)` in degree `1` and
`C₀ = ModuleCat.of 𝔽₂ (Fin m → 𝔽₂)` in degree `0`, with the differential being `∂^C`. -/
noncomputable def parityCheckComplex {m : ℕ}
    (parityCheck : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) : ChainComplex𝔽₂ :=
  HomologicalComplex.double
    (ModuleCat.ofHom parityCheck :
      ModuleCat.of 𝔽₂ (Fin n → 𝔽₂) ⟶ ModuleCat.of 𝔽₂ (Fin m → 𝔽₂))
    (ComplexShape.down_mk (1 : ℤ) (0 : ℤ) (by omega))

/-! ## Code equals cycles of the chain complex -/

-- Notation for the morphism used in parityCheckComplex
private noncomputable abbrev pcMor {n m : ℕ}
    (parityCheck : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) :
    ModuleCat.of 𝔽₂ (Fin n → 𝔽₂) ⟶ ModuleCat.of 𝔽₂ (Fin m → 𝔽₂) :=
  ModuleCat.ofHom parityCheck

private noncomputable abbrev pcRel : (ComplexShape.down ℤ).Rel 1 0 :=
  ComplexShape.down_mk (1 : ℤ) (0 : ℤ) (by omega)

/-- The isomorphism `C.X 1 ≅ ModuleCat.of 𝔽₂ (Fin n → 𝔽₂)` for the parity check complex. -/
noncomputable def parityCheckComplexXIso₁ {m : ℕ}
    (parityCheck : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) :
    (parityCheckComplex parityCheck).X 1 ≅ ModuleCat.of 𝔽₂ (Fin n → 𝔽₂) :=
  HomologicalComplex.doubleXIso₀ (pcMor parityCheck) pcRel

/-- The code `𝒞 = ker ∂^C` equals the image of the cycles `Z₁(C)` under the canonical
isomorphism `C.X 1 ≅ 𝔽₂^n`. This formalizes `𝒞 = Z₁(C) = ker ∂^C`. -/
-- Helper: the differential of the double complex factors through the isos
private lemma parityCheckComplex_d_eq {m : ℕ}
    (parityCheck : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) :
    (parityCheckComplex parityCheck).d 1 0 =
    (parityCheckComplexXIso₁ parityCheck).hom ≫ pcMor parityCheck ≫
    (HomologicalComplex.doubleXIso₁ (pcMor parityCheck) pcRel (by omega)).inv := by
  exact HomologicalComplex.double_d (pcMor parityCheck) pcRel (by omega)

theorem code_eq_cycles_map {m : ℕ}
    (parityCheck : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) :
    (ofParityCheck parityCheck).code =
    ((parityCheckComplex parityCheck).cycles 1).map
      (parityCheckComplexXIso₁ parityCheck).hom.hom := by
  set C := parityCheckComplex parityCheck
  set φ := parityCheckComplexXIso₁ parityCheck
  set ψ := HomologicalComplex.doubleXIso₁ (pcMor parityCheck) pcRel (by omega : (1 : ℤ) ≠ 0)
  have hd := parityCheckComplex_d_eq parityCheck
  ext x
  simp only [ofParityCheck, Submodule.mem_map]
  simp only [ChainComplex𝔽₂.cycles, ChainComplex𝔽₂.differential]
  constructor
  · intro hx
    refine ⟨φ.inv.hom x, ?_, ?_⟩
    · -- Show φ.inv x ∈ ker (C.d 1 (1-1)).hom
      simp only [LinearMap.mem_ker]
      rw [show (1 : ℤ) - 1 = 0 from by omega]
      change (C.d 1 0).hom (φ.inv.hom x) = 0
      rw [hd, ModuleCat.comp_apply, ModuleCat.comp_apply]
      have hid : φ.hom.hom (φ.inv.hom x) = x := by
        change (φ.inv ≫ φ.hom).hom x = x
        rw [φ.inv_hom_id]; rfl
      rw [hid]
      have hx' := LinearMap.mem_ker.mp hx
      change ψ.inv.hom (parityCheck x) = 0
      rw [hx', map_zero]
    · change (φ.inv ≫ φ.hom).hom x = x
      rw [φ.inv_hom_id]; rfl
  · rintro ⟨y, hy, rfl⟩
    simp only [LinearMap.mem_ker] at hy ⊢
    rw [show (1 : ℤ) - 1 = 0 from by omega] at hy
    have hdy : (C.d 1 0).hom y = 0 := hy
    rw [hd, ModuleCat.comp_apply, ModuleCat.comp_apply] at hdy
    -- hdy now says ψ.inv (pcMor(φ.hom y)) = 0
    -- Since ψ.inv is an iso, it's injective, so pcMor(φ.hom y) = 0
    -- which means parityCheck (φ.hom y) = 0
    have hinj : Function.Injective (ψ.inv.hom) := by
      intro a b hab
      have h1 : ψ.hom.hom (ψ.inv.hom a) = ψ.hom.hom (ψ.inv.hom b) := congrArg _ hab
      have h2 : ∀ z, ψ.hom.hom (ψ.inv.hom z) = z := fun z => by
        change (ψ.inv ≫ ψ.hom).hom z = z; rw [ψ.inv_hom_id]; rfl
      rwa [h2 a, h2 b] at h1
    -- The hypothesis says ψ.inv applied to something equals 0
    -- Apply injectivity: that something = 0
    have h0 : ψ.inv.hom ((pcMor parityCheck).hom (φ.hom.hom y)) = ψ.inv.hom 0 := by
      rw [map_zero]; exact hdy
    have h1 := hinj h0
    -- h1 : (pcMor parityCheck).hom (φ.hom.hom y) = 0
    -- which is parityCheck (φ.hom.hom y) = 0
    exact h1

end ClassicalCode
