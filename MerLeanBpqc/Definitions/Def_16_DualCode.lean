import MerLeanBpqc.Definitions.Def_3_ClassicalCode
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Definition 16: Dual Code

Given a classical `[n, k, d]`-code `L ⊆ 𝔽₂^n` (Def_3), the dual code is
`L⊥ = {w ∈ 𝔽₂^n : ⟨w, c⟩ = 0 for all c ∈ L}`, where `⟨w, c⟩ = Σᵢ wᵢcᵢ`
is the standard `𝔽₂`-dot product.

## Main Results
- `dualCode` — the dual code `L⊥` as a `ClassicalCode`
- `mem_dualCode_iff` — membership characterization via dot product
- `mem_dualCode_iff'` — symmetric characterization (commutativity of dot product)
- `dualCodeEquivDualAnnihilator` — `L⊥ ≃ₗ L.code.dualAnnihilator`
- `dimension_dualCode` — `dim L⊥ = n - dim L`
- `dualCode_isNKDCode` — `L⊥` is an `[n, n-k, d_{L⊥}]`-code
-/

open scoped Matrix
open ClassicalCode

namespace ClassicalCode

variable {n : ℕ} (𝒞 : ClassicalCode n)

/-! ## Dual Code Definition -/

/-- The dual code `L⊥ = {w ∈ 𝔽₂^n : ⟨w, c⟩ = 0 for all c ∈ L}`, where `⟨w, c⟩ = Σᵢ wᵢ cᵢ`
is the standard `𝔽₂`-inner product. This is defined as the pullback of the dual annihilator
`L.code.dualAnnihilator ⊆ Dual(𝔽₂^n)` through the canonical isomorphism
`dotProductEquiv : 𝔽₂^n ≃ₗ Dual(𝔽₂^n)` given by `v ↦ (w ↦ v ⬝ᵥ w)`. -/
noncomputable def dualCode : ClassicalCode n where
  code := 𝒞.code.dualAnnihilator.comap (dotProductEquiv 𝔽₂ (Fin n)).toLinearMap

/-! ## Membership Characterization -/

/-- Membership in the dual code: `w ∈ L⊥` iff `w ⬝ᵥ c = 0` for all `c ∈ L`. -/
theorem mem_dualCode_iff (w : Fin n → 𝔽₂) :
    w ∈ (dualCode 𝒞).code ↔ ∀ c ∈ 𝒞.code, dotProduct w c = 0 := by
  simp only [dualCode, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  constructor
  · intro hw c hc
    have := hw c hc
    simp [dotProductEquiv] at this
    exact this
  · intro hw c hc
    simp [dotProductEquiv]
    exact hw c hc

/-- The dual code is symmetric: `w ∈ L⊥` iff `c ⬝ᵥ w = 0` for all `c ∈ L`.
Over `𝔽₂`, `w ⬝ᵥ c = c ⬝ᵥ w` since `𝔽₂` is commutative. -/
theorem mem_dualCode_iff' (w : Fin n → 𝔽₂) :
    w ∈ (dualCode 𝒞).code ↔ ∀ c ∈ 𝒞.code, dotProduct c w = 0 := by
  rw [mem_dualCode_iff]
  constructor <;> intro h c hc
  · rw [dotProduct_comm]; exact h c hc
  · rw [dotProduct_comm]; exact h c hc

/-! ## Equivalence with Dual Annihilator -/

/-- The linear equivalence between `↥(dualCode 𝒞).code` and `↥(𝒞.code.dualAnnihilator)`,
obtained from `dotProductEquiv`. Since `dualCode.code = dualAnnihilator.comap (dotProductEquiv)`,
the restriction of `dotProductEquiv` gives the equivalence. -/
noncomputable def dualCodeEquivDualAnnihilator :
    ↥(dualCode 𝒞).code ≃ₗ[𝔽₂] ↥(𝒞.code.dualAnnihilator) := by
  have heq : (dualCode 𝒞).code =
      Submodule.comap (dotProductEquiv 𝔽₂ (Fin n)).toLinearMap 𝒞.code.dualAnnihilator := by
    rfl
  rw [heq, Submodule.comap_equiv_eq_map_symm]
  exact ((dotProductEquiv 𝔽₂ (Fin n)).symm.submoduleMap 𝒞.code.dualAnnihilator).symm

/-! ## Dimension Formula -/

/-- The dimension of the dual code: `dim L⊥ = n - dim L`. This follows from the dual annihilator
dimension formula `dim L + dim L.dualAnnihilator = dim 𝔽₂^n = n` and the fact that
`dotProductEquiv` preserves dimension. -/
theorem dimension_dualCode [FiniteDimensional 𝔽₂ (Fin n → 𝔽₂)] :
    (dualCode 𝒞).dimension = n - 𝒞.dimension := by
  unfold dimension
  -- Use the equivalence to transfer finrank
  have hfr : Module.finrank 𝔽₂ ↥(dualCode 𝒞).code =
      Module.finrank 𝔽₂ ↥𝒞.code.dualAnnihilator :=
    LinearEquiv.finrank_eq (dualCodeEquivDualAnnihilator 𝒞)
  rw [hfr]
  have hdim := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (K := 𝔽₂) (V := Fin n → 𝔽₂) 𝒞.code
  have hfin : Module.finrank 𝔽₂ (Fin n → 𝔽₂) = n := Module.finrank_fin_fun 𝔽₂
  omega

/-! ## Dual Code is an [n, n-k, d_{L⊥}]-code -/

/-- The dual code is an `[n, n-k, d_{L⊥}]`-code, where `k = dim L` and `d_{L⊥}` is the
minimum distance of the dual code. -/
theorem dualCode_isNKDCode [FiniteDimensional 𝔽₂ (Fin n → 𝔽₂)] :
    (dualCode 𝒞).IsNKDCode (n - 𝒞.dimension) (dualCode 𝒞).distance := by
  exact ⟨dimension_dualCode 𝒞, rfl⟩

end ClassicalCode
