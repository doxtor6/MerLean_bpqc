import MerLeanBpqc.Definitions.Def_12_FiberBundleDoubleComplex
import MerLeanBpqc.Theorems.Thm_3_FiberBundleHomology
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Definition 13: Augmented Complex

A 1-complex `F = (F₁ →[∂^F] F₀)` is augmented if there is a linear map `ε : F₀ → 𝔽₂`
such that `ε ∘ ∂^F = 0`. The augmentation gives a chain map `π : F → 𝔽₂` with
`π₀ = ε` and `π₁ = 0`.

Given a fiber bundle complex `B ⊗_φ F`, the augmentation induces:
- A chain map `π_* : Tot(B ⊠_φ F)_n → B_n` sending `b ⊗ f ↦ π_q(f) · b`
- A cochain map `π^* : B*_n → Tot(B ⊠_φ F)*_n` as the dual of `π_*`

## Main Definitions
- `AugmentedComplex` — augmentation structure on a 1-complex
- `augMap` — the augmentation map at each fiber degree
- `piStarSummandLin` — the linear map `b ⊗ f ↦ π_q(f) · b`
- `piStarMor` — the chain map `π_*` assembled from summands
- `baseDiff` — the base differential
- `cochainPiStar` — the cochain map `π^*` (dual of `π_*`)
-/

open CategoryTheory LinearMap
open scoped TensorProduct

noncomputable section

namespace FiberBundle

variable {n₁ m₁ n₂ m₂ : ℕ}

/-! ## Augmented Complex -/

/-- A complex `F = (F₁ →[∂^F] F₀)` is augmented if there is a linear map
`ε : F₀ → 𝔽₂` such that `ε ∘ ∂^F = 0`. -/
structure AugmentedComplex (n₂ m₂ : ℕ)
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂)) where
  /-- The augmentation map `ε : F₀ → 𝔽₂`. -/
  ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂
  /-- The chain map condition: `ε ∘ ∂^F = 0`. -/
  comp_eq_zero : ε.comp dF = 0

/-! ## Augmentation map at each degree -/

/-- The augmentation map at fiber degree `q`:
- At `q = 0`: `ε : F₀ → 𝔽₂` (= `π₀`)
- At `q = 1`: `0 : F₁ → 𝔽₂` (= `π₁`, since `π₁ = 0`)
- At other `q`: `0` (spaces are trivial) -/
def augMap (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (aug : AugmentedComplex n₂ m₂ dF) (q : ℤ) :
    (Fin (fiberSize n₂ m₂ q) → 𝔽₂) →ₗ[𝔽₂] 𝔽₂ :=
  if hq : q = 0 then hq ▸ aug.ε
  else 0

@[simp]
lemma augMap_zero (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (aug : AugmentedComplex n₂ m₂ dF) :
    augMap dF aug 0 = aug.ε := by
  simp [augMap]

@[simp]
lemma augMap_one (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (aug : AugmentedComplex n₂ m₂ dF) :
    augMap dF aug 1 = 0 := by
  simp [augMap]

/-! ## The π_* map on summands -/

/-- The linear map underlying `π_*` on the `(p, q)`-summand:
`b ⊗ f ↦ π_q(f) · b`. Uses `TensorProduct.rid` to identify `M ⊗ 𝔽₂ ≅ M`
after applying the augmentation. -/
def piStarSummandLin (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (aug : AugmentedComplex n₂ m₂ dF) (p q : ℤ) :
    (Fin (baseSize n₁ m₁ p) → 𝔽₂) ⊗[𝔽₂] (Fin (fiberSize n₂ m₂ q) → 𝔽₂) →ₗ[𝔽₂]
    (Fin (baseSize n₁ m₁ p) → 𝔽₂) :=
  (TensorProduct.rid 𝔽₂ (Fin (baseSize n₁ m₁ p) → 𝔽₂)).toLinearMap.comp
    (LinearMap.lTensor _ (augMap dF aug q))

lemma piStarSummandLin_tmul_q0
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (aug : AugmentedComplex n₂ m₂ dF) (p : ℤ)
    (b : Fin (baseSize n₁ m₁ p) → 𝔽₂)
    (f : Fin (fiberSize n₂ m₂ 0) → 𝔽₂) :
    piStarSummandLin (n₁ := n₁) (m₁ := m₁) dF aug p 0 (b ⊗ₜ f) = aug.ε f • b := by
  simp [piStarSummandLin, augMap_zero, lTensor_tmul, TensorProduct.rid_tmul]; rfl

lemma piStarSummandLin_q_ne_zero
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (aug : AugmentedComplex n₂ m₂ dF) (p q : ℤ) (hq : q ≠ 0) :
    piStarSummandLin (n₁ := n₁) (m₁ := m₁) dF aug p q = 0 := by
  simp [piStarSummandLin, augMap, dif_neg hq, LinearMap.comp_zero]

/-! ## The (p,q)-component as a ModuleCat morphism -/

/-- The `(p, q)`-component of `π_*` as a `ModuleCat` morphism, targeting
`𝔽₂^{baseSize(n)}` with type transport from the proof `p + q = n`.
When `q = 0`, `p = n` and this sends `b ⊗ f ↦ ε(f) · b`.
When `q ≠ 0`, this is zero. -/
def piStarSummandMor (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (aug : AugmentedComplex n₂ m₂ dF) (n : ℤ)
    (p q : ℤ) (hpq : p + q = n) :
    fbObj n₁ m₁ n₂ m₂ (p, q) ⟶ ModuleCat.of 𝔽₂ (Fin (baseSize n₁ m₁ n) → 𝔽₂) :=
  if hq : q = 0 then
    ModuleCat.ofHom (
      (LinearMap.funLeft 𝔽₂ 𝔽₂ (Fin.cast (by subst hq; congr 1; omega))).comp
        (piStarSummandLin (n₁ := n₁) (m₁ := m₁) dF aug p q))
  else
    0

/-! ## The chain map π_* -/

/-- The chain map `π_* : Tot(B ⊠_φ F)_n → 𝔽₂^{baseSize(n)}` at degree `n`,
assembled from the summand maps using `totalDesc`. -/
def piStarMor
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (aug : AugmentedComplex n₂ m₂ dF) (n : ℤ) :
    (fiberBundleDoubleComplex dB dF φ).totalComplex.X n ⟶
      ModuleCat.of 𝔽₂ (Fin (baseSize n₁ m₁ n) → 𝔽₂) :=
  (fiberBundleDoubleComplex dB dF φ).totalDesc
    (fun p q hpq => piStarSummandMor dF aug n p q (by
      change p + q = n
      simp [ComplexShape.π] at hpq
      exact hpq))

/-! ## Base differential -/

/-- The base differential at degrees `(n, n')`: `dB` when `n = 1, n' = 0`, `0` otherwise. -/
def baseDiff (n₁ m₁ : ℕ) (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (n n' : ℤ) :
    (Fin (baseSize n₁ m₁ n) → 𝔽₂) →ₗ[𝔽₂] (Fin (baseSize n₁ m₁ n') → 𝔽₂) :=
  if hn : n = 1 ∧ n' = 0 then hn.1 ▸ hn.2 ▸ dB
  else 0

/-! ## Augmentation compatibility with connection -/

/-- The augmentation `ε` is compatible with a chain automorphism `ψ` if `ε ∘ α₀ = ε`.
This follows from `ActsAsIdOnHomology`: since `α₀(y) - y ∈ im(dF)` and `ε ∘ dF = 0`,
we get `ε(α₀(y)) = ε(y)`. -/
lemma aug_comp_α₀_eq
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (aug : AugmentedComplex n₂ m₂ dF)
    (ψ : ChainAutomorphism n₂ m₂ dF)
    (hψ : ψ.ActsAsIdOnHomology dF) :
    aug.ε.comp ψ.α₀.toLinearMap = aug.ε := by
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  have h := hψ.deg0 y
  rw [LinearMap.mem_range] at h
  obtain ⟨z, hz⟩ := h
  have hsub : aug.ε (ψ.α₀ y - y) = 0 := by
    rw [← hz]
    have := LinearMap.ext_iff.mp aug.comp_eq_zero z
    simp at this
    exact this
  rw [map_sub] at hsub
  exact sub_eq_zero.mp hsub

/-- The augmentation is preserved by all connection automorphisms in the support of `∂^B`,
assuming the connection acts as identity on homology. -/
lemma aug_preserved_by_connection
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (aug : AugmentedComplex n₂ m₂ dF)
    (hφ : ActsAsIdentityOnHomology dB dF φ)
    (b1 : Fin n₁) (b0 : Fin m₁) (hne : dB (Pi.single b1 1) b0 ≠ 0) :
    aug.ε.comp (φ b1 b0).α₀.toLinearMap = aug.ε :=
  aug_comp_α₀_eq dF aug (φ b1 b0) (hφ b1 b0 hne)

/-! ## Helper lemmas -/

/-- Helper: `autAtDeg` at degree 0 is `α₀`. -/
@[simp]
lemma autAtDeg_zero
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (b1 : Fin n₁) (b0 : Fin m₁) :
    autAtDeg dF φ 0 b1 b0 = (φ b1 b0).α₀.toLinearMap := by
  simp [autAtDeg]

/-! ## Chain map properties of π_* -/

/-- On the `(p, 0)` summand, π_* intertwines the horizontal differential with the base
differential: `piStar ∘ dh = dB ∘ piStar`. -/
lemma piStarChainMap_q0_horizontal
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (aug : AugmentedComplex n₂ m₂ dF)
    (hφ : ActsAsIdentityOnHomology dB dF φ) :
    (piStarSummandLin (n₁ := n₁) (m₁ := m₁) dF aug 0 0).comp
      (twistedDhLin dB (fun b1 b0 => autAtDeg dF φ 0 b1 b0)) =
    dB.comp (piStarSummandLin (n₁ := n₁) (m₁ := m₁) dF aug 1 0) := by
  apply TensorProduct.ext'
  intro b f
  change (piStarSummandLin dF aug 0 0) ((twistedDhLin dB fun b1 b0 ↦ autAtDeg dF φ 0 b1 b0) (b ⊗ₜ[𝔽₂] f)) =
    dB (piStarSummandLin dF aug 1 0 (b ⊗ₜ[𝔽₂] f))
  simp only [twistedDhLin_tmul]
  simp_rw [map_sum, map_smul, show ∀ (p : ℤ) (b : Fin (baseSize n₁ m₁ p) → 𝔽₂) (f : Fin (fiberSize n₂ m₂ 0) → 𝔽₂),
    piStarSummandLin (n₁ := n₁) (m₁ := m₁) dF aug p 0 (b ⊗ₜ[𝔽₂] f) = aug.ε f • b
    from piStarSummandLin_tmul_q0 dF aug]
  rw [map_smul]
  -- Go pointwise and handle each summand via by_cases on the coefficient
  ext j
  -- Simplify both sides step by step
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- Inner sum: ∑ x_1, ... Pi.single x_1 1 j = ... (collapses via ite)
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero,
             Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  -- Each summand: replace aug.ε ((autAtDeg dF φ 0 i j) f) with aug.ε f
  have step1 : ∀ (i : Fin n₁) (j : Fin m₁),
      b i * (dB (Pi.single i 1) j * aug.ε ((autAtDeg dF φ 0 i j) f)) =
      b i * (dB (Pi.single i 1) j * aug.ε f) := by
    intro i j
    by_cases hne : dB (Pi.single i 1) j = 0
    · simp [hne]
    · have key : aug.ε.comp (autAtDeg dF φ 0 i j) = aug.ε := by
        rw [autAtDeg_zero]
        exact aug_preserved_by_connection dB dF φ aug hφ i j hne
      congr 1; congr 1
      exact LinearMap.congr_fun key f
  simp_rw [step1]
  -- Now: ∑ i, b i * (dB (Pi.single i 1) j * aug.ε f) = aug.ε f * dB b j
  simp_rw [show ∀ x, b x * (dB (Pi.single x 1) j * aug.ε f) =
    aug.ε f * (b x * dB (Pi.single x 1) j) from fun x => by ring]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [show ∀ x, b x * dB (Pi.single x 1) j =
    (b x • dB (Pi.single x 1)) j from fun x => by simp [Pi.smul_apply, smul_eq_mul]]
  rw [← Finset.sum_apply]
  have expand : dB b = ∑ i : Fin n₁, b i • dB (Pi.single i 1) := by
    conv_lhs => rw [show b = ∑ i : Fin n₁, b i • Pi.single i 1 from by
      ext j; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']]
    simp [map_sum, map_smul]
  exact congrFun expand.symm j

/-- On the `(p, 1)` summand, the vertical part of the chain map sends `b ⊗ f` via
`id ⊗ dF` to the `(p, 0)` summand, and then `piStar` applies `ε`.
The composition equals zero because `ε ∘ dF = 0`. -/
lemma piStarChainMap_q1_vertical
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (aug : AugmentedComplex n₂ m₂ dF)
    (p : ℤ) :
    (piStarSummandLin (n₁ := n₁) (m₁ := m₁) dF aug p 0).comp
      (LinearMap.lTensor _ (fiberDiff n₂ m₂ dF 1 0)) = 0 := by
  apply TensorProduct.ext'
  intro b f
  simp only [LinearMap.comp_apply, lTensor_tmul, piStarSummandLin_tmul_q0, zero_apply]
  have : (fiberDiff n₂ m₂ dF 1 0) f = dF f := by
    simp [fiberDiff]; rfl
  rw [this]
  have := LinearMap.ext_iff.mp aug.comp_eq_zero f
  simp [LinearMap.comp_apply] at this
  rw [this, zero_smul]

/-! ## Cochain map π^* -/

/-- The cochain map `π* : Dual(𝔽₂^{baseSize(n)}) → Dual(Tot(B ⊠_φ F)_n)` at degree `n`,
defined as the dual (transpose) of `π_*`. On a cochain `β ∈ B*_p`, this gives
`π*(β)(b ⊗ f) = β(b) · ε(f)` for `f ∈ F₀` and `π*(β)(b ⊗ f) = 0` for `f ∈ F₁`. -/
def cochainPiStar
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (aug : AugmentedComplex n₂ m₂ dF) (n : ℤ) :
    Module.Dual 𝔽₂ (Fin (baseSize n₁ m₁ n) → 𝔽₂) →ₗ[𝔽₂]
    Module.Dual 𝔽₂ ((fiberBundleDoubleComplex dB dF φ).totalComplex.X n) :=
  Module.Dual.transpose (R := 𝔽₂) (piStarMor dB dF φ aug n).hom

end FiberBundle

end
