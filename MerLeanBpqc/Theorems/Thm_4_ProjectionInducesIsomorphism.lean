import MerLeanBpqc.Theorems.Thm_3_FiberBundleHomology
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Theorem 4: Projection Induces Isomorphism

Under the assumptions that (1) the connection φ acts as identity on homology of F,
(2) the augmentation ε̄ : H₀(F) → 𝔽₂ is an isomorphism, and (3) H₀(B) = 0,
the projection π_* induces an isomorphism H₁(B ⊗_φ F) ≅ H₁(B), and dually
π^* induces an isomorphism H^1(B) ≅ H^1(B ⊗_φ F).

## Main Results
- `piStarDeg1Lin` — the linear map π_* at degree 1: (b ⊗ f, b' ⊗ f') ↦ ε(f) · b
- `piStarH1` — the induced map H₁(π_*) : H₁(B ⊗_φ F) → ker(dB)
- `piStarH1_isLinearEquiv` — H₁(π_*) is an isomorphism
- `piUpperStarH1` — the induced map H¹(π*) : H¹(B) → H¹(B ⊗_φ F)
- `piUpperStarH1_isLinearEquiv` — H¹(π*) is an isomorphism
-/

open CategoryTheory LinearMap
open scoped TensorProduct

noncomputable section

namespace FiberBundle

variable {n₁ m₁ n₂ m₂ : ℕ}

/-! ## Helper: tensor with zero module -/

/-- `M ⊗ N` is zero when `M` is subsingleton. -/
lemma tensorProduct_eq_zero_of_subsingleton_left {M N : Type*} [AddCommGroup M] [Module 𝔽₂ M]
    [AddCommGroup N] [Module 𝔽₂ N] [Subsingleton M] (x : M ⊗[𝔽₂] N) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n => rw [Subsingleton.elim m 0, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- If `M = 0` (subsingleton), then `M ⊗ N` is subsingleton. -/
instance tensorProduct_subsingleton_left (M N : Type*) [AddCommGroup M] [Module 𝔽₂ M]
    [AddCommGroup N] [Module 𝔽₂ N] [Subsingleton M] :
    Subsingleton (M ⊗[𝔽₂] N) :=
  ⟨fun a b => by rw [tensorProduct_eq_zero_of_subsingleton_left a,
    tensorProduct_eq_zero_of_subsingleton_left b]⟩

/-- If `M` is subsingleton, `M ⊗ N ≃ₗ 0` (the trivial module). -/
def tensorProduct_zero_left_equiv (M N : Type*) [AddCommGroup M] [Module 𝔽₂ M]
    [AddCommGroup N] [Module 𝔽₂ N] [Subsingleton M] :
    M ⊗[𝔽₂] N ≃ₗ[𝔽₂] PUnit := by
  exact {
    toFun := fun _ => PUnit.unit
    invFun := fun _ => 0
    left_inv := fun x => by simp [tensorProduct_eq_zero_of_subsingleton_left x]
    right_inv := fun x => by simp
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
  }

/-! ## Helper: quotient by top is subsingleton -/

instance quotient_top_subsingleton (M : Type*) [AddCommGroup M] [Module 𝔽₂ M] :
    Subsingleton (M ⧸ (⊤ : Submodule 𝔽₂ M)) := by
  constructor
  intro a b
  induction a using Quotient.inductionOn with | _ a =>
  induction b using Quotient.inductionOn with | _ b =>
  exact (Submodule.Quotient.eq _).mpr (Submodule.mem_top)

/-- `range f = ⊤` implies the quotient `M / range f` is subsingleton. -/
instance quotient_range_top_subsingleton {M N : Type*} [AddCommGroup M] [Module 𝔽₂ M]
    [AddCommGroup N] [Module 𝔽₂ N] (f : M →ₗ[𝔽₂] N) (hf : range f = ⊤) :
    Subsingleton (N ⧸ range f) := by
  rw [hf]; exact quotient_top_subsingleton N

/-! ## Helper: product with zero -/

/-- `M × PUnit ≃ₗ M`. -/
def prod_punit_equiv (M : Type*) [AddCommGroup M] [Module 𝔽₂ M] :
    (M × PUnit) ≃ₗ[𝔽₂] M where
  toFun := fun p => p.1
  invFun := fun m => (m, PUnit.unit)
  left_inv := fun ⟨m, u⟩ => by simp
  right_inv := fun m => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-! ## Definition of π_* at degree 1

The projection map π_* from Def_13: on the (p,0) summand B_p ⊗ F_0,
it sends b ⊗ f ↦ ε(f) · b. On the (p,1) summand B_p ⊗ F_1, it is zero.
At degree 1 of the total complex, Tot₁ = A₁₀ × A₀₁ = (B₁ ⊗ F₀) × (B₀ ⊗ F₁).
So π_*(x₁₀, x₀₁) = (rid ∘ (id ⊗ ε))(x₁₀). -/

/-- The projection π_* at degree 1: `(x₁₀, x₀₁) ↦ (TensorProduct.rid (id ⊗ ε))(x₁₀)`.
    This sends `b ⊗ f ↦ ε(f) · b` on the `B₁ ⊗ F₀` component and is zero on `B₀ ⊗ F₁`. -/
def piStarDeg1Lin (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂) :
    ((Fin n₁ → 𝔽₂) ⊗[𝔽₂] (Fin m₂ → 𝔽₂)) × ((Fin m₁ → 𝔽₂) ⊗[𝔽₂] (Fin n₂ → 𝔽₂)) →ₗ[𝔽₂]
    (Fin n₁ → 𝔽₂) :=
  LinearMap.coprod
    ((TensorProduct.rid 𝔽₂ (Fin n₁ → 𝔽₂)).toLinearMap.comp (LinearMap.lTensor _ ε))
    0

/-- π_* sends `b ⊗ f` to `ε(f) • b` on the first component. -/
lemma piStarDeg1Lin_tmul (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂)
    (b : Fin n₁ → 𝔽₂) (f : Fin m₂ → 𝔽₂) :
    piStarDeg1Lin ε (b ⊗ₜ[𝔽₂] f, (0 : (Fin m₁ → 𝔽₂) ⊗[𝔽₂] (Fin n₂ → 𝔽₂))) = ε f • b := by
  simp [piStarDeg1Lin, LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.lTensor_tmul,
    TensorProduct.rid_tmul]

/-- π_* is zero on the second component (B₀ ⊗ F₁). -/
lemma piStarDeg1Lin_snd (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂)
    (x : (Fin m₁ → 𝔽₂) ⊗[𝔽₂] (Fin n₂ → 𝔽₂)) :
    piStarDeg1Lin (n₁ := n₁) (m₁ := m₁) (n₂ := n₂) ε
      ((0 : (Fin n₁ → 𝔽₂) ⊗[𝔽₂] (Fin m₂ → 𝔽₂)), x) = 0 := by
  simp [piStarDeg1Lin, LinearMap.coprod_apply]

/-! ## Helper: ε is invariant under the connection -/

/-- When φ(b1,b0) acts as identity on homology and ε ∘ dF = 0,
    we get ε ∘ α₀ = ε (the augmentation is invariant under the connection). -/
lemma epsilon_comp_alpha0_eq
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (ψ : ChainAutomorphism n₂ m₂ dF)
    (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂) (hε : ε.comp dF = 0)
    (hψ : ψ.ActsAsIdOnHomology dF) :
    ε.comp ψ.α₀.toLinearMap = ε := by
  apply LinearMap.ext; intro v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  have hd : ψ.α₀ v - v ∈ range dF := hψ.deg0 v
  obtain ⟨w, hw⟩ := hd
  have hεr : ε (ψ.α₀ v - v) = 0 := by
    rw [← hw]; exact LinearMap.congr_fun hε w
  rwa [map_sub, sub_eq_zero] at hεr

/-- Per-term epsilon invariance: `dB(e_{b1})(b0) • ε(autAtDeg f) = dB(e_{b1})(b0) • ε(f)`. -/
lemma epsilon_autAtDeg_smul_eq
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂) (hε : ε.comp dF = 0)
    (hφ : ActsAsIdentityOnHomology dB dF φ)
    (b1 : Fin n₁) (b0 : Fin m₁) (f : Fin m₂ → 𝔽₂) :
    dB (Pi.single b1 1) b0 • ε (autAtDeg dF φ 0 b1 b0 f) =
    dB (Pi.single b1 1) b0 • ε f := by
  by_cases h : dB (Pi.single b1 1) b0 = 0
  · simp [h]
  · congr 1
    have hψ := hφ b1 b0 h
    have : autAtDeg dF φ 0 b1 b0 = (φ b1 b0).α₀.toLinearMap := by
      simp [autAtDeg]
    rw [this]
    exact LinearMap.congr_fun (epsilon_comp_alpha0_eq dF (φ b1 b0) ε hε hψ) f

/-- Basis expansion of a linear map: `dB b = ∑ i, b i • dB (Pi.single i 1)`. -/
lemma linearMap_basis_expand
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (b : Fin n₁ → 𝔽₂) :
    dB b = ∑ b1 : Fin n₁, b b1 • dB (Pi.single b1 1) := by
  conv_lhs => rw [show b = ∑ i : Fin n₁, b i • Pi.single i 1 from by
    ext j; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']]
  simp [map_sum, map_smul]

/-- The chain map property for the twisted differential:
    (rid ∘ (id ⊗ ε)) ∘ dh₀ = dB ∘ (rid ∘ (id ⊗ ε)) on B₁ ⊗ F₀. -/
lemma piStar_chainmap_twistedDh
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂) (hε : ε.comp dF = 0)
    (hφ : ActsAsIdentityOnHomology dB dF φ)
    (x : (Fin n₁ → 𝔽₂) ⊗[𝔽₂] (Fin m₂ → 𝔽₂)) :
    (TensorProduct.rid 𝔽₂ (Fin m₁ → 𝔽₂))
      ((LinearMap.lTensor _ ε) ((fiberBundleSmallDC dB dF φ).dh₀ x)) =
    dB ((TensorProduct.rid 𝔽₂ (Fin n₁ → 𝔽₂))
      ((LinearMap.lTensor _ ε) x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul b f =>
    simp only [fiberBundleSmallDC]
    rw [twistedDhLin_tmul]
    simp only [map_sum, map_smul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    -- Goal: Σ b1 b0, b(b1) • dB(e_{b1})(b0) • ε(autAtDeg(f)) • e_{b0} = ε(f) • dB(b)
    -- autAtDeg dF φ 0 b1 b0 unfolds to (φ b1 b0).α₀.toLinearMap
    simp only [autAtDeg, show (0 : ℤ) ≠ 1 from by omega, ↓reduceDIte, show (0 : ℤ) = 0 from rfl]
    -- Replace each term using Finset.sum_congr
    have step1 : ∀ (b1 : Fin n₁) (b0 : Fin m₁),
        b b1 • dB (Pi.single b1 1) b0 • ε ((φ b1 b0).α₀ f) •
          (Pi.single b0 (1 : 𝔽₂) : Fin m₁ → 𝔽₂) =
        b b1 • dB (Pi.single b1 1) b0 • ε f •
          (Pi.single b0 (1 : 𝔽₂) : Fin m₁ → 𝔽₂) := by
      intro b1 b0
      by_cases h : dB (Pi.single b1 1) b0 = 0
      · simp [h]
      · have := LinearMap.congr_fun (epsilon_comp_alpha0_eq dF (φ b1 b0) ε hε (hφ b1 b0 h)) f
        simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at this
        rw [this]
    simp only [LinearEquiv.coe_coe] at step1 ⊢
    simp_rw [step1]
    -- Now: Σ b1 b0, b(b1) • dB(e_{b1})(b0) • ε(f) • e_{b0} = ε(f) • dB(b)
    -- Go pointwise
    ext j
    simp only [smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
               Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
               mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    -- Goal: ∑ x, b x * (dB (Pi.single x 1) j * ε f) = ε f * dB b j
    simp_rw [show ∀ x, b x * (dB (Pi.single x 1) j * ε f) =
      ε f * (b x * dB (Pi.single x 1) j) from fun x => by ring]
    rw [← Finset.mul_sum]
    congr 1
    -- Goal: ∑ x, b x * dB (Pi.single x 1) j = dB b j
    simp_rw [show ∀ x, b x * dB (Pi.single x 1) j =
      (b x • dB (Pi.single x 1)) j from fun x => by simp [Pi.smul_apply, smul_eq_mul]]
    rw [← Finset.sum_apply]
    exact congrFun (linearMap_basis_expand dB b).symm j

/-! ## π_* maps cycles to ker(dB) and boundaries to 0 -/

/-- π_* maps total 1-cycles to ker(dB). This is because π_* is a chain map:
    dB ∘ π_* = π_* ∘ d₁, and d₁(z) = 0 for z ∈ totZ₁. -/
lemma piStarDeg1_maps_cycles
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂) (hε : ε.comp dF = 0)
    (hφ : ActsAsIdentityOnHomology dB dF φ)
    (z : ↥(fiberBundleSmallDC dB dF φ).totZ₁) :
    piStarDeg1Lin ε z.val ∈ ker dB := by
  rw [mem_ker]
  -- z ∈ ker d₁ means d₁(z.val) = 0
  have hz : (fiberBundleSmallDC dB dF φ).d₁ z.val = 0 := mem_ker.mp z.prop
  -- d₁ = coprod dh₀ dv₀, so dh₀(z.1) + dv₀(z.2) = 0
  simp only [SmallDC.d₁, coprod_apply] at hz
  -- Apply (rid ∘ (id ⊗ ε)) at degree 0 to the equation dh₀(z.1) + dv₀(z.2) = 0
  have h0 : (TensorProduct.rid 𝔽₂ (Fin m₁ → 𝔽₂))
      ((LinearMap.lTensor _ ε) ((fiberBundleSmallDC dB dF φ).dh₀ z.val.1 +
        (fiberBundleSmallDC dB dF φ).dv₀ z.val.2)) = 0 := by
    rw [hz]; simp
  simp only [map_add] at h0
  -- The dv₀ term vanishes: (rid ∘ (id ⊗ ε)) ∘ (id ⊗ dF) = 0
  have hdv : (TensorProduct.rid 𝔽₂ (Fin m₁ → 𝔽₂))
      ((LinearMap.lTensor _ ε) ((fiberBundleSmallDC dB dF φ).dv₀ z.val.2)) = 0 := by
    simp only [fiberBundleSmallDC]
    rw [← LinearMap.comp_apply (LinearMap.lTensor _ ε) (LinearMap.lTensor _ dF),
        ← LinearMap.lTensor_comp, hε]
    simp [LinearMap.lTensor_zero]
  rw [hdv, add_zero] at h0
  -- By chain map property: dh₀ term = dB(piStar(z.1))
  rw [piStar_chainmap_twistedDh dB dF φ ε hε hφ z.val.1] at h0
  -- piStarDeg1Lin ε z = (rid ∘ (id ⊗ ε))(z.1)
  show dB (piStarDeg1Lin ε z.val) = 0
  simp only [piStarDeg1Lin, coprod_apply, zero_apply, add_zero, LinearMap.comp_apply] at h0 ⊢
  exact h0

/-- The restriction of π_* to totZ₁, landing in ker(dB). -/
def piStarOnCycles
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂) (hε : ε.comp dF = 0)
    (hφ : ActsAsIdentityOnHomology dB dF φ) :
    ↥(fiberBundleSmallDC dB dF φ).totZ₁ →ₗ[𝔽₂] ↥(ker dB) where
  toFun z := ⟨piStarDeg1Lin ε z.val, piStarDeg1_maps_cycles dB dF φ ε hε hφ z⟩
  map_add' x y := by ext; simp [map_add]
  map_smul' r x := by ext; simp [map_smul]

/-- π_* maps total 1-boundaries to 0 in ker(dB). Since B has no degree-2 terms,
    the image of π_* on boundaries is 0 (boundaries come from d₂ which involves
    B₁ ⊗ F₁, and π₁ = 0 on F₁): `ε ∘ dF = 0` ensures `π_*(dv₁(x)) = 0` and
    `π_*` is zero on the A₀₁ component. -/
lemma piStarOnCycles_maps_boundaries
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂) (hε : ε.comp dF = 0)
    (hφ : ActsAsIdentityOnHomology dB dF φ) :
    (fiberBundleSmallDC dB dF φ).totB₁InZ₁ ≤
      (piStarOnCycles dB dF φ ε hε hφ).ker := by
  intro z hz
  simp only [mem_ker, piStarOnCycles, LinearMap.coe_mk, AddHom.coe_mk]
  -- z.val ∈ totB₁ = range d₂
  rw [SmallDC.totB₁InZ₁, Submodule.mem_comap] at hz
  rw [SmallDC.totB₁, mem_range] at hz
  obtain ⟨w, hw⟩ := hz
  -- z.val = (dv₁(w), dh₁(w))
  have hfst : z.val.1 = (fiberBundleSmallDC dB dF φ).dv₁ w := by
    have := congr_arg Prod.fst hw; simp [SmallDC.d₂, prod_apply] at this; exact this.symm
  -- piStarDeg1Lin ε z.val = (rid ∘ (id ⊗ ε))(dv₁(w))
  ext
  simp only [Submodule.coe_zero, ZeroMemClass.coe_zero, Pi.zero_apply,
    piStarDeg1Lin, coprod_apply, zero_apply, add_zero, LinearMap.comp_apply]
  -- dv₁ = lTensor _ dF, so (id ⊗ ε)(dv₁(w)) = lTensor _ (ε ∘ dF)(w) = 0
  rw [hfst]
  have : (LinearMap.lTensor (Fin n₁ → 𝔽₂) ε) ((fiberBundleSmallDC dB dF φ).dv₁ w) = 0 := by
    simp only [fiberBundleSmallDC]
    rw [← LinearMap.comp_apply (LinearMap.lTensor _ ε) (LinearMap.lTensor _ dF),
        ← LinearMap.lTensor_comp, hε]
    simp [LinearMap.lTensor_zero]
  simp [this]

/-! ## The induced map on homology H₁(π_*) -/

/-- The induced map H₁(π_*) : H₁(B ⊗_φ F) → ker(dB) = H₁(B).
    This is the map on quotients induced by π_* restricted to cycles. -/
def piStarH1
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂) (hε : ε.comp dF = 0)
    (hφ : ActsAsIdentityOnHomology dB dF φ) :
    (fiberBundleSmallDC dB dF φ).totH₁ →ₗ[𝔽₂] ↥(ker dB) :=
  Submodule.liftQ _ (piStarOnCycles dB dF φ ε hε hφ)
    (piStarOnCycles_maps_boundaries dB dF φ ε hε hφ)

/-! ## Surjectivity helpers for H₁(π_*) -/

/-- The twisted horizontal differential sends `v ⊗ f₀` (with `v ∈ ker dB`) into the
    range of the vertical differential `dv₀ = lTensor _ dF`. This is because the twisting
    only changes `f₀` by elements in `im(dF)`. -/
lemma twistedDh_kerDB_tmul_mem_range_dv₀
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (hφ : ActsAsIdentityOnHomology dB dF φ)
    (v : ↥(ker dB)) (f₀ : Fin m₂ → 𝔽₂) :
    (fiberBundleSmallDC dB dF φ).dh₀ (v.val ⊗ₜ f₀) ∈
      range (fiberBundleSmallDC dB dF φ).dv₀ := by
  simp only [fiberBundleSmallDC]
  rw [twistedDhLin_tmul]
  -- Unfold autAtDeg to get (φ b1 b0).α₀
  simp only [autAtDeg, show (0 : ℤ) ≠ 1 from by omega, ↓reduceDIte,
             show (0 : ℤ) = 0 from rfl, LinearEquiv.coe_toLinearMap]
  simp_rw [smul_smul, show ∀ (x : Fin n₁) (x_1 : Fin m₁),
      (Pi.single x_1 (1 : 𝔽₂) : Fin m₁ → 𝔽₂) ⊗ₜ[𝔽₂] ((φ x x_1).α₀ f₀) =
      (Pi.single x_1 (1 : 𝔽₂) : Fin m₁ → 𝔽₂) ⊗ₜ[𝔽₂] f₀ +
      (Pi.single x_1 (1 : 𝔽₂) : Fin m₁ → 𝔽₂) ⊗ₜ[𝔽₂] ((φ x x_1).α₀ f₀ - f₀)
    from fun x x_1 => by rw [← TensorProduct.tmul_add, add_sub_cancel],
    smul_add]
  simp_rw [Finset.sum_add_distrib]
  apply Submodule.add_mem
  · -- First sum = dB(v) ⊗ f₀ = 0 ∈ range
    have : ∑ b1, ∑ b0, (v.val b1 * dB (Pi.single b1 1) b0) •
        ((Pi.single b0 (1 : 𝔽₂) : Fin m₁ → 𝔽₂) ⊗ₜ[𝔽₂] f₀) = 0 := by
      rw [show (∑ b1 : Fin n₁, ∑ b0 : Fin m₁,
        (v.val b1 * dB (Pi.single b1 1) b0) •
        ((Pi.single b0 (1 : 𝔽₂) : Fin m₁ → 𝔽₂) ⊗ₜ[𝔽₂] f₀)) =
        (dB v.val) ⊗ₜ[𝔽₂] f₀ from by
          simp_rw [TensorProduct.smul_tmul', ← TensorProduct.sum_tmul]
          congr 1
          rw [linearMap_basis_expand dB v.val]
          ext j; simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
            Finset.sum_ite_eq', Finset.mem_univ]]
      rw [mem_ker.mp v.prop, TensorProduct.zero_tmul]
    rw [this]; exact zero_mem _
  · -- Second sum: each term ∈ range(lTensor _ dF)
    apply Submodule.sum_mem; intro b1 _; apply Submodule.sum_mem; intro b0 _
    by_cases h : dB (Pi.single b1 1) b0 = 0
    · simp [h]
    · -- dB(e_{b1})(b0) ≠ 0, so autAtDeg(f₀) - f₀ ∈ range dF
      have hψ := hφ b1 b0 h
      obtain ⟨g, hg⟩ := hψ.deg0 f₀
      rw [show (φ b1 b0).α₀ f₀ - f₀ = dF g from hg.symm]
      rw [show (Pi.single b0 (1 : 𝔽₂) : Fin m₁ → 𝔽₂) ⊗ₜ[𝔽₂] dF g =
        (LinearMap.lTensor (Fin m₁ → 𝔽₂) dF) (Pi.single b0 (1 : 𝔽₂) ⊗ₜ g) from by
          simp [LinearMap.lTensor_tmul]]
      exact Submodule.smul_mem _ _ (mem_range.mpr ⟨_, rfl⟩)

/-- piStarH1 is surjective: for any `v ∈ ker dB`, there exists a class in `totH₁`
    mapping to `v`. -/
lemma piStarH1_surjective
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂) (hε : ε.comp dF = 0)
    (hφ : ActsAsIdentityOnHomology dB dF φ)
    (hε_surj : Function.Surjective ε) :
    Function.Surjective (piStarH1 dB dF φ ε hε hφ) := by
  -- Get f₀ with ε(f₀) = 1
  obtain ⟨f₀, hf₀⟩ := hε_surj 1
  intro ⟨v, hv⟩
  -- dh₀(v ⊗ f₀) ∈ range(dv₀)
  have hdh : (fiberBundleSmallDC dB dF φ).dh₀ (v ⊗ₜ f₀) ∈
      range (fiberBundleSmallDC dB dF φ).dv₀ :=
    twistedDh_kerDB_tmul_mem_range_dv₀ dB dF φ hφ ⟨v, hv⟩ f₀
  obtain ⟨y, hy⟩ := hdh
  -- z = (v ⊗ f₀, y) ∈ ker d₁ since dh₀(v ⊗ f₀) + dv₀(y) = 0 over 𝔽₂
  let z_val : ((Fin n₁ → 𝔽₂) ⊗[𝔽₂] (Fin m₂ → 𝔽₂)) ×
      ((Fin m₁ → 𝔽₂) ⊗[𝔽₂] (Fin n₂ → 𝔽₂)) := (v ⊗ₜ f₀, y)
  have hz : z_val ∈ (fiberBundleSmallDC dB dF φ).totZ₁ := by
    rw [SmallDC.totZ₁, mem_ker, SmallDC.d₁]
    show (fiberBundleSmallDC dB dF φ).dh₀ (v ⊗ₜ f₀) +
      (fiberBundleSmallDC dB dF φ).dv₀ y = 0
    rw [← hy]; exact ZModModule.add_self _
  let z : ↥(fiberBundleSmallDC dB dF φ).totZ₁ := ⟨z_val, hz⟩
  -- [z] ∈ totH₁ maps to v under piStarH1
  use Submodule.Quotient.mk z
  have : (piStarH1 dB dF φ ε hε hφ) (Submodule.Quotient.mk z) =
      piStarOnCycles dB dF φ ε hε hφ z := Submodule.liftQ_apply _ _ _
  rw [this]
  ext x
  simp only [piStarOnCycles, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_mk, z_val, piStarDeg1Lin, coprod_apply, zero_apply, add_zero,
    LinearMap.comp_apply, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hf₀, one_smul,
    Pi.smul_apply, smul_eq_mul, mul_one, z, Pi.one_apply]
  simp [TensorProduct.rid_tmul]

/-! ## Dimension argument: finrank totH₁ = finrank (ker dB) -/

/-- The finrank of `totH₁` equals that of `ker dB` under the fiber bundle hypotheses. -/
lemma finrank_totH1_eq_finrank_kerDB
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (hφ : ActsAsIdentityOnHomology dB dF φ)
    (hεbar : ((Fin m₂ → 𝔽₂) ⧸ range dF) ≃ₗ[𝔽₂] 𝔽₂)
    (hH0B : range dB = ⊤) :
    Module.finrank 𝔽₂ (fiberBundleSmallDC dB dF φ).totH₁ =
    Module.finrank 𝔽₂ ↥(ker dB) := by
  obtain ⟨e⟩ := fiberBundleHomology_n1 dB dF φ hφ
  -- totH₁ ≅ (ker dB ⊗ coker dF) × (coker dB ⊗ ker dF)
  have h1 := LinearEquiv.finrank_eq e
  -- coker dB is subsingleton
  haveI : Subsingleton ((Fin m₁ → 𝔽₂) ⧸ range dB) := by
    rw [hH0B]; exact quotient_top_subsingleton _
  -- coker dB ⊗ ker dF is subsingleton
  haveI : Subsingleton (((Fin m₁ → 𝔽₂) ⧸ range dB) ⊗[𝔽₂] ↥(ker dF)) :=
    tensorProduct_subsingleton_left _ _
  -- ker dB ⊗ coker dF ≅ ker dB ⊗ 𝔽₂ ≅ ker dB
  have h2 : Module.finrank 𝔽₂ (↥(ker dB) ⊗[𝔽₂] ((Fin m₂ → 𝔽₂) ⧸ range dF)) =
      Module.finrank 𝔽₂ ↥(ker dB) := by
    rw [LinearEquiv.finrank_eq (LinearEquiv.lTensor _ hεbar),
        LinearEquiv.finrank_eq (TensorProduct.rid 𝔽₂ ↥(ker dB))]
  rw [h1, Module.finrank_prod]
  have h3 : Module.finrank 𝔽₂ (((Fin m₁ → 𝔽₂) ⧸ range dB) ⊗[𝔽₂] ↥(ker dF)) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [h2, h3, add_zero]

/-! ## Main theorem: H₁(π_*) is an isomorphism -/

/-- Under assumptions:
  (1) connection φ acts as identity on homology of F,
  (2) ε̄ : H₀(F) → 𝔽₂ is an isomorphism (the augmentation ε induces an iso on H₀(F)),
  (3) H₀(B) = 0, i.e., range dB = ⊤ (dB is surjective),
  the map H₁(π_*) : H₁(B ⊗_φ F) → H₁(B) = ker(dB) is a linear isomorphism.
  This is the specific isomorphism induced by the chain map π_* from Def_13. -/
theorem piStarH1_isLinearEquiv
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂) (hε : ε.comp dF = 0)
    (hφ : ActsAsIdentityOnHomology dB dF φ)
    (hεbar : ((Fin m₂ → 𝔽₂) ⧸ range dF) ≃ₗ[𝔽₂] 𝔽₂)
    (hH0B : range dB = ⊤)
    (hε_surj : Function.Surjective ε) :
    Function.Bijective (piStarH1 dB dF φ ε hε hφ) := by
  have hsurj := piStarH1_surjective dB dF φ ε hε hφ hε_surj
  have hfr := finrank_totH1_eq_finrank_kerDB dB dF φ hφ hεbar hH0B
  haveI : FiniteDimensional 𝔽₂ (fiberBundleSmallDC dB dF φ).totH₁ := by
    obtain ⟨e⟩ := fiberBundleHomology_n1 dB dF φ hφ
    exact LinearEquiv.finiteDimensional e.symm
  haveI : FiniteDimensional 𝔽₂ ↥(ker dB) := FiniteDimensional.finiteDimensional_submodule _
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mpr hsurj, hsurj⟩

/-- The isomorphism H₁(π_*) as a `LinearEquiv`. -/
def piStarH1Equiv
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂) (hε : ε.comp dF = 0)
    (hφ : ActsAsIdentityOnHomology dB dF φ)
    (hεbar : ((Fin m₂ → 𝔽₂) ⧸ range dF) ≃ₗ[𝔽₂] 𝔽₂)
    (hH0B : range dB = ⊤)
    (hε_surj : Function.Surjective ε) :
    (fiberBundleSmallDC dB dF φ).totH₁ ≃ₗ[𝔽₂] ↥(ker dB) :=
  LinearEquiv.ofBijective (piStarH1 dB dF φ ε hε hφ)
    (piStarH1_isLinearEquiv dB dF φ ε hε hφ hεbar hH0B hε_surj)

/-! ## Cohomology version via duality (π^*) -/

/-- The cochain map π^* at degree 1: the dual/transpose of π_* at degree 1.
    For β ∈ B*₁ = Dual(B₁), π^*(β) ∈ Tot₁* is defined by
    π^*(β)(b ⊗ f) = β(b) · ε(f) for f ∈ F₀, and π^*(β)(b ⊗ f) = 0 for f ∈ F₁. -/
def piUpperStarDeg1Lin (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂) :
    Module.Dual 𝔽₂ (Fin n₁ → 𝔽₂) →ₗ[𝔽₂]
    Module.Dual 𝔽₂ (((Fin n₁ → 𝔽₂) ⊗[𝔽₂] (Fin m₂ → 𝔽₂)) ×
                     ((Fin m₁ → 𝔽₂) ⊗[𝔽₂] (Fin n₂ → 𝔽₂))) :=
  (piStarDeg1Lin ε).dualMap

/-- For finite-dimensional spaces, an isomorphism `V ≃ₗ W` dualizes to `W* ≃ₗ V*`. -/
def dualEquivOfEquiv {V W : Type*} [AddCommGroup V] [Module 𝔽₂ V]
    [AddCommGroup W] [Module 𝔽₂ W] [FiniteDimensional 𝔽₂ V] [FiniteDimensional 𝔽₂ W]
    (e : V ≃ₗ[𝔽₂] W) :
    Module.Dual 𝔽₂ W ≃ₗ[𝔽₂] Module.Dual 𝔽₂ V where
  toFun := fun f => f.comp e.toLinearMap
  invFun := fun f => f.comp e.symm.toLinearMap
  left_inv := fun f => by ext w; simp
  right_inv := fun f => by ext v; simp
  map_add' := fun f g => by ext; simp
  map_smul' := fun r f => by ext; simp

/-- The induced map H¹(π^*) on cohomology. Since π^* is the transpose of π_*,
    and H₁(π_*) is an isomorphism between finite-dimensional spaces, the transpose
    H¹(π^*) : H¹(B) → H¹(B ⊗_φ F) is also an isomorphism. -/
def piUpperStarH1Equiv
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂) (hε : ε.comp dF = 0)
    (hφ : ActsAsIdentityOnHomology dB dF φ)
    (hεbar : ((Fin m₂ → 𝔽₂) ⧸ range dF) ≃ₗ[𝔽₂] 𝔽₂)
    (hH0B : range dB = ⊤)
    (hε_surj : Function.Surjective ε)
    [FiniteDimensional 𝔽₂ (fiberBundleSmallDC dB dF φ).totH₁]
    [FiniteDimensional 𝔽₂ ↥(ker dB)] :
    Module.Dual 𝔽₂ ↥(ker dB) ≃ₗ[𝔽₂]
      Module.Dual 𝔽₂ (fiberBundleSmallDC dB dF φ).totH₁ :=
  dualEquivOfEquiv (piStarH1Equiv dB dF φ ε hε hφ hεbar hH0B hε_surj)

/-- H¹(π^*) is an isomorphism: the transpose of the isomorphism H₁(π_*). -/
theorem piUpperStarH1_isLinearEquiv
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (ε : (Fin m₂ → 𝔽₂) →ₗ[𝔽₂] 𝔽₂) (hε : ε.comp dF = 0)
    (hφ : ActsAsIdentityOnHomology dB dF φ)
    (hεbar : ((Fin m₂ → 𝔽₂) ⧸ range dF) ≃ₗ[𝔽₂] 𝔽₂)
    (hH0B : range dB = ⊤)
    (hε_surj : Function.Surjective ε)
    [FiniteDimensional 𝔽₂ (fiberBundleSmallDC dB dF φ).totH₁]
    [FiniteDimensional 𝔽₂ ↥(ker dB)] :
    Function.Bijective (piUpperStarH1Equiv dB dF φ ε hε hφ hεbar hH0B hε_surj).toLinearMap := by
  exact (piUpperStarH1Equiv dB dF φ ε hε hφ hεbar hH0B hε_surj).bijective

end FiberBundle

end
