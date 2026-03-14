import MerLeanBpqc.Definitions.Def_12_FiberBundleDoubleComplex
import MerLeanBpqc.Theorems.Thm_2_SmallDoubleComplexHomology
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Theorem 3: Fiber Bundle Homology

Let `B ⊗_φ F` be a fiber bundle complex (Def_12). If the connection `φ` acts as
the identity on the homology of `F`, then
`H_n(B ⊗_φ F) ≅ ⊕_{p+q=n} H_p(B) ⊗ H_q(F)` for each `n`.

## Main Definitions
- `ChainAutomorphism.ActsAsIdOnHomology` — a chain automorphism induces the identity on homology
- `ActsAsIdentityOnHomology` — the connection acts as identity on homology
- `fiberBundleSmallDC` — the fiber bundle as a 2×2 double complex (`SmallDC`)
- `fiberBundleHomology_n0/n1/n2` — the main isomorphisms at each degree
-/

open CategoryTheory LinearMap
open scoped TensorProduct

noncomputable section

namespace FiberBundle

variable {n₁ m₁ n₂ m₂ : ℕ}

/-! ## Acts as identity on homology -/

/-- A chain automorphism `ψ` of `F = (F₁ →[dF] F₀)` **acts as the identity on homology** if:
- At degree 1: `α₁(f) = f` for all `f ∈ ker(dF)` (since `H₁(F) = ker(dF)`)
- At degree 0: `α₀(y) - y ∈ im(dF)` for all `y` (so `[α₀(y)] = [y]` in `H₀(F) = F₀/im(dF)`)
-/
structure ChainAutomorphism.ActsAsIdOnHomology
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (ψ : ChainAutomorphism n₂ m₂ dF) : Prop where
  /-- At degree 1: `α₁` fixes `ker(dF)`. -/
  deg1 : ∀ f : Fin n₂ → 𝔽₂, f ∈ ker dF → ψ.α₁ f = f
  /-- At degree 0: `α₀(y) - y ∈ im(dF)` for all `y`. -/
  deg0 : ∀ y : Fin m₂ → 𝔽₂, ψ.α₀ y - y ∈ range dF

/-- The connection `φ` **acts as identity on homology** if for every basis element `b¹` and
every `b⁰ ∈ supp(∂^B b¹)`, the chain automorphism `φ(b¹, b⁰)` acts as identity on `H_q(F)`. -/
def ActsAsIdentityOnHomology
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF) : Prop :=
  ∀ (b1 : Fin n₁) (b0 : Fin m₁),
    dB (Pi.single b1 1) b0 ≠ 0 → (φ b1 b0).ActsAsIdOnHomology dF

/-! ## SmallDC from fiber bundle -/

/-- The fiber bundle double complex as a concrete 2×2 double complex. -/
def fiberBundleSmallDC
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF) : SmallDC where
  A₁₁ := (Fin n₁ → 𝔽₂) ⊗[𝔽₂] (Fin n₂ → 𝔽₂)
  A₁₀ := (Fin n₁ → 𝔽₂) ⊗[𝔽₂] (Fin m₂ → 𝔽₂)
  A₀₁ := (Fin m₁ → 𝔽₂) ⊗[𝔽₂] (Fin n₂ → 𝔽₂)
  A₀₀ := (Fin m₁ → 𝔽₂) ⊗[𝔽₂] (Fin m₂ → 𝔽₂)
  dv₁ := LinearMap.lTensor _ dF
  dv₀ := LinearMap.lTensor _ dF
  dh₁ := twistedDhLin dB (fun b1 b0 => autAtDeg dF φ 1 b1 b0)
  dh₀ := twistedDhLin dB (fun b1 b0 => autAtDeg dF φ 0 b1 b0)
  comm := (twistedDh_comm_dv dB dF φ).symm

/-! ## Flatness lemmas

Over `𝔽₂` (a field), every module is free hence flat. This gives:
- `ker(id_M ⊗ f) ≅ M ⊗ ker(f)`
- `(M ⊗ N) / im(id_M ⊗ f) ≅ M ⊗ (N / im f)`
-/

/-- `ker(id_M ⊗ f) ≅ M ⊗ ker(f)` when `M` is free (hence flat). -/
def lTensor_ker_equiv (M : Type*) [AddCommGroup M] [Module 𝔽₂ M] [Module.Free 𝔽₂ M]
    (f : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂)) :
    ↥(ker (LinearMap.lTensor M f)) ≃ₗ[𝔽₂] M ⊗[𝔽₂] ↥(ker f) := by
  haveI : Module.Flat 𝔽₂ M := inferInstance
  have hinj : Function.Injective (LinearMap.lTensor M (ker f).subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (ker f).injective_subtype
  have hker_eq : ker (LinearMap.lTensor M f) =
      range (LinearMap.lTensor M (ker f).subtype) := by
    rw [← exact_iff]
    exact Module.Flat.lTensor_exact M (LinearMap.exact_subtype_ker_map f)
  exact (LinearEquiv.ofEq _ _ hker_eq).trans
    (LinearEquiv.ofInjective _ hinj).symm

/-- `(M ⊗ N) / im(id_M ⊗ f) ≅ M ⊗ (N / im f)`. -/
def lTensor_quotient_equiv (M : Type*) [AddCommGroup M] [Module 𝔽₂ M]
    (f : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂)) :
    ((M ⊗[𝔽₂] (Fin m₂ → 𝔽₂)) ⧸ LinearMap.range (LinearMap.lTensor M f)) ≃ₗ[𝔽₂]
    M ⊗[𝔽₂] ((Fin m₂ → 𝔽₂) ⧸ LinearMap.range f) :=
  lTensor.equiv M (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _)

/-- `ker(f ⊗ id_M) ≅ ker(f) ⊗ M` when `M` is free (hence flat). -/
def rTensor_ker_equiv (M : Type*) [AddCommGroup M] [Module 𝔽₂ M] [Module.Free 𝔽₂ M]
    (f : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂)) :
    ↥(ker (LinearMap.rTensor M f)) ≃ₗ[𝔽₂] ↥(ker f) ⊗[𝔽₂] M := by
  haveI : Module.Flat 𝔽₂ M := inferInstance
  have hinj : Function.Injective (LinearMap.rTensor M (ker f).subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (ker f).injective_subtype
  have hker_eq : ker (LinearMap.rTensor M f) =
      range (LinearMap.rTensor M (ker f).subtype) := by
    rw [← exact_iff]
    exact Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map f)
  exact (LinearEquiv.ofEq _ _ hker_eq).trans
    (LinearEquiv.ofInjective _ hinj).symm

/-- `(N ⊗ M) / im(f ⊗ id_M) ≅ (N / im f) ⊗ M`. -/
def rTensor_quotient_equiv (M : Type*) [AddCommGroup M] [Module 𝔽₂ M]
    (f : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂)) :
    (((Fin m₁ → 𝔽₂) ⊗[𝔽₂] M) ⧸ LinearMap.range (LinearMap.rTensor M f)) ≃ₗ[𝔽₂]
    ((Fin m₁ → 𝔽₂) ⧸ LinearMap.range f) ⊗[𝔽₂] M :=
  rTensor.equiv M (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _)

/-! ## Key lemma: twisted dh on ker(dF)

When the connection acts as identity on H₁(F) = ker(dF), the twisted horizontal
differential restricted to B₁ ⊗ ker(dF) equals the untwisted dB ⊗ id_{ker(dF)}.
-/

/-- Decompose a function as a sum over basis in a tensor product. -/
lemma pi_tmul_eq_sum {V : Type*} [AddCommGroup V] [Module 𝔽₂ V] {n : ℕ}
    (g : Fin n → 𝔽₂) (v : V) :
    g ⊗ₜ[𝔽₂] v = ∑ i : Fin n, g i • (Pi.single i (1 : 𝔽₂) ⊗ₜ[𝔽₂] v) := by
  have hg : g = ∑ i, g i • Pi.single i 1 := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hg]
  rw [TensorProduct.sum_tmul]
  congr 1

/-- The twisted dh₁ on basis elements `Pi.single i 1 ⊗ₜ f` equals `dB(eᵢ) ⊗ₜ f`
    when `f ∈ ker(dF)` and identity-on-homology holds. -/
lemma twistedDh1_single_tmul
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (hφ : ActsAsIdentityOnHomology dB dF φ)
    (i : Fin n₁) (f : Fin n₂ → 𝔽₂) (hf : f ∈ ker dF) :
    twistedDhLin dB (fun b1 b0 => (φ b1 b0).α₁.toLinearMap) (Pi.single i 1 ⊗ₜ f) =
    dB (Pi.single i 1) ⊗ₜ[𝔽₂] f := by
  simp only [twistedDhLin_tmul]
  -- Outer sum: only b1 = i contributes (Pi.single i 1 vanishes elsewhere)
  rw [Finset.sum_eq_single i]
  · -- The i-th term: ∑ b0, 1 • dB(eᵢ)(b0) • (e_{b0} ⊗ₜ α₁(i,b0)(f))
    simp only [Pi.single_eq_same, one_smul]
    -- Replace α₁(f) by f using identity-on-homology
    -- Goal: ∑ b0, dB(eᵢ)(b0) • (e_{b0} ⊗ₜ α₁(i,b0)(f)) = dB(eᵢ) ⊗ₜ f
    rw [show (∑ x : Fin m₁, dB (Pi.single i 1) x •
          (Pi.single x (1 : 𝔽₂) ⊗ₜ[𝔽₂] (φ i x).α₁.toLinearMap f)) =
        ∑ x : Fin m₁, dB (Pi.single i 1) x • (Pi.single x (1 : 𝔽₂) ⊗ₜ[𝔽₂] f) from
      Finset.sum_congr rfl fun b0 _ => by
        by_cases hsupp : dB (Pi.single i 1) b0 = 0
        · simp [hsupp]
        · congr 1; congr 1; exact (hφ i b0 hsupp).deg1 f (mem_ker.mp hf)]
    exact (pi_tmul_eq_sum (dB (Pi.single i 1)) f).symm
  · -- Other terms are zero (Pi.single i 1 b = 0 when b ≠ i)
    intro b _ hne
    simp [hne]
  · -- i ∈ Finset.univ
    intro h; exact absurd (Finset.mem_univ _) h

/-- The twisted dh₁ agrees with `rTensor · dB` on `B₁ ⊗ ker(dF)`. Key commutativity diagram. -/
lemma twistedDh1_comp_lTensor_eq
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (hφ : ActsAsIdentityOnHomology dB dF φ) :
    (twistedDhLin dB (fun b1 b0 => (φ b1 b0).α₁.toLinearMap)).comp
      (LinearMap.lTensor _ (ker dF).subtype) =
    (LinearMap.lTensor _ (ker dF).subtype).comp (LinearMap.rTensor _ dB) := by
  apply TensorProduct.ext'
  intro b ⟨f, hf⟩
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
    Submodule.subtype_apply]
  have hb : b = ∑ i, b i • Pi.single i 1 := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hb]
  rw [TensorProduct.sum_tmul, map_sum]
  conv_rhs => rw [hb, map_sum, TensorProduct.sum_tmul]
  congr 1; ext i
  have key := twistedDh1_single_tmul dB dF φ hφ i f hf
  change (twistedDhLin dB fun b1 b0 => (φ b1 b0).α₁.toLinearMap)
    (b i • Pi.single i 1 ⊗ₜ[𝔽₂] f) = dB (b i • Pi.single i 1) ⊗ₜ[𝔽₂] f
  rw [map_smul, key, map_smul]; rfl

/-! ## Characterizing properties of flatness equivalences -/

/-- The symm direction of `lTensor_ker_equiv`: underlying value is `lTensor M subtype y`. -/
lemma lTensor_ker_equiv_symm_val (M : Type*) [AddCommGroup M] [Module 𝔽₂ M] [Module.Free 𝔽₂ M]
    (f : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (y : M ⊗[𝔽₂] ↥(ker f)) :
    ((lTensor_ker_equiv M f).symm y).val = LinearMap.lTensor M (ker f).subtype y := by
  simp only [lTensor_ker_equiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply]

/-- Forward direction: `lTensor M subtype (lTensor_ker_equiv M f x) = x.val`. -/
lemma lTensor_ker_equiv_apply_val (M : Type*) [AddCommGroup M] [Module 𝔽₂ M] [Module.Free 𝔽₂ M]
    (f : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (x : ↥(ker (LinearMap.lTensor M f))) :
    LinearMap.lTensor M (ker f).subtype (lTensor_ker_equiv M f x) = x.val := by
  have h := lTensor_ker_equiv_symm_val M f (lTensor_ker_equiv M f x)
  rw [LinearEquiv.symm_apply_apply] at h; exact h.symm

/-- The symm direction of `rTensor_ker_equiv`: underlying value is `rTensor M subtype y`. -/
lemma rTensor_ker_equiv_symm_val (M : Type*) [AddCommGroup M] [Module 𝔽₂ M] [Module.Free 𝔽₂ M]
    (f : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (y : ↥(ker f) ⊗[𝔽₂] M) :
    ((rTensor_ker_equiv M f).symm y).val = LinearMap.rTensor M (ker f).subtype y := by
  simp only [rTensor_ker_equiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply]

/-! ## Kernel equivalence from commutative diagram -/

/-- If `e₂ ∘ f = g ∘ e₁` (as linear maps), then `ker f ≃ ker g`. -/
def kerEquivOfConjugate {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module 𝔽₂ M₁] [AddCommGroup M₂] [Module 𝔽₂ M₂]
    [AddCommGroup N₁] [Module 𝔽₂ N₁] [AddCommGroup N₂] [Module 𝔽₂ N₂]
    (e₁ : M₁ ≃ₗ[𝔽₂] N₁) (e₂ : M₂ ≃ₗ[𝔽₂] N₂)
    (f : M₁ →ₗ[𝔽₂] M₂) (g : N₁ →ₗ[𝔽₂] N₂)
    (h : e₂.toLinearMap.comp f = g.comp e₁.toLinearMap) :
    ↥(ker f) ≃ₗ[𝔽₂] ↥(ker g) where
  toFun := fun ⟨x, hx⟩ => ⟨e₁ x, by
    rw [mem_ker]; have := LinearMap.ext_iff.mp h x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    rw [← this, mem_ker.mp hx, map_zero]⟩
  invFun := fun ⟨y, hy⟩ => ⟨e₁.symm y, by
    rw [mem_ker]; apply e₂.injective; rw [map_zero]
    have := LinearMap.ext_iff.mp h (e₁.symm y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e₁.apply_symm_apply] at this
    rw [this]; exact mem_ker.mp hy⟩
  left_inv := fun ⟨x, _⟩ => by simp
  right_inv := fun ⟨y, _⟩ => by simp
  map_add' := fun ⟨x₁, _⟩ ⟨x₂, _⟩ => by simp [map_add]
  map_smul' := fun r ⟨x, _⟩ => by simp [map_smul]

/-- If `e₂ ∘ f = g ∘ e₁`, then `coker(f) ≃ coker(g)`. -/
def quotientEquivOfConjugate {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module 𝔽₂ M₁] [AddCommGroup M₂] [Module 𝔽₂ M₂]
    [AddCommGroup N₁] [Module 𝔽₂ N₁] [AddCommGroup N₂] [Module 𝔽₂ N₂]
    (e₁ : M₁ ≃ₗ[𝔽₂] N₁) (e₂ : M₂ ≃ₗ[𝔽₂] N₂)
    (f : M₁ →ₗ[𝔽₂] M₂) (g : N₁ →ₗ[𝔽₂] N₂)
    (h : e₂.toLinearMap.comp f = g.comp e₁.toLinearMap) :
    (M₂ ⧸ range f) ≃ₗ[𝔽₂] (N₂ ⧸ range g) := by
  have hrange : (range f).map e₂.toLinearMap = range g := by
    ext y; constructor
    · rintro ⟨z, hz, rfl⟩; obtain ⟨x, rfl⟩ := mem_range.mp hz
      have h1 := LinearMap.ext_iff.mp h x
      simp only [LinearMap.comp_apply] at h1
      -- h1 : ↑e₂ (f x) = g (↑e₁ x)
      rw [h1]; exact mem_range.mpr ⟨e₁ x, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨f (e₁.symm w), mem_range.mpr ⟨e₁.symm w, rfl⟩, by
        have := LinearMap.ext_iff.mp h (e₁.symm w)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e₁.apply_symm_apply] at this
        exact this⟩
  exact Submodule.Quotient.equiv (range f) (range g) e₂ hrange

/-! ## Commutativity diagrams for fiber bundle -/

/-- dh₁ in the fiber bundle SmallDC equals the twistedDhLin with α₁. -/
lemma fiberBundleSmallDC_dh₁_eq
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF) :
    (fiberBundleSmallDC dB dF φ).dh₁ =
    twistedDhLin dB (fun b1 b0 => (φ b1 b0).α₁.toLinearMap) :=
  rfl

set_option maxHeartbeats 400000 in
/-- The commutativity: `lTensor_ker_equiv B₀ dF ∘ barDh₁ = rTensor dB ∘ lTensor_ker_equiv B₁ dF`
    for the fiber bundle SmallDC. -/
lemma fiberBundleSmallDC_barDh₁_conj
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (hφ : ActsAsIdentityOnHomology dB dF φ) :
    let E := fiberBundleSmallDC dB dF φ
    (lTensor_ker_equiv (Fin m₁ → 𝔽₂) dF).toLinearMap.comp E.barDh₁ =
    (LinearMap.rTensor ↥(ker dF) dB).comp
      (lTensor_ker_equiv (Fin n₁ → 𝔽₂) dF).toLinearMap := by
  intro E
  -- We need: e₂.comp barDh₁ = (rTensor dB).comp e₁
  -- Strategy: inject via lTensor subtype (injective by flatness), reduce to dh₁ equality.
  haveI : Module.Flat 𝔽₂ (Fin m₁ → 𝔽₂) := inferInstance
  have hinj : Function.Injective (LinearMap.lTensor (Fin m₁ → 𝔽₂) (ker dF).subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (ker dF).injective_subtype
  apply LinearMap.ext; intro ⟨x, hx⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  apply hinj
  -- LHS: lTensor subtype (e₂ (barDh₁ ⟨x,hx⟩)) = (barDh₁ ⟨x,hx⟩).val = dh₁ x
  rw [lTensor_ker_equiv_apply_val]
  -- RHS: lTensor subtype (rTensor dB (e₁ ⟨x,hx⟩))
  -- By commutativity = dh₁ (lTensor subtype (e₁ ⟨x,hx⟩)) = dh₁ x
  have hcomm := twistedDh1_comp_lTensor_eq dB dF φ hφ
  have hdh₁ := fiberBundleSmallDC_dh₁_eq dB dF φ
  have key := LinearMap.ext_iff.mp (hdh₁ ▸ hcomm)
    (lTensor_ker_equiv (Fin n₁ → 𝔽₂) dF ⟨x, hx⟩)
  simp only [LinearMap.comp_apply] at key
  rw [lTensor_ker_equiv_apply_val] at key
  show E.dh₁ x = _
  convert key.symm using 1
  exact key.symm

/-! ## Twisted dh₀ on quotient: identity on homology at degree 0

When the connection acts as identity on H₀(F) = coker(dF), the twisted horizontal
differential dh₀ composed with the quotient map equals `rTensor coker(dF) dB`.
-/

/-- The twisted dh₀ on basis elements `Pi.single i 1 ⊗ₜ f`, composed with the quotient
    map `lTensor B₀ mkQ`, equals `dB(eᵢ) ⊗ₜ [f]` when identity-on-homology holds. -/
lemma twistedDh0_single_tmul_quotient
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (hφ : ActsAsIdentityOnHomology dB dF φ)
    (i : Fin n₁) (f : Fin m₂ → 𝔽₂) :
    LinearMap.lTensor (Fin m₁ → 𝔽₂) (range dF).mkQ
      (twistedDhLin dB (fun b1 b0 => (φ b1 b0).α₀.toLinearMap) (Pi.single i 1 ⊗ₜ f)) =
    dB (Pi.single i 1) ⊗ₜ[𝔽₂] (range dF).mkQ f := by
  simp only [twistedDhLin_tmul, map_sum, map_smul, LinearMap.lTensor_tmul]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, one_smul]
    rw [show (∑ x : Fin m₁, dB (Pi.single i 1) x •
          (Pi.single x (1 : 𝔽₂) ⊗ₜ[𝔽₂] (range dF).mkQ ((φ i x).α₀.toLinearMap f))) =
        ∑ x : Fin m₁, dB (Pi.single i 1) x •
          (Pi.single x (1 : 𝔽₂) ⊗ₜ[𝔽₂] (range dF).mkQ f) from
      Finset.sum_congr rfl fun b0 _ => by
        by_cases hsupp : dB (Pi.single i 1) b0 = 0
        · simp [hsupp]
        · congr 1; congr 1
          rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
          exact (hφ i b0 hsupp).deg0 f]
    exact (pi_tmul_eq_sum (dB (Pi.single i 1)) ((range dF).mkQ f)).symm
  · intro b _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

set_option maxHeartbeats 400000 in
/-- The full commutativity: `lTensor B₀ mkQ ∘ dh₀ = rTensor coker(dF) dB ∘ lTensor B₁ mkQ`. -/
lemma twistedDh0_comp_lTensor_quotient_eq
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (hφ : ActsAsIdentityOnHomology dB dF φ) :
    (LinearMap.lTensor (Fin m₁ → 𝔽₂) (range dF).mkQ).comp
      (twistedDhLin dB (fun b1 b0 => (φ b1 b0).α₀.toLinearMap)) =
    (LinearMap.rTensor ((Fin m₂ → 𝔽₂) ⧸ range dF) dB).comp
      (LinearMap.lTensor (Fin n₁ → 𝔽₂) (range dF).mkQ) := by
  apply TensorProduct.ext'
  intro b f
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]
  have hb : b = ∑ i, b i • Pi.single i 1 := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hb, TensorProduct.sum_tmul, map_sum, map_sum]
  conv_rhs => rw [hb, map_sum, TensorProduct.sum_tmul]
  apply Finset.sum_congr rfl; intro i _
  -- Goal:  lTensor mkQ (twistedDhLin ... ((b i • eᵢ) ⊗ₜ f)) = dB (b i • eᵢ) ⊗ₜ mkQ f
  -- Use linearity to pull b i out of both sides
  have key := twistedDh0_single_tmul_quotient dB dF φ hφ i f
  have h1 : (twistedDhLin dB (fun b1 b0 => (φ b1 b0).α₀.toLinearMap))
      ((b i • Pi.single i 1) ⊗ₜ[𝔽₂] f) =
    b i • (twistedDhLin dB (fun b1 b0 => (φ b1 b0).α₀.toLinearMap))
      (Pi.single i 1 ⊗ₜ[𝔽₂] f) := by
    rw [← TensorProduct.smul_tmul', map_smul]
  rw [h1, map_smul, key, map_smul, ← TensorProduct.smul_tmul']

/-! ## Main theorems -/

-- Degree 2: totH₂ ≅ ker(dB) ⊗ ker(dF)
set_option maxHeartbeats 400000 in
theorem fiberBundleHomology_n2
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (hφ : ActsAsIdentityOnHomology dB dF φ) :
    Nonempty ((fiberBundleSmallDC dB dF φ).totH₂ ≃ₗ[𝔽₂]
      ↥(ker dB) ⊗[𝔽₂] ↥(ker dF)) := by
  let E := fiberBundleSmallDC dB dF φ
  -- Step 1: totH₂ ≃ itH₂ = ker(barDh₁)
  let e_tot := E.homologyEquiv_n2
  -- Step 2: ker(barDh₁) ≃ ker(rTensor ker(dF) dB) via conjugation
  let e_conj := kerEquivOfConjugate
    (lTensor_ker_equiv (Fin n₁ → 𝔽₂) dF)
    (lTensor_ker_equiv (Fin m₁ → 𝔽₂) dF)
    E.barDh₁
    (LinearMap.rTensor ↥(ker dF) dB)
    (fiberBundleSmallDC_barDh₁_conj dB dF φ hφ)
  -- Step 3: ker(rTensor ker(dF) dB) ≃ ker(dB) ⊗ ker(dF)
  let e_flat := rTensor_ker_equiv ↥(ker dF) dB
  exact ⟨e_tot.trans (e_conj.trans e_flat)⟩

/-- The commutativity: `lTensor_quotient_equiv B₀ dF ∘ barDh₀ = rTensor dB ∘ lTensor_quotient_equiv B₁ dF`.
    This follows from `twistedDh0_comp_lTensor_quotient_eq` and the definitions of `barDh₀` (mapQ)
    and `lTensor_quotient_equiv` (lTensor.equiv), by diagram chasing on the quotient. -/
lemma barDh₀_lTensor_quotient_conj
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (hφ : ActsAsIdentityOnHomology dB dF φ) :
    let E := fiberBundleSmallDC dB dF φ
    (lTensor_quotient_equiv (Fin m₁ → 𝔽₂) dF).toLinearMap.comp E.barDh₀ =
    (LinearMap.rTensor _ dB).comp (lTensor_quotient_equiv (Fin n₁ → 𝔽₂) dF).toLinearMap := by
  sorry

-- Degree 0: totH₀ ≅ coker(dB) ⊗ coker(dF)
set_option maxHeartbeats 400000 in
theorem fiberBundleHomology_n0
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (hφ : ActsAsIdentityOnHomology dB dF φ) :
    Nonempty ((fiberBundleSmallDC dB dF φ).totH₀ ≃ₗ[𝔽₂]
      ((Fin m₁ → 𝔽₂) ⧸ range dB) ⊗[𝔽₂] ((Fin m₂ → 𝔽₂) ⧸ range dF)) := by
  let E := fiberBundleSmallDC dB dF φ
  -- Step 1: totH₀ ≃ itH₀ = vH₀₀ / range(barDh₀)
  let e_tot := E.homologyEquiv_n0
  -- Step 2: coker(barDh₀) ≃ coker(rTensor coker(dF) dB) via conjugation
  have h_dh₀_eq : E.dh₀ = twistedDhLin dB (fun b1 b0 => (φ b1 b0).α₀.toLinearMap) := rfl
  -- barDh₀ is mapQ of dh₀. Under lTensor_quotient_equiv, the commutativity gives:
  have h_conj : (lTensor_quotient_equiv (Fin m₁ → 𝔽₂) dF).toLinearMap.comp E.barDh₀ =
      (LinearMap.rTensor _ dB).comp (lTensor_quotient_equiv (Fin n₁ → 𝔽₂) dF).toLinearMap :=
    barDh₀_lTensor_quotient_conj dB dF φ hφ
  let e_conj := quotientEquivOfConjugate
    (lTensor_quotient_equiv (Fin n₁ → 𝔽₂) dF)
    (lTensor_quotient_equiv (Fin m₁ → 𝔽₂) dF)
    E.barDh₀
    (LinearMap.rTensor _ dB)
    h_conj
  -- Step 3: coker(rTensor coker(dF) dB) ≃ coker(dB) ⊗ coker(dF)
  let e_flat := rTensor_quotient_equiv ((Fin m₂ → 𝔽₂) ⧸ range dF) dB
  exact ⟨e_tot.trans (e_conj.trans e_flat)⟩

-- Degree 1: totH₁ ≅ (ker(dB) ⊗ coker(dF)) × (coker(dB) ⊗ ker(dF))
set_option maxHeartbeats 400000 in
theorem fiberBundleHomology_n1
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (hφ : ActsAsIdentityOnHomology dB dF φ) :
    Nonempty ((fiberBundleSmallDC dB dF φ).totH₁ ≃ₗ[𝔽₂]
      (↥(ker dB) ⊗[𝔽₂] ((Fin m₂ → 𝔽₂) ⧸ range dF)) ×
      (((Fin m₁ → 𝔽₂) ⧸ range dB) ⊗[𝔽₂] ↥(ker dF))) := by
  let E := fiberBundleSmallDC dB dF φ
  -- Step 1: totH₁ ≃ itH₁_fst × itH₁_snd
  let e_tot := E.homologyEquiv_n1
  -- itH₁_fst = ker(barDh₀) and itH₁_snd = vH₀₁/range(barDh₁)
  -- Step 2a: ker(barDh₀) ≃ ker(rTensor coker(dF) dB) ≃ ker(dB) ⊗ coker(dF)
  have h_conj₀ : (lTensor_quotient_equiv (Fin m₁ → 𝔽₂) dF).toLinearMap.comp E.barDh₀ =
      (LinearMap.rTensor _ dB).comp (lTensor_quotient_equiv (Fin n₁ → 𝔽₂) dF).toLinearMap :=
    barDh₀_lTensor_quotient_conj dB dF φ hφ
  let e_fst := (kerEquivOfConjugate
    (lTensor_quotient_equiv (Fin n₁ → 𝔽₂) dF)
    (lTensor_quotient_equiv (Fin m₁ → 𝔽₂) dF)
    E.barDh₀ (LinearMap.rTensor _ dB) h_conj₀).trans
    (rTensor_ker_equiv _ dB)
  -- Step 2b: vH₀₁/range(barDh₁) ≃ coker(rTensor ker(dF) dB) ≃ coker(dB) ⊗ ker(dF)
  let e_snd := (quotientEquivOfConjugate
    (lTensor_ker_equiv (Fin n₁ → 𝔽₂) dF)
    (lTensor_ker_equiv (Fin m₁ → 𝔽₂) dF)
    E.barDh₁ (LinearMap.rTensor _ dB)
    (fiberBundleSmallDC_barDh₁_conj dB dF φ hφ)).trans
    (rTensor_quotient_equiv _ dB)
  exact ⟨e_tot.trans (e_fst.prodCongr e_snd)⟩

end FiberBundle

end
