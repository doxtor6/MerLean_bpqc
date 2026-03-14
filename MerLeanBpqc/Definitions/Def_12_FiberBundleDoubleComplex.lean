import MerLeanBpqc.Definitions.Def_10_TotalComplex
import MerLeanBpqc.Definitions.Def_11_TensorProductDoubleComplex
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Definition 12: Fiber Bundle Double Complex

Let `B = (B₁ →[∂^B] B₀)` and `F = (F₁ →[∂^F] F₀)` be 1-complexes over `𝔽₂` (the base
and fiber), with canonical bases: `B₁ = 𝔽₂^{n₁}`, `B₀ = 𝔽₂^{m₁}`, `F₁ = 𝔽₂^{n₂}`,
`F₀ = 𝔽₂^{m₂}`.

A *chain automorphism* of `F` is a pair of invertible linear maps
`(α₁ : F₁ ≃ F₁, α₀ : F₀ ≃ F₀)` satisfying `∂^F ∘ α₁ = α₀ ∘ ∂^F`.

A *connection* `φ` assigns to each pair `(b¹ : Fin n₁, b⁰ : Fin m₁)` a chain automorphism
of `F`. The fiber bundle double complex `B ⊠_φ F` has objects `B_p ⊗ F_q`, vertical
differential `∂^v = id_B ⊗ ∂^F`, and twisted horizontal differential `∂^h_φ`.

The fiber bundle code is `B ⊗_φ F = Tot(B ⊠_φ F)`.

## Main Definitions
- `ChainAutomorphism` — chain automorphism of a 1-complex
- `Connection` — connection for the fiber bundle
- `twistedDhLin` — twisted horizontal differential as a linear map
- `twistedDh_comm_dv` — commutativity of differentials
- `fiberBundleDoubleComplex` — the double complex `B ⊠_φ F`
- `fiberBundleComplex` — the total complex `Tot(B ⊠_φ F)`
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace FiberBundle

variable {n₁ m₁ n₂ m₂ : ℕ}

/-! ## Chain Automorphism -/

/-- A chain automorphism of a 1-complex `F = (F₁ →[∂^F] F₀)` over `𝔽₂`, where `F₁ = 𝔽₂^{n₂}`
and `F₀ = 𝔽₂^{m₂}`. This is a pair of invertible linear maps satisfying
`∂^F ∘ α₁ = α₀ ∘ ∂^F`. -/
structure ChainAutomorphism (n₂ m₂ : ℕ)
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂)) where
  /-- The automorphism on `F₁ = 𝔽₂^{n₂}`. -/
  α₁ : (Fin n₂ → 𝔽₂) ≃ₗ[𝔽₂] (Fin n₂ → 𝔽₂)
  /-- The automorphism on `F₀ = 𝔽₂^{m₂}`. -/
  α₀ : (Fin m₂ → 𝔽₂) ≃ₗ[𝔽₂] (Fin m₂ → 𝔽₂)
  /-- The chain map condition: `∂^F ∘ α₁ = α₀ ∘ ∂^F`. -/
  comm : dF.comp α₁.toLinearMap = α₀.toLinearMap.comp dF

/-- The identity chain automorphism. -/
def ChainAutomorphism.id
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂)) :
    ChainAutomorphism n₂ m₂ dF where
  α₁ := LinearEquiv.refl 𝔽₂ _
  α₀ := LinearEquiv.refl 𝔽₂ _
  comm := by simp [LinearEquiv.refl_toLinearMap]

/-! ## Connection -/

/-- A connection for a fiber bundle. Assigns a chain automorphism of `F` to each pair
`(b¹ : Fin n₁, b⁰ : Fin m₁)`. Values outside `supp(∂^B e_{b¹})` are irrelevant. -/
def Connection (n₁ m₁ n₂ m₂ : ℕ)
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂)) :=
  Fin n₁ → Fin m₁ → ChainAutomorphism n₂ m₂ dF

/-- The trivial connection: `φ(b¹, b⁰) = id_F` for all pairs. -/
def Connection.trivial
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂)) :
    Connection n₁ m₁ n₂ m₂ dF :=
  fun _ _ => ChainAutomorphism.id dF

/-! ## Twisted horizontal differential -/

/-- The twisted horizontal differential `∂^h_φ : 𝔽₂^{n₁} ⊗ V → 𝔽₂^{m₁} ⊗ V`.
On a basis element `e_{b1} ⊗ f`, this gives
`Σ_{b0 ∈ supp(∂^B e_{b1})} e_{b0} ⊗ autComp(b1,b0)(f)`. -/
noncomputable def twistedDhLin {V : Type*} [AddCommGroup V] [Module 𝔽₂ V]
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (autComp : Fin n₁ → Fin m₁ → V →ₗ[𝔽₂] V) :
    (Fin n₁ → 𝔽₂) ⊗[𝔽₂] V →ₗ[𝔽₂] (Fin m₁ → 𝔽₂) ⊗[𝔽₂] V :=
  TensorProduct.lift
    { toFun := fun b =>
        { toFun := fun f =>
            ∑ b1 : Fin n₁, ∑ b0 : Fin m₁,
              (b b1) • ((dB (Pi.single b1 1) b0) •
                ((Pi.single b0 (1 : 𝔽₂)) ⊗ₜ[𝔽₂] (autComp b1 b0 f)))
          map_add' := by
            intro f g
            simp [map_add, TensorProduct.tmul_add, smul_add, Finset.sum_add_distrib]
          map_smul' := by
            intro r f
            simp [map_smul, TensorProduct.tmul_smul, smul_comm r, Finset.smul_sum,
              RingHom.id_apply] }
      map_add' := by
        intro x y; ext f
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Pi.add_apply,
          add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r x; ext f
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
          Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
        congr 1; ext b1; congr 1; ext b0
        rw [mul_smul] }

@[simp]
lemma twistedDhLin_tmul {V : Type*} [AddCommGroup V] [Module 𝔽₂ V]
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (autComp : Fin n₁ → Fin m₁ → V →ₗ[𝔽₂] V)
    (b : Fin n₁ → 𝔽₂) (f : V) :
    twistedDhLin dB autComp (b ⊗ₜ f) =
      ∑ b1 : Fin n₁, ∑ b0 : Fin m₁,
        (b b1) • ((dB (Pi.single b1 1) b0) •
          ((Pi.single b0 (1 : 𝔽₂)) ⊗ₜ[𝔽₂] (autComp b1 b0 f))) := by
  simp [twistedDhLin]

/-! ## Commutativity of differentials -/

/-- The twisted horizontal differential commutes with `id ⊗ ∂^F`. This is the key property
that makes `B ⊠_φ F` a valid double complex, and follows from the chain map condition. -/
lemma twistedDh_comm_dv
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF) :
    (twistedDhLin dB (fun b1 b0 => (φ b1 b0).α₀.toLinearMap)).comp
      (LinearMap.lTensor (Fin n₁ → 𝔽₂) dF) =
    (LinearMap.lTensor (Fin m₁ → 𝔽₂) dF).comp
      (twistedDhLin dB (fun b1 b0 => (φ b1 b0).α₁.toLinearMap)) := by
  apply TensorProduct.ext'
  intro b f
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, twistedDhLin_tmul]
  simp only [map_sum, map_smul, LinearMap.lTensor_tmul]
  congr 1; ext b1; congr 1; ext b0; congr 1; congr 1; congr 1
  have hcomm := (φ b1 b0).comm
  have := LinearMap.ext_iff.mp hcomm f
  simp only [LinearMap.comp_apply] at this
  exact this.symm

/-! ## Size functions for the graded object -/

/-- The dimension of the base space at degree `p`: `n₁` at degree 1, `m₁` at degree 0,
and `0` elsewhere. -/
def baseSize (n₁ m₁ : ℕ) (p : ℤ) : ℕ :=
  if p = 1 then n₁ else if p = 0 then m₁ else 0

/-- The dimension of the fiber space at degree `q`: `n₂` at degree 1, `m₂` at degree 0,
and `0` elsewhere. -/
def fiberSize (n₂ m₂ : ℕ) (q : ℤ) : ℕ :=
  if q = 1 then n₂ else if q = 0 then m₂ else 0

@[simp] lemma baseSize_one : baseSize n₁ m₁ 1 = n₁ := by simp [baseSize]
@[simp] lemma baseSize_zero : baseSize n₁ m₁ 0 = m₁ := by simp [baseSize]
@[simp] lemma fiberSize_one : fiberSize n₂ m₂ 1 = n₂ := by simp [fiberSize]
@[simp] lemma fiberSize_zero : fiberSize n₂ m₂ 0 = m₂ := by simp [fiberSize]

/-- The graded object underlying the fiber bundle double complex:
`(p, q) ↦ 𝔽₂^{baseSize(p)} ⊗ 𝔽₂^{fiberSize(q)}`. -/
noncomputable def fbObj (n₁ m₁ n₂ m₂ : ℕ) : ℤ × ℤ → ModuleCat 𝔽₂ :=
  fun ⟨p, q⟩ => ModuleCat.of 𝔽₂ ((Fin (baseSize n₁ m₁ p) → 𝔽₂) ⊗[𝔽₂] (Fin (fiberSize n₂ m₂ q) → 𝔽₂))

/-! ## Vertical differential (id ⊗ ∂^F) -/

/-- The fiber differential at degree `(q, q')`: this is `dF` when `q = 1, q' = 0`,
and `0` otherwise. Matches the shape of a 1-complex. -/
noncomputable def fiberDiff (n₂ m₂ : ℕ)
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂)) (q q' : ℤ) :
    (Fin (fiberSize n₂ m₂ q) → 𝔽₂) →ₗ[𝔽₂] (Fin (fiberSize n₂ m₂ q') → 𝔽₂) :=
  if hq : q = 1 ∧ q' = 0 then
    hq.1 ▸ hq.2 ▸ dF
  else 0

/-- The vertical differential `id_B ⊗ ∂^F` as a ModuleCat morphism. -/
noncomputable def fbDv (n₁ m₁ n₂ m₂ : ℕ)
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (p : ℤ) (q q' : ℤ) :
    fbObj n₁ m₁ n₂ m₂ (p, q) ⟶ fbObj n₁ m₁ n₂ m₂ (p, q') :=
  ModuleCat.ofHom (LinearMap.lTensor _ (fiberDiff n₂ m₂ dF q q'))

/-! ## Automorphism component selection -/

/-- Given a connection φ, extract the automorphism component at fiber degree `q`:
`α₁` when `q = 1`, `α₀` when `q = 0`, and `id` otherwise. -/
noncomputable def autAtDeg
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (q : ℤ) (b1 : Fin n₁) (b0 : Fin m₁) :
    (Fin (fiberSize n₂ m₂ q) → 𝔽₂) →ₗ[𝔽₂] (Fin (fiberSize n₂ m₂ q) → 𝔽₂) :=
  if hq : q = 1 then
    hq ▸ (φ b1 b0).α₁.toLinearMap
  else if hq : q = 0 then
    hq ▸ (φ b1 b0).α₀.toLinearMap
  else LinearMap.id

/-! ## Twisted horizontal differential -/

/-- The twisted horizontal differential as a ModuleCat morphism.
For `p = 1, p' = 0`, this applies `twistedDhLin` with the connection-twisted automorphisms.
For all other positions, it is zero. -/
noncomputable def fbDh (n₁ m₁ n₂ m₂ : ℕ)
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (p p' : ℤ) (q : ℤ) :
    fbObj n₁ m₁ n₂ m₂ (p, q) ⟶ fbObj n₁ m₁ n₂ m₂ (p', q) :=
  if hp : p = 1 ∧ p' = 0 then
    hp.1 ▸ hp.2 ▸
      ModuleCat.ofHom (twistedDhLin dB (fun b1 b0 => autAtDeg dF φ q b1 b0))
  else 0

/-! ## Shape conditions -/

private lemma fbDh_shape
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (p p' : ℤ) (hp : ¬(ComplexShape.down ℤ).Rel p p') (q : ℤ) :
    fbDh n₁ m₁ n₂ m₂ dB dF φ p p' q = 0 := by
  unfold fbDh
  have h : ¬(p = 1 ∧ p' = 0) := by
    intro ⟨hp1, hp0⟩; apply hp; change p' + 1 = p; omega
  rw [dif_neg h]

private lemma fiberDiff_shape (n₂ m₂ : ℕ)
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (q q' : ℤ) (hq : ¬(ComplexShape.down ℤ).Rel q q') :
    fiberDiff n₂ m₂ dF q q' = 0 := by
  simp only [fiberDiff]
  split_ifs with h
  · exfalso; apply hq; change q' + 1 = q; omega
  · rfl

private lemma fbDv_shape
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (p : ℤ) (q q' : ℤ) (hq : ¬(ComplexShape.down ℤ).Rel q q') :
    fbDv n₁ m₁ n₂ m₂ dF p q q' = 0 := by
  unfold fbDv
  rw [fiberDiff_shape n₂ m₂ dF q q' hq, LinearMap.lTensor_zero]
  rfl

/-! ## d² = 0 conditions -/

private lemma fbDh_comp
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (p p' p'' q : ℤ) :
    fbDh n₁ m₁ n₂ m₂ dB dF φ p p' q ≫ fbDh n₁ m₁ n₂ m₂ dB dF φ p' p'' q = 0 := by
  -- At most one factor is nonzero: p=1,p'=0 and p'=1,p''=0 can't both hold
  unfold fbDh
  by_cases h1 : p = 1 ∧ p' = 0
  · -- First factor nonzero, second must be zero since p' = 0 ≠ 1
    have h2 : ¬(p' = 1 ∧ p'' = 0) := by omega
    rw [dif_pos h1, dif_neg h2, comp_zero]
  · -- First factor is zero
    rw [dif_neg h1, zero_comp]

private lemma fiberDiff_comp (n₂ m₂ : ℕ)
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂)) (q q' q'' : ℤ) :
    (fiberDiff n₂ m₂ dF q' q'').comp (fiberDiff n₂ m₂ dF q q') = 0 := by
  unfold fiberDiff
  by_cases h1 : q = 1 ∧ q' = 0
  · -- fiberDiff q q' is nonzero, but fiberDiff q' q'' must be zero since q' = 0 ≠ 1
    have h2 : ¬(q' = 1 ∧ q'' = 0) := by omega
    rw [dif_pos h1, dif_neg h2, LinearMap.zero_comp]
  · rw [dif_neg h1, LinearMap.comp_zero]

private lemma lTensor_fiberDiff_comp (n₁ m₁ n₂ m₂ : ℕ)
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂)) (p : ℤ) (q q' q'' : ℤ) :
    (LinearMap.lTensor (Fin (baseSize n₁ m₁ p) → 𝔽₂) (fiberDiff n₂ m₂ dF q' q'')).comp
      (LinearMap.lTensor (Fin (baseSize n₁ m₁ p) → 𝔽₂) (fiberDiff n₂ m₂ dF q q')) = 0 := by
  rw [← LinearMap.lTensor_comp, fiberDiff_comp, LinearMap.lTensor_zero]

private lemma fbDv_comp
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (p : ℤ) (q q' q'' : ℤ) :
    fbDv n₁ m₁ n₂ m₂ dF p q q' ≫ fbDv n₁ m₁ n₂ m₂ dF p q' q'' = 0 := by
  simp only [fbDv]
  ext x
  simp only [ModuleCat.comp_apply, ModuleCat.ofHom_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply]
  exact LinearMap.ext_iff.mp (lTensor_fiberDiff_comp n₁ m₁ n₂ m₂ dF p q q' q'') x

/-! ## Commutativity: ∂^h ∘ ∂^v = ∂^v ∘ ∂^h -/

private lemma fbDh_comm_fbDv
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF)
    (p p' q q' : ℤ) :
    fbDh n₁ m₁ n₂ m₂ dB dF φ p p' q ≫ fbDv n₁ m₁ n₂ m₂ dF p' q q' =
    fbDv n₁ m₁ n₂ m₂ dF p q q' ≫ fbDh n₁ m₁ n₂ m₂ dB dF φ p p' q' := by
  by_cases hp : p = 1 ∧ p' = 0
  · -- hp : p = 1 ∧ p' = 0. Need commutativity of twisted dh with dv
    obtain ⟨rfl, rfl⟩ := hp
    have hdif : (1 : ℤ) = 1 ∧ (0 : ℤ) = 0 := ⟨rfl, rfl⟩
    simp only [fbDh, dif_pos hdif, fbDv]
    by_cases hq : q = 1 ∧ q' = 0
    · -- The nontrivial case: (p,p',q,q') = (1,0,1,0)
      obtain ⟨rfl, rfl⟩ := hq
      have hqif : (1 : ℤ) = 1 ∧ (0 : ℤ) = 0 := ⟨rfl, rfl⟩
      ext x
      simp only [ModuleCat.comp_apply, ModuleCat.ofHom_apply, fiberDiff, dif_pos hqif,
        autAtDeg, dite_true, ↓reduceDIte]
      have hcomm := twistedDh_comm_dv dB dF φ
      have := LinearMap.ext_iff.mp hcomm x
      simp only [LinearMap.comp_apply] at this
      exact this.symm
    · -- fiberDiff is zero, both sides are zero
      have hfz : fiberDiff n₂ m₂ dF q q' = 0 := by
        simp only [fiberDiff, dif_neg hq]
      have hdv1 : fbDv n₁ m₁ n₂ m₂ dF 1 q q' = 0 := by
        unfold fbDv; rw [hfz, LinearMap.lTensor_zero]; rfl
      have hdv0 : fbDv n₁ m₁ n₂ m₂ dF 0 q q' = 0 := by
        unfold fbDv; rw [hfz, LinearMap.lTensor_zero]; rfl
      -- Unfold back to fbDv level, then use hdv0/hdv1
      change fbDh n₁ m₁ n₂ m₂ dB dF φ 1 0 q ≫ fbDv n₁ m₁ n₂ m₂ dF 0 q q' =
        fbDv n₁ m₁ n₂ m₂ dF 1 q q' ≫ fbDh n₁ m₁ n₂ m₂ dB dF φ 1 0 q'
      rw [hdv0, hdv1, comp_zero, zero_comp]
  · -- fbDh is zero on both sides
    simp only [fbDh, dif_neg hp, zero_comp, comp_zero]

/-! ## The fiber bundle double complex -/

/-- The fiber bundle double complex `B ⊠_φ F` as a `DoubleComplex𝔽₂`.
Objects are `𝔽₂^{baseSize(p)} ⊗ 𝔽₂^{fiberSize(q)}`, vertical differential is `id ⊗ ∂^F`,
and horizontal differential is the connection-twisted `∂^h_φ`. -/
noncomputable def fiberBundleDoubleComplex
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF) : DoubleComplex𝔽₂ :=
  HomologicalComplex₂.ofGradedObject
    (ComplexShape.down ℤ) (ComplexShape.down ℤ)
    (fbObj n₁ m₁ n₂ m₂)
    (fun p p' q => fbDh n₁ m₁ n₂ m₂ dB dF φ p p' q)
    (fun p q q' => fbDv n₁ m₁ n₂ m₂ dF p q q')
    (fun p p' hp q => fbDh_shape dB dF φ p p' hp q)
    (fun p q q' hq => fbDv_shape dF p q q' hq)
    (fun p p' p'' q => fbDh_comp dB dF φ p p' p'' q)
    (fun p q q' q'' => fbDv_comp dF p q q' q'')
    (fun p p' q q' => fbDh_comm_fbDv dB dF φ p p' q q')

/-! ## HasTotal instance -/

/-- The fiber bundle double complex has a total complex. -/
noncomputable instance fiberBundleDoubleComplex_hasTotal
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF) :
    (fiberBundleDoubleComplex dB dF φ).HasTotal (ComplexShape.down ℤ) := by
  unfold HomologicalComplex₂.HasTotal
  intro j
  infer_instance

/-! ## The fiber bundle complex (total complex) -/

/-- The fiber bundle complex `B ⊗_φ F = Tot(B ⊠_φ F)`.
This is the total complex of the fiber bundle double complex. -/
noncomputable def fiberBundleComplex
    (dB : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dF : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂))
    (φ : Connection n₁ m₁ n₂ m₂ dF) : ChainComplex𝔽₂ :=
  (fiberBundleDoubleComplex dB dF φ).totalComplex

end FiberBundle
