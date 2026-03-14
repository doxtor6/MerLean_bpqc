import MerLeanBpqc.Definitions.Def_23_BalancedProductChainComplex
import MerLeanBpqc.Definitions.Def_25_InvariantLabeling
import MerLeanBpqc.Definitions.Def_8_CycleGraph
import MerLeanBpqc.Definitions.Def_15_TannerCodeLocalSystem
import MerLeanBpqc.Definitions.Def_4_CSSCode
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Definition 26: Balanced Product Tanner Cycle Code

The balanced product Tanner cycle code is `C(X,L) ⊗_{ℤ_ℓ} C(C_ℓ)` (Def_23), a quantum
CSS code whose total complex has three terms corresponding to physical qubits (`C_1`),
`Z`-checks (`∂_2^Tot`), and `X`-checks (`∂_1^Tot`).
-/

open CategoryTheory
open scoped TensorProduct

noncomputable section

namespace BalancedProductTannerCycleCode

variable {H : Type} [Group H] [Fintype H] [DecidableEq H]
variable (X : GraphWithGroupAction H)
variable {s : ℕ} (Λ : X.CellLabeling s)

abbrev C1 := ModuleCat.of 𝔽₂ (X.graph.cells 1 → 𝔽₂)
abbrev C0 := ModuleCat.of 𝔽₂ (X.graph.cells 0 → Fin s → 𝔽₂)

def cellLocalView (v : X.graph.cells 0) :
    (X.graph.cells 1 → 𝔽₂) →ₗ[𝔽₂] (Fin s → 𝔽₂) where
  toFun c i := c ((Λ v).symm i).val
  map_add' c₁ c₂ := by ext i; simp [Pi.add_apply]
  map_smul' r c := by ext i; simp [Pi.smul_apply]

def tannerDifferential :
    (X.graph.cells 1 → 𝔽₂) →ₗ[𝔽₂] (X.graph.cells 0 → Fin s → 𝔽₂) where
  toFun c v := cellLocalView X Λ v c
  map_add' c₁ c₂ := by ext v i; simp [cellLocalView, Pi.add_apply]
  map_smul' r c := by ext v i; simp [cellLocalView, Pi.smul_apply]

/-! ## Direct chain complex constructions -/

private def tannerObj (s : ℕ) : ℤ → ModuleCat 𝔽₂
  | (1 : ℤ) => ModuleCat.of 𝔽₂ (X.graph.cells 1 → 𝔽₂)
  | (0 : ℤ) => ModuleCat.of 𝔽₂ (X.graph.cells 0 → Fin s → 𝔽₂)
  | (Int.ofNat (_ + 2)) => ModuleCat.of 𝔽₂ PUnit
  | (Int.negSucc _) => ModuleCat.of 𝔽₂ PUnit

private def tannerMor (s : ℕ) (Λ : X.CellLabeling s) :
    (i j : ℤ) → (tannerObj X s i ⟶ tannerObj X s j)
  | 1, 0 => ModuleCat.ofHom (tannerDifferential X Λ)
  | _, _ => 0

private lemma tannerMor_zero (s : ℕ) (Λ : X.CellLabeling s) {i j : ℤ}
    (h : ¬(i = 1 ∧ j = 0)) :
    tannerMor X s Λ i j = 0 := by
  match i, j with
  | 1, 0 => exact absurd ⟨rfl, rfl⟩ h
  | 0, _ => rfl
  | 1, (Int.ofNat (_ + 1)) => rfl
  | 1, (Int.negSucc _) => rfl
  | (Int.ofNat (_ + 2)), _ => rfl
  | (Int.negSucc _), _ => rfl

def tannerCodeComplex : ChainComplex𝔽₂ where
  X := tannerObj X s
  d := tannerMor X s Λ
  shape i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    exact tannerMor_zero X s Λ (fun ⟨hi, hj⟩ => hij (by omega))
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.down_Rel] at hij hjk
    by_cases h : i = 1 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h
      have : k = -1 := by omega
      subst this
      show tannerMor X s Λ 1 0 ≫ tannerMor X s Λ 0 (-1) = 0
      have : tannerMor X s Λ 0 (-1) = 0 :=
        tannerMor_zero X s Λ (by rintro ⟨h1, h2⟩; exact absurd h1 (by omega))
      rw [this]; simp
    · rw [tannerMor_zero X s Λ h]; simp

/-- The Tanner code chain complex has trivial (PUnit) module at degrees outside {0, 1}. -/
lemma tannerCodeComplex_X_subsingleton {p : ℤ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    Subsingleton ↑((tannerCodeComplex X Λ).X p) := by
  match p with
  | (0 : ℤ) => exact absurd rfl hp0
  | (1 : ℤ) => exact absurd rfl hp1
  | Int.ofNat (_ + 2) => show Subsingleton PUnit; exact inferInstance
  | Int.negSucc _ => show Subsingleton PUnit; exact inferInstance

/-! ## H-actions -/

def actionC1 : Representation 𝔽₂ H (X.graph.cells 1 → 𝔽₂) where
  toFun h :=
    { toFun := fun c e => c (h⁻¹ • e)
      map_add' := fun c₁ c₂ => by ext e; simp [Pi.add_apply]
      map_smul' := fun r c => by ext e; simp [Pi.smul_apply] }
  map_one' := by ext c e; simp
  map_mul' g₁ g₂ := by ext c e; simp [mul_inv_rev, mul_smul]

def actionC0 : Representation 𝔽₂ H (X.graph.cells 0 → Fin s → 𝔽₂) where
  toFun h :=
    { toFun := fun f v => f (h⁻¹ • v)
      map_add' := fun f₁ f₂ => by ext v i; simp [Pi.add_apply]
      map_smul' := fun r f => by ext v i; simp [Pi.smul_apply] }
  map_one' := by ext f v; simp
  map_mul' g₁ g₂ := by ext f v; simp [mul_inv_rev, mul_smul]

lemma tannerDifferential_equivariant (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
    (h : H) :
    tannerDifferential X Λ ∘ₗ (actionC1 X h) =
    (actionC0 X (s := s) h) ∘ₗ tannerDifferential X Λ := by
  ext c v i
  simp only [LinearMap.comp_apply, tannerDifferential, LinearMap.coe_mk, AddHom.coe_mk,
    actionC1, actionC0, MonoidHom.coe_mk, OneHom.coe_mk]
  simp only [cellLocalView, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  have hinv := hΛ v h⁻¹ ((Λ v).symm i)
  simp only [Equiv.apply_symm_apply] at hinv
  have : (Λ (h⁻¹ • v)).symm i =
    ⟨h⁻¹ • ((Λ v).symm i).val,
      X.smul_incident_of_incident v ((Λ v).symm i).val h⁻¹ ((Λ v).symm i).prop⟩ := by
    apply (Λ (h⁻¹ • v)).injective
    rw [Equiv.apply_symm_apply]
    exact hinv.symm
  rw [this]

private def tannerAction (s : ℕ) : ∀ (i : ℤ), Representation 𝔽₂ H ↥(tannerObj X s i)
  | (1 : ℤ) => actionC1 X
  | (0 : ℤ) => actionC0 X (s := s)
  | (Int.ofNat (_ + 2)) => 1
  | (Int.negSucc _) => 1

def tannerCodeHEquivariant (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ) :
    HEquivariantChainComplex H where
  complex := tannerCodeComplex X Λ
  action := tannerAction X s
  equivariant := by
    intro i j h
    by_cases h10 : i = 1 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h10
      show (tannerMor X s Λ 1 0).hom ∘ₗ (tannerAction X s 1 h) =
           (tannerAction X s 0 h) ∘ₗ (tannerMor X s Λ 1 0).hom
      show (ModuleCat.ofHom (tannerDifferential X Λ)).hom ∘ₗ actionC1 X h =
           actionC0 X (s := s) h ∘ₗ (ModuleCat.ofHom (tannerDifferential X Λ)).hom
      simp only [ModuleCat.hom_ofHom]
      exact tannerDifferential_equivariant X Λ hΛ h
    · have hd : (tannerCodeComplex X Λ).d i j = 0 := by
        change tannerMor X s Λ i j = 0
        exact tannerMor_zero X s Λ h10
      rw [hd]
      simp [ModuleCat.hom_zero]

/-! ## Cycle graph chain complex (direct construction) -/

variable (ℓ : ℕ) [NeZero ℓ]

private def cycleObj : ℤ → ModuleCat 𝔽₂
  | (0 : ℤ) => ModuleCat.of 𝔽₂ (Fin ℓ → 𝔽₂)
  | (1 : ℤ) => ModuleCat.of 𝔽₂ (Fin ℓ → 𝔽₂)
  | (Int.ofNat (_ + 2)) => ModuleCat.of 𝔽₂ PUnit
  | (Int.negSucc _) => ModuleCat.of 𝔽₂ PUnit

private def cycleMor : (i j : ℤ) → (cycleObj ℓ i ⟶ cycleObj ℓ j)
  | 1, 0 => ModuleCat.ofHom (CycleGraph.differential ℓ)
  | _, _ => 0

private lemma cycleMor_zero {i j : ℤ} (h : ¬(i = 1 ∧ j = 0)) :
    cycleMor ℓ i j = 0 := by
  match i, j with
  | 1, 0 => exact absurd ⟨rfl, rfl⟩ h
  | 0, _ => rfl
  | 1, (Int.ofNat (_ + 1)) => rfl
  | 1, (Int.negSucc _) => rfl
  | (Int.ofNat (_ + 2)), _ => rfl
  | (Int.negSucc _), _ => rfl

def cycleComplex : ChainComplex𝔽₂ where
  X := cycleObj ℓ
  d := cycleMor ℓ
  shape i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    exact cycleMor_zero ℓ (fun ⟨hi, hj⟩ => hij (by omega))
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.down_Rel] at hij hjk
    by_cases h : i = 1 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h
      have : k = -1 := by omega
      subst this
      show cycleMor ℓ 1 0 ≫ cycleMor ℓ 0 (-1) = 0
      have : cycleMor ℓ 0 (-1) = 0 :=
        cycleMor_zero ℓ (by rintro ⟨h1, h2⟩; exact absurd h1 (by omega))
      rw [this]; simp
    · rw [cycleMor_zero ℓ h]; simp

/-- The cycle graph chain complex has trivial (PUnit) module at degrees outside {0, 1}. -/
lemma cycleComplex_X_subsingleton {p : ℤ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    Subsingleton ↑((cycleComplex ℓ).X p) := by
  match p with
  | (0 : ℤ) => exact absurd rfl hp0
  | (1 : ℤ) => exact absurd rfl hp1
  | Int.ofNat (_ + 2) => show Subsingleton PUnit; exact inferInstance
  | Int.negSucc _ => show Subsingleton PUnit; exact inferInstance

/-! ## H-action on Cycle Graph -/

variable [MulAction H (Fin ℓ)]

/-- The `H`-action on `Fin ℓ` is compatible with the cycle graph boundary:
`h • pred(i) = pred(h • i)` where `pred(i) = ⟨(i + ℓ - 1) % ℓ, _⟩`. -/
def CycleCompatibleAction : Prop :=
  ∀ (h : H) (i : Fin ℓ),
    h • (⟨(i.val + ℓ - 1) % ℓ, Nat.mod_lt _ (NeZero.pos ℓ)⟩ : Fin ℓ) =
      ⟨((h • i).val + ℓ - 1) % ℓ, Nat.mod_lt _ (NeZero.pos ℓ)⟩

def cycleChainAction : Representation 𝔽₂ H (Fin ℓ → 𝔽₂) where
  toFun h :=
    { toFun := fun f i => f (h⁻¹ • i)
      map_add' := fun f₁ f₂ => by ext i; simp [Pi.add_apply]
      map_smul' := fun r f => by ext i; simp [Pi.smul_apply] }
  map_one' := by ext f i; simp
  map_mul' g₁ g₂ := by ext f i; simp [mul_inv_rev, mul_smul]

private def cycleAction' : ∀ (i : ℤ), Representation 𝔽₂ H ↥(cycleObj ℓ i)
  | (0 : ℤ) => cycleChainAction ℓ
  | (1 : ℤ) => cycleChainAction ℓ
  | (Int.ofNat (_ + 2)) => 1
  | (Int.negSucc _) => 1

private lemma cycle_differential_equivariant (hcompat : CycleCompatibleAction (H := H) ℓ)
    (h : H) :
    CycleGraph.differential ℓ ∘ₗ (cycleChainAction ℓ h) =
    (cycleChainAction ℓ h) ∘ₗ CycleGraph.differential ℓ := by
  ext f i
  simp only [LinearMap.comp_apply, cycleChainAction, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, CycleGraph.differential_apply]
  -- LHS: f (h⁻¹ • i) + f (h⁻¹ • ⟨(i.val + ℓ - 1) % ℓ, _⟩)
  -- RHS: f (h⁻¹ • i) + f ⟨((h⁻¹ • i).val + ℓ - 1) % ℓ, _⟩
  congr 1
  congr 1
  rw [hcompat h⁻¹ i]

def cycleGraphHEquivariant (hcompat : CycleCompatibleAction (H := H) ℓ) :
    HEquivariantChainComplex H where
  complex := cycleComplex ℓ
  action := cycleAction' ℓ
  equivariant := by
    intro i j h
    by_cases h10 : i = 1 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h10
      show (cycleMor ℓ 1 0).hom ∘ₗ (cycleAction' ℓ 1 h) =
           (cycleAction' ℓ 0 h) ∘ₗ (cycleMor ℓ 1 0).hom
      show (ModuleCat.ofHom (CycleGraph.differential ℓ)).hom ∘ₗ cycleChainAction ℓ h =
           cycleChainAction ℓ h ∘ₗ (ModuleCat.ofHom (CycleGraph.differential ℓ)).hom
      simp only [ModuleCat.hom_ofHom]
      exact cycle_differential_equivariant ℓ hcompat h
    · have hd : (cycleComplex ℓ).d i j = 0 := by
        change cycleMor ℓ i j = 0
        exact cycleMor_zero ℓ h10
      rw [hd]
      simp [ModuleCat.hom_zero]

/-! ## The Balanced Product Tanner Cycle Code -/

/-- The balanced product Tanner cycle code `C(X,L) ⊗_{ℤ_ℓ} C(C_ℓ)`, a quantum CSS code.
Requires `ℓ ≥ 3` odd, an `H`-invariant labeling, and a compatible `H`-action on the cycle graph.
The total complex has three terms: `C₂ → C₁ → C₀` where physical qubits correspond to `C₁`,
Z-checks are given by `∂₂ : C₂ → C₁`, and X-checks are given by `∂₁ : C₁ → C₀`. -/
def balancedProductTannerCycleCode
    (hℓ_ge : ℓ ≥ 3) (hℓ_odd : ℓ % 2 = 1)
    (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
    (hcompat : CycleCompatibleAction (H := H) ℓ) :
    ChainComplex𝔽₂ :=
  (tannerCodeHEquivariant X Λ hΛ).balancedProductComplex
    (cycleGraphHEquivariant ℓ hcompat)

/-! ## Abbreviations for the H-equivariant complexes -/

variable (hℓ_ge : ℓ ≥ 3) (hℓ_odd : ℓ % 2 = 1)
variable (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
variable (hcompat : CycleCompatibleAction (H := H) ℓ)

private abbrev tannerHEq := tannerCodeHEquivariant X Λ hΛ
private abbrev cycleHEq := cycleGraphHEquivariant ℓ hcompat

/-! ## Tensor product identifications

The balanced product double complex `C(X,L) ⊠_{ℤ_ℓ} C(C_ℓ)` has entries at `(p,q)` where
`p ∈ {0,1}` (Tanner complex degrees) and `q ∈ {0,1}` (cycle complex degrees). The total complex
`Tot` has three non-trivial degrees:
- `C₂ = Tot_2 = (C ⊠ D)_{1,1} = C₁(X,L) ⊗_{ℤ_ℓ} C₁(C_ℓ)`
- `C₁ = Tot_1 = (C ⊠ D)_{1,0} ⊕ (C ⊠ D)_{0,1} = (C₁(X,L) ⊗_{ℤ_ℓ} C₀(C_ℓ)) ⊕ (C₀(X,L) ⊗_{ℤ_ℓ} C₁(C_ℓ))`
- `C₀ = Tot_0 = (C ⊠ D)_{0,0} = C₀(X,L) ⊗_{ℤ_ℓ} C₀(C_ℓ)`
-/

/-- `C₂ = C₁(X,L) ⊗_{ℤ_ℓ} C₁(C_ℓ)`, the balanced product of the degree-1 components. -/
theorem balancedProductTannerCycleCode_C2_eq :
    ((tannerHEq X Λ hΛ).balancedProductDoubleComplex (cycleHEq ℓ hcompat)).obj 1 1 =
    (tannerHEq X Λ hΛ).bpObj (cycleHEq ℓ hcompat) 1 1 := rfl

/-- `C₀ = C₀(X,L) ⊗_{ℤ_ℓ} C₀(C_ℓ)`, the balanced product of the degree-0 components. -/
theorem balancedProductTannerCycleCode_C0_eq :
    ((tannerHEq X Λ hΛ).balancedProductDoubleComplex (cycleHEq ℓ hcompat)).obj 0 0 =
    (tannerHEq X Λ hΛ).bpObj (cycleHEq ℓ hcompat) 0 0 := rfl

/-- The inclusion `C₁(X,L) ⊗_{ℤ_ℓ} C₀(C_ℓ) ↪ C₁` into the total complex at degree 1. -/
def ιC1_tanner_component :
    (tannerHEq X Λ hΛ).bpObj (cycleHEq ℓ hcompat) 1 0 ⟶
    (balancedProductTannerCycleCode X Λ ℓ hℓ_ge hℓ_odd hΛ hcompat).X 1 :=
  ((tannerHEq X Λ hΛ).balancedProductDoubleComplex (cycleHEq ℓ hcompat)).ιTotalComplex 1 0 1 (by omega)

/-- The inclusion `C₀(X,L) ⊗_{ℤ_ℓ} C₁(C_ℓ) ↪ C₁` into the total complex at degree 1. -/
def ιC1_cycle_component :
    (tannerHEq X Λ hΛ).bpObj (cycleHEq ℓ hcompat) 0 1 ⟶
    (balancedProductTannerCycleCode X Λ ℓ hℓ_ge hℓ_odd hΛ hcompat).X 1 :=
  ((tannerHEq X Λ hΛ).balancedProductDoubleComplex (cycleHEq ℓ hcompat)).ιTotalComplex 0 1 1 (by omega)

/-- The inclusion `C₁(X,L) ⊗_{ℤ_ℓ} C₁(C_ℓ) ↪ C₂` into the total complex at degree 2. -/
def ιC2_component :
    (tannerHEq X Λ hΛ).bpObj (cycleHEq ℓ hcompat) 1 1 ⟶
    (balancedProductTannerCycleCode X Λ ℓ hℓ_ge hℓ_odd hΛ hcompat).X 2 :=
  ((tannerHEq X Λ hΛ).balancedProductDoubleComplex (cycleHEq ℓ hcompat)).ιTotalComplex 1 1 2 (by omega)

/-- The inclusion `C₀(X,L) ⊗_{ℤ_ℓ} C₀(C_ℓ) ↪ C₀` into the total complex at degree 0. -/
def ιC0_component :
    (tannerHEq X Λ hΛ).bpObj (cycleHEq ℓ hcompat) 0 0 ⟶
    (balancedProductTannerCycleCode X Λ ℓ hℓ_ge hℓ_odd hΛ hcompat).X 0 :=
  ((tannerHEq X Λ hΛ).balancedProductDoubleComplex (cycleHEq ℓ hcompat)).ιTotalComplex 0 0 0 (by omega)

/-! ## CSS code structure

A chain complex `C₂ →[∂₂] C₁ →[∂₁] C₀` with `∂₁ ∘ ∂₂ = 0` determines a CSS code:
- Physical qubits correspond to `C₁`
- Z-checks are given by `∂₂ : C₂ → C₁`
- X-checks are given by `∂₁ : C₁ → C₀`
The CSS condition `∂₁ ∘ ∂₂ = 0` is automatic from the chain complex .
-/

/-- The Z-check map `∂₂ : C₂ → C₁` of the balanced product Tanner cycle code. -/
def zCheckMap :
    (balancedProductTannerCycleCode X Λ ℓ hℓ_ge hℓ_odd hΛ hcompat).X 2 ⟶
    (balancedProductTannerCycleCode X Λ ℓ hℓ_ge hℓ_odd hΛ hcompat).X 1 :=
  (balancedProductTannerCycleCode X Λ ℓ hℓ_ge hℓ_odd hΛ hcompat).d 2 1

/-- The X-check map `∂₁ : C₁ → C₀` of the balanced product Tanner cycle code. -/
def xCheckMap :
    (balancedProductTannerCycleCode X Λ ℓ hℓ_ge hℓ_odd hΛ hcompat).X 1 ⟶
    (balancedProductTannerCycleCode X Λ ℓ hℓ_ge hℓ_odd hΛ hcompat).X 0 :=
  (balancedProductTannerCycleCode X Λ ℓ hℓ_ge hℓ_odd hΛ hcompat).d 1 0

/-- The CSS condition: the composition of the X-check map and Z-check map is zero,
i.e., `∂₁ ∘ ∂₂ = 0`. This is the fundamental property that makes the code a valid
quantum CSS code. -/
theorem css_condition :
    zCheckMap X Λ ℓ hℓ_ge hℓ_odd hΛ hcompat ≫
    xCheckMap X Λ ℓ hℓ_ge hℓ_odd hΛ hcompat = 0 :=
  (balancedProductTannerCycleCode X Λ ℓ hℓ_ge hℓ_odd hΛ hcompat).d_comp_d 2 1 0

/-- The balanced product Tanner cycle code has `ℓ ≥ 3`. -/
theorem balancedProductTannerCycleCode_ℓ_ge
    (hℓ_ge : ℓ ≥ 3) : ℓ ≥ 3 := hℓ_ge

/-- The balanced product Tanner cycle code has `ℓ` odd. -/
theorem balancedProductTannerCycleCode_ℓ_odd
    (hℓ_odd : ℓ % 2 = 1) : ℓ % 2 = 1 := hℓ_odd

end BalancedProductTannerCycleCode

end
