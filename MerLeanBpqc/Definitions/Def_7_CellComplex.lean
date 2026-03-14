import MerLeanBpqc.Definitions.Def_1_ChainComplex
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.ZMod.Basic

/-!
# Definition 7: Cell Complex

A regular cell complex `X` consists of finite sets `X_n` for each `n ∈ ℤ` (with `X_n = ∅` for
all but finitely many `n`), whose elements are called `n`-cells, together with for each `n`-cell
`σ ∈ X_n` a subset `∂σ ⊆ X_{n-1}` (the set of `(n-1)`-cells in the boundary of `σ`).

The associated chain complex `C(X) = (C_•(X), ∂)` is defined by
`C_i(X) = ⊕_{σ ∈ X_i} 𝔽₂ σ` (the free `𝔽₂`-vector space on `X_i`)
and the differential `∂_n(σ) = Σ_{τ ∈ ∂σ} τ` for each `n`-cell `σ ∈ X_n`,
extended linearly. This satisfies the chain complex condition `∂_{n-1} ∘ ∂_n = 0`.

The homology of the cell complex is `H_i(X) = H_i(C(X))`.

## Main Definitions
- `CellComplex` — a regular cell complex with finite cell sets and boundary maps
- `CellComplex.differentialMap` — the differential `∂_n : C_n(X) → C_{n-1}(X)` as a linear map
- `CellComplex.differentialMap_comp` — proof that `∂_{n-1} ∘ ∂_n = 0`
- `CellComplex.chainComplex` — the associated chain complex `C(X)`
- `CellComplex.cellHomology` — the homology `H_i(X) = H_i(C(X))`
-/

open CategoryTheory

/-! ## Cell Complex Structure -/

/-- A regular cell complex `X` consists of finite sets `X_n` for each `n ∈ ℤ`,
whose elements are called `n`-cells, together with for each `n`-cell `σ ∈ X_n`
a subset `∂σ ⊆ X_{n-1}` (the boundary of `σ`). The chain complex condition
requires `∂_{n-1} ∘ ∂_n = 0`, which is encoded as: for every `n`-cell `σ`
and every `(n-2)`-cell `ρ`, the number of `(n-1)`-cells `τ` with `τ ∈ ∂σ`
and `ρ ∈ ∂τ` is even. -/
structure CellComplex where
  /-- The type of `n`-cells for each `n ∈ ℤ`. -/
  cells : ℤ → Type
  /-- Each `cells n` is a finite type. -/
  [cells_fintype : ∀ n, Fintype (cells n)]
  /-- Each `cells n` has decidable equality. -/
  [cells_deceq : ∀ n, DecidableEq (cells n)]
  /-- The boundary map: for each `n`-cell `σ`, the set of `(n-1)`-cells in `∂σ`. -/
  bdry : {n : ℤ} → cells n → Finset (cells (n - 1))
  /-- The chain complex condition: for every `n`-cell `σ` and every `(n-2)`-cell `ρ`,
  the number of `(n-1)`-cells `τ` with `τ ∈ ∂σ` and `ρ ∈ ∂τ` is even. -/
  bdry_bdry : ∀ (n : ℤ) (σ : cells n) (ρ : cells (n - 1 - 1)),
    Even (Finset.card (Finset.filter (fun τ : cells (n - 1) => ρ ∈ bdry τ) (bdry σ)))

attribute [instance] CellComplex.cells_fintype CellComplex.cells_deceq

namespace CellComplex

variable (X : CellComplex)

/-! ## The differential as a linear map -/

/-- The differential `∂_n : C_n(X) → C_{n-1}(X)` of the cell complex,
defined by `∂_n(f)(τ) = Σ_{σ : X_n | τ ∈ ∂σ} f(σ)` for `τ ∈ X_{n-1}`.
Equivalently, on a basis element `eσ`, `∂_n(eσ) = Σ_{τ ∈ ∂σ} eτ`.
Here `C_i(X) = cells i → 𝔽₂` is the free `𝔽₂`-vector space on `X_i`. -/
noncomputable def differentialMap (n : ℤ) :
    (X.cells n → 𝔽₂) →ₗ[𝔽₂] (X.cells (n - 1) → 𝔽₂) :=
  LinearMap.pi (fun τ =>
    ∑ σ ∈ Finset.univ.filter (fun σ => τ ∈ X.bdry σ),
      LinearMap.proj σ)

@[simp]
lemma differentialMap_apply (n : ℤ) (f : X.cells n → 𝔽₂) (τ : X.cells (n - 1)) :
    X.differentialMap n f τ =
      ∑ σ ∈ Finset.univ.filter (fun σ => τ ∈ X.bdry σ), f σ := by
  simp [differentialMap, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply]

/-! ## Chain complex condition: ∂_{n-1} ∘ ∂_n = 0 -/

/-- The chain complex condition `∂_{n-1} ∘ ∂_n = 0`. This follows from the
even boundary condition: for every `n`-cell `σ` and every `(n-2)`-cell `ρ`,
the number of `(n-1)`-cells `τ` with `τ ∈ ∂σ` and `ρ ∈ ∂τ` is even. -/
theorem differentialMap_comp (n : ℤ) :
    (X.differentialMap (n - 1)).comp (X.differentialMap n) = 0 := by
  ext f ρ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply, differentialMap_apply]
  -- Goal: ∑ τ ∈ univ.filter (ρ ∈ ∂·), (∑ σ ∈ univ.filter (τ ∈ ∂·), f σ) = 0
  -- Convert inner filtered sum to sum over univ
  conv_lhs => arg 2; ext τ; rw [Finset.sum_filter]
  -- Goal: ∑ τ ∈ univ.filter (ρ ∈ ∂·), (∑ σ ∈ univ, if τ ∈ ∂σ then f σ else 0) = 0
  -- Swap summation order (both finsets are fixed)
  rw [Finset.sum_comm]
  -- Goal: ∑ σ ∈ univ, (∑ τ ∈ univ.filter (ρ ∈ ∂·), if τ ∈ ∂σ then f σ else 0) = 0
  apply Finset.sum_eq_zero
  intro σ _
  -- Split the inner sum by the condition τ ∈ ∂σ
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  -- Goal: f σ * card(univ.filter (ρ ∈ ∂·) |>.filter (· ∈ ∂σ)) = 0
  -- Rewrite with filter_filter
  rw [Finset.filter_filter]
  -- Identify with bdry_bdry
  have hset : Finset.filter (fun τ => ρ ∈ X.bdry τ ∧ τ ∈ X.bdry σ) Finset.univ =
      (X.bdry σ).filter (fun τ => ρ ∈ X.bdry τ) := by
    ext τ; simp [Finset.mem_filter, and_comm]
  rw [hset]
  have heven := X.bdry_bdry n σ ρ
  rw [show ((X.bdry σ).filter (fun τ => ρ ∈ X.bdry τ)).card = (Finset.filter (fun τ => ρ ∈ X.bdry τ) (X.bdry σ)).card from rfl]
  have h0 : ((Finset.filter (fun τ => ρ ∈ X.bdry τ) (X.bdry σ)).card : 𝔽₂) = 0 :=
    heven.natCast_zmod_two
  rw [h0, zero_mul]

/-! ## The chain complex C(X) -/

/-- The `ModuleCat` object for degree `i`: `ModuleCat.of 𝔽₂ (cells i → 𝔽₂)`. -/
private noncomputable def complexObj (i : ℤ) : ModuleCat 𝔽₂ :=
  ModuleCat.of 𝔽₂ (X.cells i → 𝔽₂)

/-- The associated chain complex `C(X) = (C_•(X), ∂)` of a cell complex `X`.
The module in degree `i` is `C_i(X) = cells i → 𝔽₂` (the free `𝔽₂`-vector space
on the `i`-cells), and the differential `∂_n` maps `eσ ↦ Σ_{τ ∈ ∂σ} eτ`. -/
noncomputable def chainComplex : ChainComplex𝔽₂ where
  X i := X.complexObj i
  d i j :=
    if h : j + 1 = i then
      eqToHom (show X.complexObj i = X.complexObj (j + 1) by rw [← h]) ≫
        ModuleCat.ofHom (X.differentialMap (j + 1)) ≫
        eqToHom (show X.complexObj ((j + 1) - 1) = X.complexObj j by
          congr 1; omega)
    else 0
  shape i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    exact dif_neg hij
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.down_Rel] at hij hjk
    subst hij; subst hjk
    rw [dif_pos rfl, dif_pos rfl]
    -- Goal: (eqToHom _ ≫ ofHom d(k+1+1) ≫ eqToHom _) ≫ (eqToHom _ ≫ ofHom d(k+1) ≫ eqToHom _) = 0
    simp only [Category.assoc]
    -- Cancel the middle eqToHom ≫ eqToHom pair
    rw [← Category.assoc (eqToHom _) (eqToHom _) _,
        eqToHom_trans, eqToHom_refl, Category.id_comp]
    -- Goal: ofHom d(k+1+1) ≫ eqToHom _ ≫ ofHom d(k+1) ≫ eqToHom _ = 0
    -- Strip the rightmost eqToHom (iso) using comp_right_eq_zero
    rw [← Category.assoc _ _ (eqToHom _),
        ← Category.assoc _ _ (eqToHom _),
        Preadditive.IsIso.comp_right_eq_zero]
    -- Goal: ofHom d(k+1+1) ≫ eqToHom _ ≫ ofHom d(k+1) = 0
    -- Use dcongr_arg to rewrite ofHom d(k+1) as eqToHom ≫ ofHom d(k+1+1-1) ≫ eqToHom
    have hidx : k + 1 = k + 1 + 1 - 1 := by omega
    rw [dcongr_arg (fun n => ModuleCat.ofHom (X.differentialMap n)) hidx]
    -- Strip the rightmost eqToHom
    rw [← Category.assoc _ _ (eqToHom _),
        ← Category.assoc _ _ (eqToHom _),
        ← Category.assoc _ _ (eqToHom _),
        Preadditive.IsIso.comp_right_eq_zero]
    -- Goal: ofHom d(k+1+1) ≫ eqToHom _ ≫ eqToHom _ ≫ ofHom d(k+1+1-1) = 0
    -- Cancel the two eqToHom's in the middle
    rw [← Category.assoc (eqToHom _) (eqToHom _) _, eqToHom_trans]
    -- This eqToHom should be between definitionally equal types
    -- (k+1+1)-1 and k+1+1-1 are the same by parsing
    rw [eqToHom_refl, Category.id_comp]
    -- Goal: ofHom d(k+1+1) ≫ ofHom d(k+1+1-1) = 0
    rw [← ModuleCat.ofHom_comp, X.differentialMap_comp (k + 1 + 1)]
    rfl

/-! ## Homology of the cell complex -/

/-- The homology `H_i(X) = H_i(C(X))` of the cell complex, using the homology
definition from Def_1 applied to the associated chain complex. -/
noncomputable def cellHomology (i : ℤ) :=
  X.chainComplex.homology' i

end CellComplex
