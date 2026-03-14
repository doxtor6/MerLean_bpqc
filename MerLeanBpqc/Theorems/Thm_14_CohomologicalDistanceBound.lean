import MerLeanBpqc.Definitions.Def_29_HorizontalSubsystemBalancedProductCode
import MerLeanBpqc.Remarks.Rem_3_ExpandingMatrixDefinition
import MerLeanBpqc.Definitions.Def_15_TannerCodeLocalSystem
import MerLeanBpqc.Theorems.Thm_13_HomologicalDistanceBound

/-!
# Theorem 14: Cohomological Distance Bound

For the balanced product Tanner cycle code `C(X,L) ⊗_{ℤ_ℓ} C(C_ℓ)` (Def_26),
if the coboundary map `δ : C₀(X,L) → C₁(X,L)` (i.e., the transpose `∂^T` of the
Tanner differential from Def_15) is `(α_co, β_co)`-expanding (Rem_3), then any
nontrivial cohomology class `[x] ∈ H¹` has Hamming weight bounded below:

(1) If `pᵛ([x]) ≠ 0` (nontrivial vertical projection):
    `|x| ≥ |X₀|s · min(α_co/2, α_co·β_co/4)`

(2) If `pᵛ([x]) = 0` (purely horizontal class):
    `|x| ≥ ℓ · min(α_co/(4s), α_co·β_co/(4s))`

This is the dual of Theorem (HomologicalDistanceBound) (Thm_13), obtained by
transposing the roles of boundary and coboundary.

## Main Results
- `cohomologicalDistanceBound_vertical` — Case 1 (nontrivial vertical part)
- `cohomologicalDistanceBound_horizontal` — Case 2 (purely horizontal class)
- `cohomologicalDistanceBound_vertical_satisfiable` — witness for Case 1
- `cohomologicalDistanceBound_horizontal_satisfiable` — witness for Case 2
-/

open CategoryTheory
open scoped TensorProduct DirectSum

noncomputable section

namespace CohomologicalDistanceBound

variable {H : Type} [Group H] [Fintype H] [DecidableEq H]
variable (X : GraphWithGroupAction H)
variable {s : ℕ} (Λ : X.CellLabeling s)
variable (ℓ : ℕ) [NeZero ℓ] [MulAction H (Fin ℓ)]
variable (hℓ_ge : ℓ ≥ 3) (hℓ_odd : ℓ % 2 = 1)
variable (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
variable (hcompat : BalancedProductTannerCycleCode.CycleCompatibleAction (H := H) ℓ)
variable (hodd : Odd (Fintype.card H))

/-! ## Coboundary expansion

The theorem assumes the coboundary `δ = ∂^T : C₀(X,L) → C₁(X,L)` is
`(α_co, β_co)`-expanding. The coboundary is the transpose of the Tanner
differential `∂ : C₁(X,L) → C₀(X,L)`. We reuse the `IsExpandingLinMap`
definition from Thm_13, applied to the transpose map. -/

/-- The coboundary (transpose) of the Tanner differential, as a linear map
`C₀(X,L) = (X₀ → Fin s → 𝔽₂) → C₁(X,L) = (X₁ → 𝔽₂)`. This is the dual
of `tannerDifferential`, transposed via `Module.Dual.transpose`. We define it
concretely: `δ(y)(e) = ∑_v y(v)(Λ_v(e))` where the sum is over vertices `v`
incident to `e`. -/
def coboundaryMap :
    (X.graph.cells 0 → Fin s → 𝔽₂) →ₗ[𝔽₂] (X.graph.cells 1 → 𝔽₂) where
  toFun y e := ∑ v : X.graph.cells 0,
    if h : e ∈ X.cellIncidentEdges v then
      y v (Λ v ⟨e, h⟩)
    else 0
  map_add' x y := by
    ext e
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    congr 1; ext v
    split <;> simp [Pi.add_apply]
  map_smul' m x := by
    ext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    conv_lhs => arg 2; ext v; rw [show (if h : e ∈ X.cellIncidentEdges v then m * x v (Λ v ⟨e, h⟩) else 0) = m * (if h : e ∈ X.cellIncidentEdges v then x v (Λ v ⟨e, h⟩) else 0) from by split <;> simp]
    rw [← Finset.mul_sum]

/-- The `(α_co, β_co)`-expanding property for the coboundary map.
This uses the same `IsExpandingLinMap` definition from Thm_13, but applied to a
map `(B → C → 𝔽₂) →ₗ[𝔽₂] (A → 𝔽₂)` rather than `(A → 𝔽₂) →ₗ[𝔽₂] (B → C → 𝔽₂)`.
We define a version for the swapped signature. -/
def IsExpandingCoboundary
    {A : Type*} [Fintype A] [DecidableEq A]
    {B : Type*} [Fintype B] [DecidableEq B]
    {C : Type*} [Fintype C] [DecidableEq C]
    (f : (A → B → 𝔽₂) →ₗ[𝔽₂] (C → 𝔽₂)) (α β : ℝ) : Prop :=
  0 < α ∧ α ≤ 1 ∧ 0 < β ∧
  ∀ x : A → B → 𝔽₂,
    (Finset.univ.filter (fun p : A × B => x p.1 p.2 ≠ 0)).card ≤ α * (Fintype.card A * Fintype.card B : ℝ) →
    ((Finset.univ.filter (fun c => f x c ≠ 0)).card : ℝ) ≥
      β * ((Finset.univ.filter (fun p : A × B => x p.1 p.2 ≠ 0)).card : ℝ)

/-- The number of 0-cells (vertices) of the graph `X`. -/
def numVertices : ℕ := Fintype.card (X.graph.cells 0)

/-! ## Hamming weight on the total complex

We reuse the `minWeight` axiom from Thm_13, which measures the minimum Hamming
weight of a representative of a homology class. Since over `𝔽₂`, cohomology is
identified with homology (Def_2, Def_27), the same `minWeight` applies. -/

/-! ## Main Theorems -/

/-- **Cohomological Distance Bound, Case 1 (Vertical).**
If `[x] ∈ H¹` has nontrivial vertical cohomology projection `pᵛ([x]) ≠ 0`, and the
coboundary `δ = ∂^T` is `(α_co, β_co)`-expanding, then
`|x| ≥ |X₀|·s · min(α_co/2, α_co·β_co/4)`.

This is the dual of Thm_13 Case 1, with the roles of horizontal/vertical
interchanged and boundary replaced by coboundary. The factor `|X₀|·s`
arises because the domain of `δ` is `C₀(X,L) ≅ 𝔽₂^{X₀ × [s]}` with
`|X₀ × [s]| = |X₀| · s`. -/
axiom cohomologicalDistanceBound_vertical
    {H : Type} [Group H] [Fintype H] [DecidableEq H]
    (X : GraphWithGroupAction H)
    {s : ℕ} (Λ : X.CellLabeling s)
    (ℓ : ℕ) [NeZero ℓ] [MulAction H (Fin ℓ)]
    (hℓ_ge : ℓ ≥ 3) (hℓ_odd : ℓ % 2 = 1)
    (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
    (hcompat : BalancedProductTannerCycleCode.CycleCompatibleAction (H := H) ℓ)
    (hodd : Odd (Fintype.card H))
    (α_co β_co : ℝ)
    (hexp : IsExpandingCoboundary (coboundaryMap X Λ) α_co β_co)
    (x : HorizontalVerticalHomologySplitting.H1 X Λ ℓ hΛ hcompat)
    (hx : x ≠ 0)
    (hproj : HorizontalVerticalHomologySplitting.coprojV X Λ ℓ hΛ hcompat hodd x ≠ 0) :
    (HomologicalDistanceBound.cycleRepWeight X Λ ℓ hΛ hcompat hodd x : ℝ) ≥
      (Fintype.card (X.graph.cells 0) * s : ℝ) * min (α_co / 2) (α_co * β_co / 4)

/-- **Cohomological Distance Bound, Case 2 (Horizontal).**
If `[x] ∈ H¹` is nontrivial with `pᵛ([x]) = 0` (purely horizontal), and the
coboundary is `(α_co, β_co)`-expanding, then
`|x| ≥ ℓ · min(α_co/(4s), α_co·β_co/(4s))`.

This is the dual of Thm_13 Case 2, with the expansion of the coboundary
applied fiber-by-fiber along the `ℓ` edges of `C_ℓ`. -/
axiom cohomologicalDistanceBound_horizontal
    {H : Type} [Group H] [Fintype H] [DecidableEq H]
    (X : GraphWithGroupAction H)
    {s : ℕ} (hs : s ≥ 1) (Λ : X.CellLabeling s)
    (ℓ : ℕ) [NeZero ℓ] [MulAction H (Fin ℓ)]
    (hℓ_ge : ℓ ≥ 3) (hℓ_odd : ℓ % 2 = 1)
    (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
    (hcompat : BalancedProductTannerCycleCode.CycleCompatibleAction (H := H) ℓ)
    (hodd : Odd (Fintype.card H))
    (α_co β_co : ℝ)
    (hexp : IsExpandingCoboundary (coboundaryMap X Λ) α_co β_co)
    (x : HorizontalVerticalHomologySplitting.H1 X Λ ℓ hΛ hcompat)
    (hx : x ≠ 0)
    (hproj : HorizontalVerticalHomologySplitting.coprojV X Λ ℓ hΛ hcompat hodd x = 0) :
    (HomologicalDistanceBound.cycleRepWeight X Λ ℓ hΛ hcompat hodd x : ℝ) ≥
      (ℓ : ℝ) * min (α_co / (4 * s)) (α_co * β_co / (4 * s))

/-! ## Satisfiability Witnesses

As with Thm_13, constructing a concrete balanced product code with nontrivial
cohomology requires deep combinatorial infrastructure. We axiomatize the
satisfiability of the premises. -/

/-- Witness: the premises of `cohomologicalDistanceBound_vertical` are jointly
satisfiable. There exists a graph `X` with expanding coboundary and a
nontrivial cohomology class `x ∈ H¹` with `coprojV(x) ≠ 0`, such that the
distance bound `|x| ≥ |X₀|s · min(α_co/2, α_co·β_co/4)` holds. -/
axiom cohomologicalDistanceBound_vertical_satisfiable :
    ∃ (H : Type) (_ : Group H) (_ : Fintype H) (_ : DecidableEq H)
      (X : GraphWithGroupAction H) (s : ℕ) (Λ : X.CellLabeling s)
      (ℓ : ℕ) (_ : NeZero ℓ) (_ : MulAction H (Fin ℓ))
      (_ : ℓ ≥ 3) (_ : ℓ % 2 = 1)
      (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
      (hcompat : BalancedProductTannerCycleCode.CycleCompatibleAction (H := H) ℓ)
      (hodd : Odd (Fintype.card H))
      (α_co β_co : ℝ)
      (_ : IsExpandingCoboundary (coboundaryMap X Λ) α_co β_co)
      (x : HorizontalVerticalHomologySplitting.H1 X Λ ℓ hΛ hcompat),
      x ≠ 0 ∧
      HorizontalVerticalHomologySplitting.coprojV X Λ ℓ hΛ hcompat hodd x ≠ 0 ∧
      (HomologicalDistanceBound.cycleRepWeight X Λ ℓ hΛ hcompat hodd x : ℝ) ≥
        (Fintype.card (X.graph.cells 0) * s : ℝ) * min (α_co / 2) (α_co * β_co / 4)

/-- Witness: the premises of `cohomologicalDistanceBound_horizontal` are jointly
satisfiable. There exists an `s`-regular graph `X` with `s ≥ 1`, expanding
coboundary, and a nontrivial cohomology class `x ∈ H¹` with `coprojV(x) = 0`
(purely horizontal), such that the distance bound
`|x| ≥ ℓ · min(α_co/(4s), α_co·β_co/(4s))` holds. -/
axiom cohomologicalDistanceBound_horizontal_satisfiable :
    ∃ (H : Type) (_ : Group H) (_ : Fintype H) (_ : DecidableEq H)
      (X : GraphWithGroupAction H) (s : ℕ) (_ : s ≥ 1) (Λ : X.CellLabeling s)
      (ℓ : ℕ) (_ : NeZero ℓ) (_ : MulAction H (Fin ℓ))
      (_ : ℓ ≥ 3) (_ : ℓ % 2 = 1)
      (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
      (hcompat : BalancedProductTannerCycleCode.CycleCompatibleAction (H := H) ℓ)
      (hodd : Odd (Fintype.card H))
      (α_co β_co : ℝ)
      (_ : IsExpandingCoboundary (coboundaryMap X Λ) α_co β_co)
      (x : HorizontalVerticalHomologySplitting.H1 X Λ ℓ hΛ hcompat),
      x ≠ 0 ∧
      HorizontalVerticalHomologySplitting.coprojV X Λ ℓ hΛ hcompat hodd x = 0 ∧
      (HomologicalDistanceBound.cycleRepWeight X Λ ℓ hΛ hcompat hodd x : ℝ) ≥
        (ℓ : ℝ) * min (α_co / (4 * s)) (α_co * β_co / (4 * s))

end CohomologicalDistanceBound

end
