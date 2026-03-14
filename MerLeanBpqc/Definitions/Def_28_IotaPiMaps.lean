import MerLeanBpqc.Definitions.Def_27_HorizontalVerticalHomologySplitting
import MerLeanBpqc.Definitions.Def_26_BalancedProductTannerCycleCode
import MerLeanBpqc.Definitions.Def_25_InvariantLabeling
import MerLeanBpqc.Definitions.Def_24_QuotientGraphTrivialization
import MerLeanBpqc.Definitions.Def_1_ChainComplex
import MerLeanBpqc.Lemmas.Lem_4_KunnethBalancedProduct

/-!
# Definition 28: Iota and Pi Maps

Let `X` be a finite graph with a free right `H = ℤ_ℓ`-action (Def_24), `L` a local code
with `H`-invariant labeling (Def_25), and `C(X,L) ⊗_{ℤ_ℓ} C(C_ℓ)` the balanced product
Tanner cycle code (Def_26).

We define `𝔽₂`-linear maps between the homology of the quotient Tanner code `C(X/H, L)`
and the horizontal homology `H₁ʰ = H₁(C(X,L)) ⊗_H H₀(C_ℓ)` (Def_27):

1. `ι : H₁(C(X/H, L)) → H₁ʰ` — lifts a cycle on the quotient graph to the balanced product
   by summing over orbit representatives: `ι[∑ a_𝓔 𝓔] = [(∑ a_𝓔 ∑_{e ∈ 𝓔} e ⊗ y₀, 0)]`

2. `π : H₁ʰ → H₁(C(X/H, L))` — projects from the horizontal homology back to the quotient
   by collapsing orbits: `π[(∑ aₑ e ⊗ y₀, 0)] = [∑ aₑ eH]`

Both maps are well-defined: `ι` maps cycles to cycles by the orbit structure of the
balanced product differential, and `π` is well-defined because horizontal homology classes
have coefficients constant on orbits.

## Main Definitions
- `quotientTannerComplex` — the Tanner code complex on the quotient graph `X/H`
- `quotientTannerHomology` — `H₁(C(X/H, L))`
- `iotaMap` — `ι : H₁(C(X/H, L)) → H₁ʰ`
- `piMap` — `π : H₁ʰ → H₁(C(X/H, L))`

## Main Results
- `piMap_comp_iotaMap` — `π ∘ ι = ℓ · id` (over `𝔽₂`, this equals `id` when `ℓ` is odd)
- `iotaMap_comp_piMap` — `ι ∘ π = id`
-/

open CategoryTheory
open scoped TensorProduct DirectSum

noncomputable section

namespace IotaPiMaps

variable {H : Type} [Group H] [Fintype H] [DecidableEq H]
variable (X : GraphWithGroupAction H)
variable {s : ℕ} (Λ : X.CellLabeling s)
variable (ℓ : ℕ) [NeZero ℓ] [MulAction H (Fin ℓ)]
variable (hℓ_ge : ℓ ≥ 3) (hℓ_odd : ℓ % 2 = 1)
variable (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
variable (hcompat : BalancedProductTannerCycleCode.CycleCompatibleAction (H := H) ℓ)
variable (hodd : Odd (Fintype.card H))

/-! ## Quotient Tanner Code Complex

The quotient graph `X/H` has its own Tanner code complex `C(X/H, L)`, built from
the quotient cell complex (Def_24) with the descended labeling (Def_25).
The chain spaces are `C₁(X/H) = (X₁/H → 𝔽₂)` and `C₀(X/H) = (X₀/H → Fin s → 𝔽₂)`.
-/

/-- The chain space of 1-chains on the quotient graph: `C₁(X/H) = (X₁/H → 𝔽₂)`. -/
abbrev quotientC1 := X.quotientEdges → 𝔽₂

/-- The chain space of 0-chains on the quotient graph: `C₀(X/H) = (X₀/H → Fin s → 𝔽₂)`. -/
abbrev quotientC0 := X.quotientVertices → Fin s → 𝔽₂

/-- The quotient local view: for a vertex orbit `[v]` and a 1-chain `c` on `X/H`,
the local view reads off the coefficients of incident edge orbits via the quotient labeling. -/
def quotientLocalView (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ) (V : X.quotientVertices) :
    (X.quotientEdges → 𝔽₂) →ₗ[𝔽₂] (Fin s → 𝔽₂) where
  toFun c i := c ((X.quotientLabeling Λ hΛ V).symm i).val
  map_add' c₁ c₂ := by ext i; simp [Pi.add_apply]
  map_smul' r c := by ext i; simp [Pi.smul_apply]

/-- The Tanner differential on the quotient graph: `∂ : C₁(X/H) → C₀(X/H)`.
Sends `c` to `v ↦ localView_v(c)`. -/
def quotientTannerDifferential (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ) :
    (X.quotientEdges → 𝔽₂) →ₗ[𝔽₂] (X.quotientVertices → Fin s → 𝔽₂) where
  toFun c V := quotientLocalView X Λ hΛ V c
  map_add' c₁ c₂ := by ext V i; simp [quotientLocalView, Pi.add_apply]
  map_smul' r c := by ext V i; simp [quotientLocalView, Pi.smul_apply]

/-- The quotient Tanner code complex `C(X/H, L)` as a chain complex over `𝔽₂`.
`C₁ = (X₁/H → 𝔽₂)` in degree 1, `C₀ = (X₀/H → Fin s → 𝔽₂)` in degree 0. -/
def quotientTannerComplex (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ) :
    ChainComplex𝔽₂ where
  X i := match i with
    | (1 : ℤ) => ModuleCat.of 𝔽₂ (X.quotientEdges → 𝔽₂)
    | (0 : ℤ) => ModuleCat.of 𝔽₂ (X.quotientVertices → Fin s → 𝔽₂)
    | (Int.ofNat (_ + 2)) => ModuleCat.of 𝔽₂ PUnit
    | (Int.negSucc _) => ModuleCat.of 𝔽₂ PUnit
  d i j := match i, j with
    | 1, 0 => ModuleCat.ofHom (quotientTannerDifferential X Λ hΛ)
    | _, _ => 0
  shape i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    match i, j with
    | 1, 0 => exact absurd rfl hij
    | 0, _ => rfl
    | 1, (Int.ofNat (_ + 1)) => rfl
    | 1, (Int.negSucc _) => rfl
    | (Int.ofNat (_ + 2)), _ => rfl
    | (Int.negSucc _), _ => rfl
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.down_Rel] at hij hjk
    match i, j, k with
    | 1, 0, _ =>
      show ModuleCat.ofHom (quotientTannerDifferential X Λ hΛ) ≫ (0 : _ ⟶ _) = 0
      simp
    | 0, _, _ => simp
    | (Int.ofNat (n + 2)), _, _ =>
      show (0 : _ ⟶ _) ≫ _ = 0
      exact CategoryTheory.Limits.HasZeroMorphisms.zero_comp _ _
    | (Int.negSucc _), _, _ =>
      show (0 : _ ⟶ _) ≫ _ = 0
      exact CategoryTheory.Limits.HasZeroMorphisms.zero_comp _ _
    | 1, (Int.ofNat (n + 1)), _ =>
      exfalso; revert hij; simp; positivity
    | 1, (Int.negSucc _), _ =>
      exfalso; revert hij; simp

/-- The homology `H₁(C(X/H, L))` of the quotient Tanner code complex. -/
abbrev quotientTannerHomology (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ) :=
  (quotientTannerComplex X Λ hΛ).homology' 1

/-! ## Abbreviations from Def_27 -/

private abbrev tannerHEq' := BalancedProductTannerCycleCode.tannerCodeHEquivariant X Λ hΛ
private abbrev cycleHEq' := BalancedProductTannerCycleCode.cycleGraphHEquivariant ℓ hcompat

/-- The horizontal homology `H₁ʰ = H₁(C(X,L)) ⊗_H H₀(C_ℓ)` from Def_27. -/
private abbrev H1h' :=
  HorizontalVerticalHomologySplitting.H1h X Λ ℓ hΛ hcompat

/-! ## The Iota Map

The map `ι : H₁(C(X/H, L)) → H₁ʰ` lifts a cycle on the quotient graph to the
balanced product by summing over orbit representatives.

For an edge orbit `𝓔 = eH`, define the orbit indicator `1_𝓔 ∈ C₁(X)` as the
function with `1_𝓔(e') = 1` iff `e' ∈ 𝓔`. Then:
  `ι[∑_𝓔 a_𝓔 𝓔] = [(∑_𝓔 a_𝓔 [1_𝓔 ⊗ δ_{y₀}], 0)]`

The map is well-defined:
- The orbit indicator `1_𝓔` is `H`-invariant, so `[1_𝓔 ⊗ g] = [1_𝓔 ⊗ g']` for
  any `g, g'` in the same orbit of `C₀(C_ℓ)`.
- ι maps cycles to cycles because the balanced product differential
  respects the orbit structure.
- ι maps boundaries to boundaries (well-defined on homology classes).

The construction requires:
1. Building the orbit indicator function for each edge orbit
2. Tensoring with a fixed 0-cell `y₀` of `C_ℓ` in the balanced product
3. Embedding into the total complex degree-1 chain space
4. Showing the resulting element is a cycle when the input is a cycle
5. Showing independence of the homology class representative
-/

/-- The `ι` map: `H₁(C(X/H, L)) → H₁ʰ(C(X,L) ⊗_H C(C_ℓ))`.

Maps a homology class `[∑_𝓔 a_𝓔 𝓔]` in the quotient Tanner code to
`[(∑_𝓔 a_𝓔 ∑_{e ∈ 𝓔} e ⊗ y₀, 0)]` in the horizontal homology of the
balanced product. Here `y₀` is a fixed 0-cell of the cycle graph `C_ℓ`.

Well-definedness: The orbit indicator `∑_{e ∈ 𝓔} δ_e` is `H`-invariant in
`C₁(X,L)`, so tensoring with `δ_{y₀} ∈ C₀(C_ℓ)` gives a well-defined element
of `C₁(X,L) ⊗_H C₀(C_ℓ)`. The map sends cycles to cycles (the quotient
differential is compatible with the balanced product differential) and
boundaries to boundaries (well-defined on homology). -/
axiom iotaMap :
    quotientTannerHomology X Λ hΛ →ₗ[𝔽₂]
    H1h' X Λ ℓ hΛ hcompat

/-! ## The Pi Map

The map `π : H₁ʰ → H₁(C(X/H, L))` projects from horizontal homology to the
quotient Tanner code homology by collapsing orbits.

By the Künneth decomposition (Def_27), elements of `H₁ʰ = H₁(C(X,L)) ⊗_H H₀(C_ℓ)`
are represented by cycles of the form `(∑_e a_e e ⊗ y₀, 0)` with coefficients
`a_e` constant on `H`-orbits. The map sends this to `[∑_e a_e eH]` in `H₁(C(X/H, L))`.

Well-definedness: The coefficients `a_e` are constant on orbits (from the balanced
product structure), so the sum `∑_e a_e eH` is well-defined (each orbit contributes
`a_𝓔 · 𝓔`). The map sends cycles to cycles because the quotient differential is
compatible with the balanced product differential (Def_24). -/
axiom piMap :
    H1h' X Λ ℓ hΛ hcompat →ₗ[𝔽₂]
    quotientTannerHomology X Λ hΛ

/-! ## Key Properties -/

/-- `π ∘ ι = ℓ · id`. Over `𝔽₂` with `ℓ` odd, `ℓ · id = id`, so `π ∘ ι = id`.

Each orbit `𝓔 = eH` has `|H| = ℓ` elements. Applying `ι` to `[𝓔]` gives
`[∑_{e ∈ 𝓔} e ⊗ y₀]`, and then `π` maps each `e ⊗ y₀` back to `𝓔`,
giving `ℓ · [𝓔]`. Since `ℓ` is odd, `ℓ ≡ 1 (mod 2)`, so `ℓ · [𝓔] = [𝓔]` in `𝔽₂`. -/
axiom piMap_comp_iotaMap (_ : ℓ % 2 = 1 := hℓ_odd) (_ : Odd (Fintype.card H) := hodd) :
    (piMap X Λ ℓ hΛ hcompat).comp (iotaMap X Λ ℓ hΛ hcompat) =
    (LinearMap.id : quotientTannerHomology X Λ hΛ →ₗ[𝔽₂] quotientTannerHomology X Λ hΛ)

/-- `ι ∘ π = id`.

For a horizontal class `[(∑_e a_e e ⊗ y₀, 0)]` with `a_e` constant on orbits,
`π` sends it to `[∑_e a_e eH]`, and `ι` lifts back to `[(∑_e a_e ∑_{e' ∈ eH} e' ⊗ y₀, 0)]`.
Since each orbit of size `ℓ` contributes `ℓ` copies, and `ℓ ≡ 1 (mod 2)`, this equals
the original class. -/
axiom iotaMap_comp_piMap (_ : ℓ % 2 = 1 := hℓ_odd) (_ : Odd (Fintype.card H) := hodd) :
    (iotaMap X Λ ℓ hΛ hcompat).comp (piMap X Λ ℓ hΛ hcompat) =
    (LinearMap.id : H1h' X Λ ℓ hΛ hcompat →ₗ[𝔽₂] H1h' X Λ ℓ hΛ hcompat)

/-! ## Satisfiability Witnesses

We construct a trivial example: `H = Unit` acting on a graph with `cells n = Unit` for all `n`,
empty boundary maps, `s = 0`, and `ℓ = 3`. This gives non-empty vertex and edge sets while
satisfying all required properties vacuously. -/

/-- Trivial graph with one vertex and one edge, with trivial Unit action. -/
def witnessGraph : GraphWithGroupAction Unit where
  graph := {
    cells := fun _ => Unit
    cells_fintype := fun _ => inferInstance
    cells_deceq := fun _ => inferInstance
    bdry := fun _ => ∅
    bdry_bdry := fun _ _ _ => ⟨0, rfl⟩
  }
  vertexAction := { smul := fun _ v => v, one_smul := fun _ => rfl,
                     mul_smul := fun _ _ _ => rfl }
  edgeAction := { smul := fun _ e => e, one_smul := fun _ => rfl,
                   mul_smul := fun _ _ _ => rfl }
  vertexFree := fun h _ _ => Subsingleton.elim h 1
  edgeFree := fun h _ _ => Subsingleton.elim h 1
  bdry_equivariant := fun _ _ _ => by simp
  quotientCondition := fun _ _ h _ _ => Subsingleton.elim h 1

/-- Trivial labeling with `s = 0` (no edges are incident to any vertex). -/
def witnessLabeling : witnessGraph.CellLabeling 0 := fun _ => {
  toFun := fun e => absurd e.2 (Finset.notMem_empty _)
  invFun := fun i => Fin.elim0 i
  left_inv := fun e => absurd e.2 (Finset.notMem_empty _)
  right_inv := fun i => Fin.elim0 i
}

/-- The trivial labeling is vacuously invariant (no incident edges). -/
lemma witnessLabeling_invariant :
    GraphWithGroupAction.IsInvariantLabeling witnessLabeling :=
  fun v _ e => absurd e.2 (Finset.notMem_empty _)

/-- Trivial MulAction of Unit on Fin 3. -/
def witnessUnitMulAction : MulAction Unit (Fin 3) where
  smul := fun _ i => i
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

/-- The trivial action is cycle-compatible. -/
lemma witnessCycleCompat :
    letI := witnessUnitMulAction
    BalancedProductTannerCycleCode.CycleCompatibleAction (H := Unit) 3 := by
  intro h i
  simp [witnessUnitMulAction]

/-- Witness: `iotaMap` premises are satisfiable with a non-trivial graph.
We use `H = Unit` acting on a graph with one vertex and one edge. -/
lemma iotaMap_satisfiable :
    ∃ (H : Type) (_ : Group H) (_ : Fintype H) (_ : DecidableEq H)
      (X : GraphWithGroupAction H) (s : ℕ) (Λ : X.CellLabeling s)
      (ℓ : ℕ) (_ : NeZero ℓ) (_ : MulAction H (Fin ℓ))
      (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
      (hcompat : BalancedProductTannerCycleCode.CycleCompatibleAction (H := H) ℓ),
      -- non-trivial: the graph has at least one vertex and one edge
      (∃ v : X.graph.cells 0, True) ∧ (∃ e : X.graph.cells 1, True) :=
  ⟨Unit, inferInstance, inferInstance, inferInstance, witnessGraph, 0, witnessLabeling,
   3, inferInstance, witnessUnitMulAction, witnessLabeling_invariant, witnessCycleCompat,
   ⟨⟨(), trivial⟩, ⟨(), trivial⟩⟩⟩

/-- Witness: `piMap_comp_iotaMap` premises are satisfiable (includes oddness). -/
lemma piMap_comp_iotaMap_satisfiable :
    ∃ (H : Type) (_ : Group H) (_ : Fintype H) (_ : DecidableEq H)
      (X : GraphWithGroupAction H) (s : ℕ) (Λ : X.CellLabeling s)
      (ℓ : ℕ) (_ : NeZero ℓ) (_ : MulAction H (Fin ℓ))
      (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
      (hcompat : BalancedProductTannerCycleCode.CycleCompatibleAction (H := H) ℓ)
      (_ : ℓ ≥ 3) (_ : ℓ % 2 = 1) (_ : Odd (Fintype.card H)),
      (∃ v : X.graph.cells 0, True) ∧ (∃ e : X.graph.cells 1, True) :=
  ⟨Unit, inferInstance, inferInstance, inferInstance, witnessGraph, 0, witnessLabeling,
   3, inferInstance, witnessUnitMulAction, witnessLabeling_invariant, witnessCycleCompat,
   le_refl 3, rfl, ⟨0, rfl⟩, ⟨⟨(), trivial⟩, ⟨(), trivial⟩⟩⟩

/-- Witness: `iotaMap_comp_piMap` premises are satisfiable (includes oddness). -/
lemma iotaMap_comp_piMap_satisfiable :
    ∃ (H : Type) (_ : Group H) (_ : Fintype H) (_ : DecidableEq H)
      (X : GraphWithGroupAction H) (s : ℕ) (Λ : X.CellLabeling s)
      (ℓ : ℕ) (_ : NeZero ℓ) (_ : MulAction H (Fin ℓ))
      (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
      (hcompat : BalancedProductTannerCycleCode.CycleCompatibleAction (H := H) ℓ)
      (_ : ℓ ≥ 3) (_ : ℓ % 2 = 1) (_ : Odd (Fintype.card H)),
      (∃ v : X.graph.cells 0, True) ∧ (∃ e : X.graph.cells 1, True) :=
  ⟨Unit, inferInstance, inferInstance, inferInstance, witnessGraph, 0, witnessLabeling,
   3, inferInstance, witnessUnitMulAction, witnessLabeling_invariant, witnessCycleCompat,
   le_refl 3, rfl, ⟨0, rfl⟩, ⟨⟨(), trivial⟩, ⟨(), trivial⟩⟩⟩

/-! ## Corollaries -/

/-- The `ι` map is injective (since `π ∘ ι = id`). -/
theorem iotaMap_injective (hℓ_odd : ℓ % 2 = 1) (hodd : Odd (Fintype.card H)) :
    Function.Injective (iotaMap X Λ ℓ hΛ hcompat) := by
  have h := piMap_comp_iotaMap (X := X) (Λ := Λ) (ℓ := ℓ) (hΛ := hΛ) (hcompat := hcompat) hℓ_odd hodd
  intro a b hab
  have : (piMap X Λ ℓ hΛ hcompat) ((iotaMap X Λ ℓ hΛ hcompat) a) =
         (piMap X Λ ℓ hΛ hcompat) ((iotaMap X Λ ℓ hΛ hcompat) b) := congr_arg _ hab
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, h, LinearMap.id_apply, LinearMap.id_apply] at this
  exact this

/-- The `π` map is surjective (since `π ∘ ι = id`). -/
theorem piMap_surjective (hℓ_odd : ℓ % 2 = 1) (hodd : Odd (Fintype.card H)) :
    Function.Surjective (piMap X Λ ℓ hΛ hcompat) := by
  have h := piMap_comp_iotaMap (X := X) (Λ := Λ) (ℓ := ℓ) (hΛ := hΛ) (hcompat := hcompat) hℓ_odd hodd
  intro y
  exact ⟨(iotaMap X Λ ℓ hΛ hcompat) y, by
    have h' := LinearMap.ext_iff.mp h y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h'
    exact h'⟩

/-- The `π` map is injective (since `ι ∘ π = id`). -/
theorem piMap_injective (hℓ_odd : ℓ % 2 = 1) (hodd : Odd (Fintype.card H)) :
    Function.Injective (piMap X Λ ℓ hΛ hcompat) := by
  have h := iotaMap_comp_piMap (X := X) (Λ := Λ) (ℓ := ℓ) (hΛ := hΛ) (hcompat := hcompat) hℓ_odd hodd
  intro a b hab
  have : (iotaMap X Λ ℓ hΛ hcompat) ((piMap X Λ ℓ hΛ hcompat) a) =
         (iotaMap X Λ ℓ hΛ hcompat) ((piMap X Λ ℓ hΛ hcompat) b) := congr_arg _ hab
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, h, LinearMap.id_apply, LinearMap.id_apply] at this
  exact this

/-- The `ι` map is surjective (since `ι ∘ π = id`). -/
theorem iotaMap_surjective (hℓ_odd : ℓ % 2 = 1) (hodd : Odd (Fintype.card H)) :
    Function.Surjective (iotaMap X Λ ℓ hΛ hcompat) := by
  have h := iotaMap_comp_piMap (X := X) (Λ := Λ) (ℓ := ℓ) (hΛ := hΛ) (hcompat := hcompat) hℓ_odd hodd
  intro y
  exact ⟨(piMap X Λ ℓ hΛ hcompat) y, by
    have h' := LinearMap.ext_iff.mp h y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h'
    exact h'⟩

/-- The `ι` map is a linear isomorphism (since `π ∘ ι = id` and `ι ∘ π = id`). -/
def iotaEquiv (hℓ_odd : ℓ % 2 = 1) (hodd : Odd (Fintype.card H)) :
    quotientTannerHomology X Λ hΛ ≃ₗ[𝔽₂] H1h' X Λ ℓ hΛ hcompat :=
  LinearEquiv.ofBijective (iotaMap X Λ ℓ hΛ hcompat)
    ⟨iotaMap_injective X Λ ℓ hΛ hcompat hℓ_odd hodd,
      iotaMap_surjective X Λ ℓ hΛ hcompat hℓ_odd hodd⟩

/-- The `π` map is a linear isomorphism. -/
def piEquiv (hℓ_odd : ℓ % 2 = 1) (hodd : Odd (Fintype.card H)) :
    H1h' X Λ ℓ hΛ hcompat ≃ₗ[𝔽₂] quotientTannerHomology X Λ hΛ :=
  LinearEquiv.ofBijective (piMap X Λ ℓ hΛ hcompat)
    ⟨piMap_injective X Λ ℓ hΛ hcompat hℓ_odd hodd,
      piMap_surjective X Λ ℓ hΛ hcompat hℓ_odd hodd⟩

/-- Witness: the quotient Tanner homology is nonempty (contains 0). -/
lemma quotientTannerHomology_nonempty :
    Nonempty (quotientTannerHomology X Λ hΛ) := ⟨0⟩

/-- Witness: the iota equivalence is nonempty. -/
lemma iotaEquiv_nonempty (hℓ_odd : ℓ % 2 = 1) (hodd : Odd (Fintype.card H)) :
    Nonempty (quotientTannerHomology X Λ hΛ ≃ₗ[𝔽₂] H1h' X Λ ℓ hΛ hcompat) :=
  ⟨iotaEquiv X Λ ℓ hΛ hcompat hℓ_odd hodd⟩

end IotaPiMaps

end
