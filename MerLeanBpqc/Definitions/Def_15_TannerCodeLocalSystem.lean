import MerLeanBpqc.Definitions.Def_3_ClassicalCode
import MerLeanBpqc.Definitions.Def_7_CellComplex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Definition 15: Tanner Code (Local System)

Let `X` be a finite `s`-regular graph, viewed as a 1-dimensional cell complex (Def_7)
with vertex set `X₀` and edge set `X₁`, and let `L` be an `[s, k_L, d_L]`-code (Def_3),
called the local code.

A labeling is a collection `Λ = {Λ_v}_{v ∈ X₀}` of bijections
`Λ_v : inc(v) → Fin s` where `inc(v) ⊂ X₁` is the set of edges incident to `v`.

The Tanner code `C(X, L, Λ)` is defined as `ker ∂ ⊂ C₁(X)`, where the differential
`∂ : C₁(X) → C₀(X) ⊗ L₀` sends each edge `e` to
`v ⊗ ∂^L(Λ_v(e)) + w ⊗ ∂^L(Λ_w(e))`.

## Main Definitions
- `Labeling` — bijections from neighbor sets to `Fin s`
- `localView` — restriction of a 1-chain to the star of a vertex
- `differential` — the differential `∂ : C₁(X) → (V → L₀)`
- `tannerCode` — the Tanner code `ker ∂`
- `mem_tannerCode_iff` — codeword characterization
- `mem_tannerCode_iff_localCode` — characterization in terms of `ClassicalCode`
- `tannerCode_eq_iInf` — intersection characterization
-/

open CategoryTheory

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] [G.LocallyFinite]
  {s : ℕ}

/-! ## Labeling -/

/-- A labeling for the Tanner code on an `s`-regular graph `G`: for each vertex `v`,
a bijection `Λ_v : N(v) ≃ Fin s` from the neighbor set of `v` to `Fin s`.
The neighbor `(Λ_v)⁻¹(i)` corresponds to the `i`-th position in the local code.
The existence of such a labeling requires `|N(v)| = s` for all `v`,
which holds when `G` is `s`-regular (`G.IsRegularOfDegree s`). -/
def Labeling :=
  ∀ v : V, G.neighborSet v ≃ Fin s

variable {G} (Λ : Labeling G (s := s))

/-! ## Local View -/

/-- The local view at vertex `v`: given a 1-chain `c ∈ C₁(X) = (G.edgeSet → 𝔽₂)`,
produce a vector in `Fin s → 𝔽₂` by reading off the coefficients of edges incident
to `v`, reindexed by the labeling `Λ_v`. Specifically,
`(localView Λ v c)(i) = c({v, w})` where `w = (Λ_v)⁻¹(i)` is the neighbor of `v`
labeled `i`. This gives the "restriction of `c` to the star of `v`" viewed as an
element of `𝔽₂^s` via the labeling. -/
noncomputable def localView (v : V) : (G.edgeSet → 𝔽₂) →ₗ[𝔽₂] (Fin s → 𝔽₂) where
  toFun c i :=
    let w : G.neighborSet v := (Λ v).symm i
    c ⟨s(v, w.val), G.mem_edgeSet.mpr w.prop⟩
  map_add' c₁ c₂ := by ext i; simp [Pi.add_apply]
  map_smul' r c := by ext i; simp [Pi.smul_apply, smul_eq_mul]

/-- The local view at vertex `v` evaluated at index `i` gives the coefficient
of the edge between `v` and the neighbor `(Λ_v)⁻¹(i)`. -/
lemma localView_apply (v : V) (c : G.edgeSet → 𝔽₂) (i : Fin s) :
    localView Λ v c i =
      c ⟨s(v, ((Λ v).symm i).val), G.mem_edgeSet.mpr ((Λ v).symm i).prop⟩ :=
  rfl

/-! ## Differential -/

/-- The differential `∂ : C₁(X) → (V → L₀)`, defined by `∂(c)(v) = parityCheck(localView_v(c))`.
This is the component form of the paper's `∂ : C₁(X) → C₀(X) ⊗ L₀`,
using the canonical isomorphism `(V → 𝔽₂) ⊗ (Fin m → 𝔽₂) ≃ V → Fin m → 𝔽₂` for finite types.

For an edge `e = {v, w}`, the paper's formula
`∂(e) = e_v ⊗ ∂^L(e_{Λ_v(w)}) + e_w ⊗ ∂^L(e_{Λ_w(v)})`
becomes: `∂(e)(v) = ∂^L(e_{Λ_v(w)})` and `∂(e)(w) = ∂^L(e_{Λ_w(v)})`. -/
noncomputable def differential {m : ℕ}
    (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) :
    (G.edgeSet → 𝔽₂) →ₗ[𝔽₂] (V → Fin m → 𝔽₂) where
  toFun c v := parityCheck (localView Λ v c)
  map_add' c₁ c₂ := by
    ext v j
    simp [map_add]
  map_smul' r c := by
    ext v j
    simp [map_smul]

/-- The differential at vertex `v` equals the parity check applied to the local view. -/
lemma differential_apply {m : ℕ}
    (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (c : G.edgeSet → 𝔽₂) (v : V) :
    differential Λ parityCheck c v = parityCheck (localView Λ v c) :=
  rfl

/-! ## Tanner Code -/

/-- The Tanner code `C(X, L, Λ) = ker ∂ ⊂ C₁(X)`, where `∂` is the differential and
`C₁(X) = G.edgeSet → 𝔽₂` is the chain space of 1-chains. A 1-chain `c = Σ_e a_e · e`
is a codeword iff for every vertex `v`, the restriction of the `a_e` to edges incident
to `v` (read via `Λ_v`) is a codeword of the local code `L = ker(parityCheck)`. -/
noncomputable def tannerCode {m : ℕ}
    (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) :
    Submodule 𝔽₂ (G.edgeSet → 𝔽₂) :=
  LinearMap.ker (differential Λ parityCheck)

/-- A chain `c` is in the Tanner code iff for every vertex `v`,
the local view `localView Λ v c` is in `ker(parityCheck)`. Equivalently,
the restriction of `c` to edges incident to `v`, read via the labeling `Λ_v`,
is a codeword of `L`. -/
theorem mem_tannerCode_iff {m : ℕ}
    (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (c : G.edgeSet → 𝔽₂) :
    c ∈ tannerCode Λ parityCheck ↔
      ∀ v : V, localView Λ v c ∈ LinearMap.ker parityCheck := by
  simp only [tannerCode, LinearMap.mem_ker, differential]
  constructor
  · intro h v
    exact congr_fun h v
  · intro h
    funext v
    exact h v

/-- The codeword characterization in terms of `ClassicalCode` (Def_3):
`c ∈ C(X, L, Λ)` iff for every vertex `v`, the local view at `v` is in the local
code `L = ofParityCheck(parityCheck)`. -/
theorem mem_tannerCode_iff_localCode {m : ℕ}
    (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂))
    (c : G.edgeSet → 𝔽₂) :
    c ∈ tannerCode Λ parityCheck ↔
      ∀ v : V, localView Λ v c ∈ (ClassicalCode.ofParityCheck parityCheck).code := by
  rw [mem_tannerCode_iff]
  simp only [ClassicalCode.ofParityCheck, ClassicalCode.code_eq_ker]

/-- The Tanner code equals the intersection of pullbacks of the local code along
all local views: `C(X, L, Λ) = ⋂_v (localView_v)⁻¹(L)`. -/
theorem tannerCode_eq_iInf {m : ℕ}
    (parityCheck : (Fin s → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) :
    tannerCode Λ parityCheck =
      ⨅ v : V, (LinearMap.ker parityCheck).comap (localView Λ v) := by
  ext c
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker]
  constructor
  · intro hc v
    rw [mem_tannerCode_iff] at hc
    exact (LinearMap.mem_ker.mp (hc v))
  · intro hc
    rw [mem_tannerCode_iff]
    intro v
    exact LinearMap.mem_ker.mpr (hc v)
