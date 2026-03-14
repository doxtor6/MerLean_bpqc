import MerLeanBpqc.Definitions.Def_15_TannerCodeLocalSystem
import MerLeanBpqc.Definitions.Def_24_QuotientGraphTrivialization

/-!
# Definition 25: Invariant Labeling

Let `X` be a finite `s`-regular graph with a free right `H`-action (Def_24), and let
`Λ = {Λ_v}_{v ∈ X₀}` be a labeling as in Def_15, assigning to each vertex `v` a
bijection from the edges incident to `v` to `[s] = Fin s`.

The labeling `Λ` is **H-invariant** if `Λ_{h • v}(h • e) = Λ_v(e)` for all
`v ∈ X₀`, `e ∈ δv`, and `h ∈ H`.

An `H`-invariant labeling descends to a well-defined labeling on the quotient graph
`X/H`: for each vertex orbit `[v]` and edge orbit `[e]` incident to `[v]`, define
`Λ̄_{[v]}([e]) = Λ_v(e)`.

## Main Definitions
- `CellLabeling`: a labeling in the cell complex setting (bijection from incident edges to `Fin s`)
- `IsInvariantLabeling`: the `H`-invariance condition on a labeling
- `quotientIncidentEdges`: the incident edges in the quotient graph
- `quotientLabeling`: the descended labeling on `X/H`

## Main Results
- `isInvariantLabeling_nonempty`: witness that the invariance premises are satisfiable
- `quotientLabeling_well_defined`: the quotient labeling is independent of representatives
-/

open MulAction

attribute [local instance] Classical.propDecidable

noncomputable section

universe u

namespace GraphWithGroupAction

variable {H : Type u} [Group H] [Fintype H] [DecidableEq H]
variable (X : GraphWithGroupAction H)

/-! ## Incident Edges in the Cell Complex -/

/-- The set of edges incident to vertex `v` in the cell complex: `δv = {e ∈ X₁ | v ∈ ∂e}`. -/
def cellIncidentEdges (v : X.graph.cells 0) : Finset (X.graph.cells 1) :=
  Finset.univ.filter (fun e => v ∈ X.graph.bdry e)

theorem mem_cellIncidentEdges (v : X.graph.cells 0) (e : X.graph.cells 1) :
    e ∈ X.cellIncidentEdges v ↔ v ∈ X.graph.bdry e := by
  simp [cellIncidentEdges]

/-- Witness: `cellIncidentEdges v` is non-empty whenever there is an edge incident to `v`. -/
lemma cellIncidentEdges_nonempty (v : X.graph.cells 0) (e : X.graph.cells 1)
    (he : v ∈ X.graph.bdry e) : (X.cellIncidentEdges v).Nonempty :=
  ⟨e, (mem_cellIncidentEdges X v e).mpr he⟩

/-! ## Cell Complex Labeling -/

/-- A labeling in the cell complex setting: for each vertex `v`, a bijection from the
edges incident to `v` to `Fin s`. This is the cell complex analogue of `Labeling` (Def_15). -/
def CellLabeling (s : ℕ) :=
  ∀ v : X.graph.cells 0, X.cellIncidentEdges v ≃ Fin s

variable {X} {s : ℕ} (Λ : X.CellLabeling s)

/-! ## H-Invariant Labeling -/

/-- The `H`-action preserves incidence: if `e` is incident to `v`, then `h • e` is
incident to `h • v`. -/
lemma smul_incident_of_incident (v : X.graph.cells 0) (e : X.graph.cells 1)
    (h : H) (he : e ∈ X.cellIncidentEdges v) :
    h • e ∈ X.cellIncidentEdges (h • v) := by
  rw [mem_cellIncidentEdges] at he ⊢
  exact X.bdry_orbit_compat e h v he

/-- Transport an element of `cellIncidentEdges v` to `cellIncidentEdges (h • v)` via the
`H`-action. -/
def smulIncidentEdge (v : X.graph.cells 0) (h : H)
    (e : X.cellIncidentEdges v) : X.cellIncidentEdges (h • v) :=
  ⟨h • e.val, X.smul_incident_of_incident v e.val h e.prop⟩

/-- The labeling `Λ` is **H-invariant** if `Λ_{h • v}(h • e) = Λ_v(e)` for all
`v ∈ X₀`, `e ∈ δv`, and `h ∈ H`. Using the left-action convention from Def_24
(where `h • v` models the right action `v · h⁻¹`). -/
def IsInvariantLabeling : Prop :=
  ∀ (v : X.graph.cells 0) (h : H) (e : X.cellIncidentEdges v),
    Λ (h • v) (X.smulIncidentEdge v h e) = Λ v e

/-! ## Witness: invariance premises are satisfiable -/

/-- Witness: the invariance condition is satisfiable for the trivial group `H = Unit`.
Any labeling on a graph with trivial group action is invariant. -/
lemma isInvariantLabeling_trivial_satisfiable :
    ∃ (H : Type) (_ : Group H) (_ : Fintype H) (_ : DecidableEq H)
      (X : GraphWithGroupAction H) (s : ℕ) (Λ : X.CellLabeling s),
      IsInvariantLabeling Λ := by
  refine ⟨Unit, inferInstance, inferInstance, inferInstance, ?_, 0, ?_, ?_⟩
  · exact {
      graph := {
        cells := fun _ => PEmpty
        cells_fintype := fun _ => inferInstance
        cells_deceq := fun _ => inferInstance
        bdry := fun _ => ∅
        bdry_bdry := fun _ _ _ => by simp
      }
      vertexAction := { smul := fun _ v => v, one_smul := fun v => rfl, mul_smul := fun _ _ v => rfl }
      edgeAction := { smul := fun _ e => e, one_smul := fun e => rfl, mul_smul := fun _ _ e => rfl }
      vertexFree := fun h v => PEmpty.elim v
      edgeFree := fun h e => PEmpty.elim e
      bdry_equivariant := fun e => PEmpty.elim e
      quotientCondition := fun e => PEmpty.elim e
    }
  · intro v; exact PEmpty.elim v
  · intro v; exact PEmpty.elim v

/-! ## Quotient Labeling -/

/-- The incident edges in the quotient graph: edge orbits `[e]` such that some
representative edge has a boundary vertex in the orbit of `v`. -/
def quotientIncidentEdges (V : X.quotientVertices) : Finset X.quotientEdges :=
  Finset.univ.filter (fun E =>
    ∃ e : X.graph.cells 1, X.edgeQuot e = E ∧
    ∃ v : X.graph.cells 0, X.vertexQuot v = V ∧ v ∈ X.graph.bdry e)

theorem mem_quotientIncidentEdges (V : X.quotientVertices) (E : X.quotientEdges) :
    E ∈ X.quotientIncidentEdges V ↔
    ∃ e : X.graph.cells 1, X.edgeQuot e = E ∧
    ∃ v : X.graph.cells 0, X.vertexQuot v = V ∧ v ∈ X.graph.bdry e := by
  simp [quotientIncidentEdges]

/-- Given a vertex `v` and an incident edge `e ∈ δv`, the quotient edge orbit `[e]` is
incident to the quotient vertex orbit `[v]`. -/
lemma quotientIncident_of_incident (v : X.graph.cells 0) (e : X.graph.cells 1)
    (he : e ∈ X.cellIncidentEdges v) :
    X.edgeQuot e ∈ X.quotientIncidentEdges (X.vertexQuot v) := by
  rw [mem_quotientIncidentEdges]
  exact ⟨e, rfl, v, rfl, (mem_cellIncidentEdges X v e).mp he⟩

/-- Witness: `quotientIncidentEdges V` is non-empty whenever there is an edge incident to
a vertex in the orbit `V`. -/
lemma quotientIncidentEdges_nonempty (v : X.graph.cells 0) (e : X.graph.cells 1)
    (he : v ∈ X.graph.bdry e) :
    (X.quotientIncidentEdges (X.vertexQuot v)).Nonempty :=
  ⟨X.edgeQuot e, X.quotientIncident_of_incident v e
    ((mem_cellIncidentEdges X v e).mpr he)⟩

/-- The quotient labeling on `X/H`, descended from an `H`-invariant labeling `Λ`.
For a vertex orbit `[v]` and an incident edge orbit `[e]`, we define
`Λ̄_{[v]}([e]) = Λ_v(e)` using any representatives `v ∈ [v]` and `e ∈ [e]`
with `e ∈ δv`. The `H`-invariance ensures this is well-defined. -/
def quotientLabeling (hΛ : IsInvariantLabeling Λ) :
    ∀ V : X.quotientVertices, X.quotientIncidentEdges V ≃ Fin s := by
  intro V
  -- We construct the bijection by choosing a representative vertex v in the orbit V
  -- and using the invariance to show the result is independent of the choice
  -- For now, pick a representative vertex
  have hV := Quotient.exists_rep V
  let v := hV.choose
  have hv : X.vertexQuot v = V := hV.choose_spec
  -- Build a map from quotient incident edges to incident edges of v
  -- Each quotient incident edge E has a representative e with some v' in the orbit of v
  -- in ∂e. By translating, we get an edge in the orbit of e incident to v.
  have translate : ∀ E : X.quotientIncidentEdges V,
      ∃ e : X.cellIncidentEdges v, X.edgeQuot e.val = E.val := by
    intro ⟨E, hE⟩
    rw [mem_quotientIncidentEdges] at hE
    obtain ⟨e, rfl, v', hv', hve⟩ := hE
    -- v' is in the same orbit as v
    have hπ : X.vertexQuot v' = X.vertexQuot v := by rw [hv, hv']
    have horb := Quotient.exact hπ
    obtain ⟨g, hg⟩ := horb
    -- g • v = v' (or g • v' = v, depending on convention)
    -- hg : g • v = v'  (orbitRel: ∃ g, g • v = v')
    -- We need an edge in the orbit of e incident to v
    -- g⁻¹ • v' = v, and g⁻¹ • e is incident to g⁻¹ • v' = v
    have hve' : v ∈ X.graph.bdry (g⁻¹ • e) := by
      rw [X.bdry_equivariant e g⁻¹ v]
      simp [hg, hve]
    exact ⟨⟨g⁻¹ • e, (mem_cellIncidentEdges X v _).mpr hve'⟩, by
      apply Quotient.sound; exact ⟨g⁻¹, rfl⟩⟩
  -- For each quotient edge, pick the translated edge
  let pickEdge : X.quotientIncidentEdges V → X.cellIncidentEdges v :=
    fun E => (translate E).choose
  have pickEdge_spec : ∀ E, X.edgeQuot (pickEdge E).val = E.val :=
    fun E => (translate E).choose_spec
  -- Show pickEdge is injective
  have pickEdge_inj : Function.Injective pickEdge := by
    intro E₁ E₂ h
    ext
    rw [← pickEdge_spec E₁, ← pickEdge_spec E₂]
    congr 1
    exact congrArg (fun x => x.val) h
  -- Show that the composition Λ v ∘ pickEdge gives a well-defined map
  -- that is independent of the choice of representative (by H-invariance)
  -- Build the equiv: quotientIncidentEdges V ≃ Fin s
  -- via quotientIncidentEdges V ↪ cellIncidentEdges v ≃ Fin s
  -- We need surjectivity too: every edge incident to v gives a quotient edge
  have pickEdge_surj : Function.Surjective pickEdge := by
    intro ⟨e, he⟩
    have hE : X.edgeQuot e ∈ X.quotientIncidentEdges V := by
      rw [← hv]; exact X.quotientIncident_of_incident v e he
    refine ⟨⟨X.edgeQuot e, hE⟩, ?_⟩
    -- pickEdge ⟨edgeQuot e, hE⟩ is some edge e' with edgeQuot e' = edgeQuot e
    -- and e' ∈ cellIncidentEdges v
    -- Both e and e' are in the orbit of the same edge and incident to v
    -- By freeness, they must be equal
    have hpe := pickEdge_spec ⟨X.edgeQuot e, hE⟩
    -- hpe : edgeQuot (pickEdge ...).val = edgeQuot e
    -- So pickEdge and e are in the same orbit
    have horb := Quotient.exact hpe
    obtain ⟨g, hg⟩ := horb
    -- hg : g • e = pickEdge.val (or g • pickEdge.val = e)
    -- Both are incident to v, so g fixes v by quotient condition? No...
    -- Actually, v ∈ bdry e and v ∈ bdry (pickEdge.val)
    -- g • (pickEdge.val) = e, so v ∈ bdry (g • pickEdge.val)
    -- Also g • v ∈ bdry (g • pickEdge.val) = bdry e
    -- Wait, let me reconsider. orbitRel gives g • e = pickEdge.val or similar
    -- Let's work with what we have
    ext
    -- We need to show pickEdge ⟨edgeQuot e, hE⟩ = ⟨e, he⟩
    -- i.e., (pickEdge ..).val = e
    let e' := (pickEdge ⟨X.edgeQuot e, hE⟩).val
    -- e' is in cellIncidentEdges v, so v ∈ bdry e'
    have he' := (pickEdge ⟨X.edgeQuot e, hE⟩).prop
    rw [mem_cellIncidentEdges] at he he'
    -- hg : g • e = e' (from orbitRel)
    -- v ∈ bdry e and v ∈ bdry e' = bdry (g • e)
    -- So v ∈ bdry (g • e), which means g⁻¹ • v ∈ bdry e
    -- Also v ∈ bdry e
    -- By quotient condition: if v and g⁻¹ • v are both in bdry e, then g⁻¹ = 1
    have hfree : g = 1 := by
      have h1 : v ∈ X.graph.bdry e := he
      have h2 : g⁻¹ • v ∈ X.graph.bdry e := by
        have hge : g • e = e' := hg
        exact (X.bdry_equivariant e g v).mp (hge ▸ he')
      have := X.quotientCondition e v g⁻¹ h1 h2
      exact inv_eq_one.mp this
    simp [hfree] at hg
    exact hg.symm
  exact Equiv.ofBijective (Λ v ∘ pickEdge) ⟨by
    exact Function.Injective.comp (Λ v).injective pickEdge_inj,
    by exact Function.Surjective.comp (Λ v).surjective pickEdge_surj⟩

/-- The quotient labeling is well-defined: using different representatives
yields the same result. This follows from `H`-invariance. -/
theorem quotientLabeling_well_defined (hΛ : IsInvariantLabeling Λ)
    (v : X.graph.cells 0) (e : X.graph.cells 1) (he : v ∈ X.graph.bdry e)
    (h : H) (he' : h • v ∈ X.graph.bdry (h • e)) :
    Λ (h • v) ⟨h • e, (mem_cellIncidentEdges X (h • v) (h • e)).mpr he'⟩ =
    Λ v ⟨e, (mem_cellIncidentEdges X v e).mpr he⟩ := by
  have inv := hΛ v h ⟨e, (mem_cellIncidentEdges X v e).mpr he⟩
  -- inv : Λ (h • v) (smulIncidentEdge v h ⟨e, _⟩) = Λ v ⟨e, _⟩
  -- smulIncidentEdge v h ⟨e, _⟩ = ⟨h • e, _⟩
  have : (X.smulIncidentEdge v h ⟨e, (mem_cellIncidentEdges X v e).mpr he⟩ : X.graph.cells 1) =
      h • e := rfl
  rw [← inv]
  congr 1

end GraphWithGroupAction

end
