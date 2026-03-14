import MerLeanBpqc.Definitions.Def_7_CellComplex

/-!
# Definition 19: Edge Boundary and Vertex Incidence for Cell Complexes

For a cell complex `X` (Def_7), we define:
- `edgeBoundaryCell X S` — the edge boundary `δS = {e ∈ X₁ | ∃ u ∈ ∂₁e, u ∈ S, ∃ w ∈ ∂₁e, w ∉ S}`
- `incidentVerticesCell X E` — vertices incident to edges `E`: `Γ(E) = {v ∈ X₀ | ∃ e ∈ E, v ∈ ∂₁ e}`
- `incidentEdges X v` — edges incident to vertex `v`: `δv = {e ∈ X₁ | v ∈ ∂₁ e}`
- `edgeBoundaryVertex X S v` — edges in the edge boundary incident to `v`: `(δS)_v = δS ∩ δv`

## Main Results
- `mem_edgeBoundaryCell` — membership characterization for `δS`
- `mem_incidentVerticesCell` — membership characterization for `Γ(E)`
- `mem_incidentEdges` — membership characterization for `δv`
- `mem_edgeBoundaryVertex` — membership characterization for `(δS)_v`
- `edgeBoundaryVertex_subset` — `(δS)_v ⊆ δS`
- `edgeBoundaryVertex_subset_incidentEdges` — `(δS)_v ⊆ δv`
- `mem_edgeBoundaryVertex_iff` — alternate characterization
-/

open Finset

namespace CellComplex

variable (X : CellComplex)

/-! ## Edge Boundary -/

/-- The edge boundary `δS = {e ∈ X₁ | ∃ u ∈ ∂₁e, u ∈ S, ∃ w ∈ ∂₁e, w ∉ S}` of a vertex
subset `S ⊆ X₀`. An edge `e` is in `δS` iff its boundary contains a vertex in `S` and
a vertex outside `S`. -/
def edgeBoundaryCell (S : Finset (X.cells 0)) : Finset (X.cells 1) :=
  Finset.univ.filter fun e =>
    (∃ u ∈ X.bdry e, u ∈ S) ∧ (∃ w ∈ X.bdry e, w ∉ S)

/-- Membership in the edge boundary: `e ∈ δS` iff `∂₁ e` meets both `S` and `Sᶜ`. -/
theorem mem_edgeBoundaryCell (S : Finset (X.cells 0)) (e : X.cells 1) :
    e ∈ edgeBoundaryCell X S ↔ (∃ u ∈ X.bdry e, u ∈ S) ∧ (∃ w ∈ X.bdry e, w ∉ S) := by
  simp [edgeBoundaryCell]

/-- Witness: the edge boundary is nonempty when there exists an edge with one endpoint
in `S` and one outside `S`. -/
lemma edgeBoundaryCell_nonempty (S : Finset (X.cells 0))
    (h : ∃ e : X.cells 1, (∃ u ∈ X.bdry e, u ∈ S) ∧ (∃ w ∈ X.bdry e, w ∉ S)) :
    (edgeBoundaryCell X S).Nonempty := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, (mem_edgeBoundaryCell X S e).mpr he⟩

/-! ## Incident Vertices -/

/-- The set of vertices incident to a set of edges `E ⊆ X₁`:
`Γ(E) = {v ∈ X₀ | ∃ e ∈ E, v ∈ ∂₁ e}`. -/
def incidentVerticesCell (E : Finset (X.cells 1)) : Finset (X.cells 0) :=
  Finset.univ.filter fun v => ∃ e ∈ E, v ∈ X.bdry e

/-- Membership in incident vertices: `v ∈ Γ(E)` iff there exists an edge `e ∈ E`
with `v ∈ ∂₁ e`. -/
theorem mem_incidentVerticesCell (E : Finset (X.cells 1)) (v : X.cells 0) :
    v ∈ incidentVerticesCell X E ↔ ∃ e ∈ E, v ∈ X.bdry e := by
  simp [incidentVerticesCell]

/-- Witness: `incidentVerticesCell` is nonempty when `E` contains an edge with a
nonempty boundary. -/
lemma incidentVerticesCell_nonempty (E : Finset (X.cells 1))
    (h : ∃ e ∈ E, ∃ v : X.cells 0, v ∈ X.bdry e) :
    (incidentVerticesCell X E).Nonempty := by
  obtain ⟨e, he, v, hv⟩ := h
  exact ⟨v, (mem_incidentVerticesCell X E v).mpr ⟨e, he, hv⟩⟩

/-! ## Incident Edges (Star of a vertex) -/

/-- The set of edges incident to a vertex `v`: `δv = {e ∈ X₁ | v ∈ ∂₁ e}`,
i.e., the star of `v`. -/
def incidentEdges (v : X.cells 0) : Finset (X.cells 1) :=
  Finset.univ.filter fun e => v ∈ X.bdry e

/-- Membership in incident edges: `e ∈ δv` iff `v ∈ ∂₁ e`. -/
theorem mem_incidentEdges (v : X.cells 0) (e : X.cells 1) :
    e ∈ incidentEdges X v ↔ v ∈ X.bdry e := by
  simp [incidentEdges]

/-- Witness: `incidentEdges` is nonempty when there exists an edge whose boundary
contains `v`. -/
lemma incidentEdges_nonempty (v : X.cells 0)
    (h : ∃ e : X.cells 1, v ∈ X.bdry e) :
    (incidentEdges X v).Nonempty := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, (mem_incidentEdges X v e).mpr he⟩

/-! ## Edge Boundary Vertex -/

/-- The edges in the edge boundary `δS` that are incident to vertex `v`:
`(δS)_v = δS ∩ δv = {e ∈ X₁ | e ∈ δS ∧ v ∈ ∂₁ e}`. -/
def edgeBoundaryVertex (S : Finset (X.cells 0)) (v : X.cells 0) : Finset (X.cells 1) :=
  (edgeBoundaryCell X S).filter fun e => v ∈ X.bdry e

/-- Membership in the edge boundary at vertex `v`: `e ∈ (δS)_v` iff
`e ∈ δS` and `v ∈ ∂₁ e`. -/
theorem mem_edgeBoundaryVertex (S : Finset (X.cells 0)) (v : X.cells 0) (e : X.cells 1) :
    e ∈ edgeBoundaryVertex X S v ↔ e ∈ edgeBoundaryCell X S ∧ v ∈ X.bdry e := by
  simp [edgeBoundaryVertex]

/-- `edgeBoundaryVertex` is a subset of the edge boundary. -/
theorem edgeBoundaryVertex_subset (S : Finset (X.cells 0)) (v : X.cells 0) :
    edgeBoundaryVertex X S v ⊆ edgeBoundaryCell X S :=
  Finset.filter_subset _ _

/-- `edgeBoundaryVertex` is a subset of the incident edges. -/
theorem edgeBoundaryVertex_subset_incidentEdges (S : Finset (X.cells 0)) (v : X.cells 0) :
    edgeBoundaryVertex X S v ⊆ incidentEdges X v := by
  intro e he
  rw [mem_edgeBoundaryVertex] at he
  rw [mem_incidentEdges]
  exact he.2

/-- Witness: `edgeBoundaryVertex` is nonempty when there exists an edge in `δS`
incident to `v`. -/
lemma edgeBoundaryVertex_nonempty (S : Finset (X.cells 0)) (v : X.cells 0)
    (h : ∃ e : X.cells 1, e ∈ edgeBoundaryCell X S ∧ v ∈ X.bdry e) :
    (edgeBoundaryVertex X S v).Nonempty := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, (mem_edgeBoundaryVertex X S v e).mpr he⟩

/-- Alternate characterization: `e ∈ (δS)_v` iff `v ∈ ∂₁ e`, `∂₁ e` meets `S`,
and `∂₁ e` meets `Sᶜ`. -/
theorem mem_edgeBoundaryVertex_iff (S : Finset (X.cells 0)) (v : X.cells 0) (e : X.cells 1) :
    e ∈ edgeBoundaryVertex X S v ↔
      v ∈ X.bdry e ∧ (∃ u ∈ X.bdry e, u ∈ S) ∧ (∃ w ∈ X.bdry e, w ∉ S) := by
  rw [mem_edgeBoundaryVertex, mem_edgeBoundaryCell]
  tauto

end CellComplex
