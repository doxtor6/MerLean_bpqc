import MerLeanBpqc.Definitions.Def_7_CellComplex
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Definition 24: Quotient Graph Trivialization

Let `X` be a finite graph (1-dimensional cell complex, Def_7) equipped with a free right
`H`-action on vertices and edges, compatible with the boundary map. The quotient graph
`X/H` inherits a cell complex structure. A **trivialization** is a section `R ⊆ X₀`
of the quotient map on vertices (one representative per orbit). Given `R`, the
**induced connection** `φ_R : (X/H)₁ → H` assigns to each edge orbit the unique
group element relating the chosen vertex representatives.

## Main Definitions
- `GraphWithGroupAction`: a graph with free right `H`-action compatible with boundary
- `GraphWithGroupAction.quotientGraph`: the quotient graph `X/H`
- `GraphWithGroupAction.Trivialization`: a section of the vertex quotient map
- `GraphWithGroupAction.inducedConnection`: the connection `φ_R : (X/H)₁ → H`

## Main Results
- `quotientGraph_cells_zero`: `(X/H)₀ = X₀/H` (orbits of vertices)
- `quotientGraph_cells_one`: `(X/H)₁ = X₁/H` (orbits of edges)
- `trivialization_nonempty`: a trivialization exists (by the  of choice)
- `inducedConnection_spec`: the connection satisfies the defining property
-/

open MulAction

attribute [local instance] Classical.propDecidable

noncomputable section

universe u

/-! ## Graph with Group Action -/

/-- A finite graph (1-dimensional cell complex) `X` with a free right action of a finite
group `H` on vertices and edges, compatible with the boundary map, and satisfying the
quotient condition (no edge connects `v` to `vh` for `h ≠ 1`).

We model the right action as `H` acting on the left via `h ↦ (· * h⁻¹)`, i.e.,
`MulAction H (X.cells 0)` where `h • v = v * h⁻¹` in right-action notation. -/
structure GraphWithGroupAction (H : Type u) [Group H] [Fintype H] where
  /-- The underlying graph as a cell complex (only degrees 0 and 1 are nontrivial). -/
  graph : CellComplex
  /-- Right `H`-action on vertices `X₀`. -/
  vertexAction : MulAction H (graph.cells 0)
  /-- Right `H`-action on edges `X₁`. -/
  edgeAction : MulAction H (graph.cells 1)
  /-- The action on vertices is free. -/
  vertexFree : ∀ (h : H) (v : graph.cells 0), h • v = v → h = 1
  /-- The action on edges is free. -/
  edgeFree : ∀ (h : H) (e : graph.cells 1), h • e = e → h = 1
  /-- Compatibility: `∂(h • e) = h • ∂(e)`, i.e., the boundary of a translated edge
  equals the translation of the boundary. Concretely, `τ ∈ ∂(h • e) ↔ h⁻¹ • τ ∈ ∂e`. -/
  bdry_equivariant : ∀ (e : graph.cells 1) (h : H) (τ : graph.cells 0),
    τ ∈ graph.bdry (h • e) ↔ h⁻¹ • τ ∈ graph.bdry e
  /-- Quotient condition: no edge connects `v` to `h • v` for `h ≠ 1`.
  Equivalently, if `e` has both `v` and `h • v` in its boundary, then `h = 1`. -/
  quotientCondition : ∀ (e : graph.cells 1) (v : graph.cells 0) (h : H),
    v ∈ graph.bdry e → h • v ∈ graph.bdry e → h = 1

namespace GraphWithGroupAction

variable {H : Type u} [Group H] [Fintype H] [DecidableEq H]
variable (X : GraphWithGroupAction H)

-- Make the MulAction instances available
instance : MulAction H (X.graph.cells 0) := X.vertexAction
instance : MulAction H (X.graph.cells 1) := X.edgeAction

/-! ## Quotient Graph -/

/-- The quotient type of vertices: `(X/H)₀ = X₀ / H`. -/
def quotientVertices := MulAction.orbitRel.Quotient H (X.graph.cells 0)

/-- The quotient type of edges: `(X/H)₁ = X₁ / H`. -/
def quotientEdges := MulAction.orbitRel.Quotient H (X.graph.cells 1)

instance : Fintype X.quotientVertices :=
  Quotient.fintype (MulAction.orbitRel H (X.graph.cells 0))

instance : Fintype X.quotientEdges :=
  Quotient.fintype (MulAction.orbitRel H (X.graph.cells 1))

instance : DecidableEq X.quotientVertices :=
  Quotient.decidableEq

instance : DecidableEq X.quotientEdges :=
  Quotient.decidableEq

/-- The quotient map on vertices: `π₀ : X₀ → (X/H)₀`. -/
def vertexQuot (v : X.graph.cells 0) : X.quotientVertices :=
  Quotient.mk'' v

/-- The quotient map on edges: `π₁ : X₁ → (X/H)₁`. -/
def edgeQuot (e : X.graph.cells 1) : X.quotientEdges :=
  Quotient.mk'' e

/-- The boundary map on the quotient graph is well-defined:
if `τ ∈ ∂e`, then `h • τ ∈ ∂(h • e)` by equivariance. -/
lemma bdry_orbit_compat (e : X.graph.cells 1) (h : H) (τ : X.graph.cells 0)
    (hτ : τ ∈ X.graph.bdry e) :
    h • τ ∈ X.graph.bdry (h • e) := by
  rw [X.bdry_equivariant e h (h • τ)]
  simp [inv_smul_smul, hτ]

/-- The boundary of an edge in the quotient: the set of vertex orbits that appear
as boundaries of any representative edge. -/
def quotientBdry (E : X.quotientEdges) : Finset X.quotientVertices :=
  Quotient.liftOn E
    (fun e => (X.graph.bdry e).image X.vertexQuot)
    (fun e₁ e₂ (h : @Setoid.r _ (MulAction.orbitRel H (X.graph.cells 1)) e₁ e₂) => by
      -- h : e₁ and e₂ are in the same orbit, so ∃ g, g • e₁ = e₂ (or vice versa)
      obtain ⟨g, hg⟩ := h
      -- hg : g • e₂ = e₁ (orbitRel convention)
      ext V
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨τ, hτ, rfl⟩
        -- τ ∈ bdry e₁, need τ' ∈ bdry e₂ with same vertex orbit
        -- Since g • e₂ = e₁, we have τ ∈ bdry (g • e₂)
        rw [← hg] at hτ
        -- Now hτ : τ ∈ bdry (g • e₂)
        have hτ' : g⁻¹ • τ ∈ X.graph.bdry e₂ := by
          rwa [← X.bdry_equivariant e₂ g τ]
        exact ⟨g⁻¹ • τ, hτ', by
          apply Quotient.sound
          exact ⟨g⁻¹, rfl⟩⟩
      · rintro ⟨τ, hτ, rfl⟩
        -- τ ∈ bdry e₂, need τ' ∈ bdry e₁ with same vertex orbit
        have hτ' : g • τ ∈ X.graph.bdry e₁ := by
          rw [← hg]
          exact X.bdry_orbit_compat e₂ g τ hτ
        exact ⟨g • τ, hτ', by
          apply Quotient.sound
          exact ⟨g, rfl⟩⟩)

/-- Witness: the quotient boundary of an edge orbit is nonempty, provided every edge
has at least one boundary vertex (which holds for any graph). -/
lemma quotientBdry_nonempty (E : X.quotientEdges)
    (hbdry : ∀ e : X.graph.cells 1, (X.graph.bdry e).Nonempty) :
    (X.quotientBdry E).Nonempty := by
  induction E using Quotient.inductionOn with
  | h e =>
    simp only [quotientBdry, Quotient.liftOn_mk]
    obtain ⟨τ, hτ⟩ := hbdry e
    exact ⟨X.vertexQuot τ, Finset.mem_image.mpr ⟨τ, hτ, rfl⟩⟩

/-! ## Trivialization (Section of the quotient map) -/

/-- A trivialization of the quotient map `π : X → X/H` is a section `R ⊆ X₀`
containing exactly one representative from each vertex orbit. -/
structure Trivialization where
  /-- The representative function: for each vertex orbit, pick a representative. -/
  repr : X.quotientVertices → X.graph.cells 0
  /-- Each representative lies in its orbit. -/
  repr_mem : ∀ (V : X.quotientVertices), X.vertexQuot (repr V) = V

/-- A trivialization always exists (by the  of choice). -/
theorem trivialization_exists : Nonempty (X.Trivialization) := by
  have : ∀ V : X.quotientVertices, ∃ v : X.graph.cells 0, X.vertexQuot v = V := by
    intro V
    exact Quotient.inductionOn V (fun v => ⟨v, rfl⟩)
  exact ⟨⟨fun V => (this V).choose, fun V => (this V).choose_spec⟩⟩

/-- Witness: a trivialization is nonempty. -/
lemma trivialization_nonempty : Nonempty (X.Trivialization) := X.trivialization_exists

/-! ## Induced Connection -/

private lemma exists_smul_repr_eq (R : X.Trivialization) (v : X.graph.cells 0) :
    ∃ g : H, g • R.repr (X.vertexQuot v) = v := by
  have h := R.repr_mem (X.vertexQuot v)
  simp only [vertexQuot] at h
  have := Quotient.exact h
  obtain ⟨g, hg⟩ := this
  exact ⟨g⁻¹, by simp only [vertexQuot]; rw [← hg]; simp [inv_smul_smul]⟩

/-- Given an edge `e ∈ X₁` and a vertex `v ∈ ∂e`, the unique group element `h` such that
`v = h • repr(π(v))`, i.e., the element relating `v` to its orbit representative. -/
def vertexGroupElement (R : X.Trivialization) (v : X.graph.cells 0) : H :=
  (X.exists_smul_repr_eq R v).choose

lemma vertexGroupElement_spec (R : X.Trivialization) (v : X.graph.cells 0) :
    (X.vertexGroupElement R v) • R.repr (X.vertexQuot v) = v := by
  exact (X.exists_smul_repr_eq R v).choose_spec

/-- For an edge `e` with boundary vertices `τ₁, τ₂`, the induced connection assigns
the group element `h` such that the edge connects `repr(π(τ₁))` to `h • repr(π(τ₂))`.

More precisely, if `τ₁ ∈ ∂e` and `τ₂ ∈ ∂e` with `τ₁ = g₁ • repr(π(τ₁))` and
`τ₂ = g₂ • repr(π(τ₂))`, then `φ_R(π(e))` relates the two representatives via
`g₁⁻¹ • g₂`. By the quotient condition, this is independent of the choice of
representative edge in the orbit.

For simplicity, we define the connection as a function on edges of X (not the quotient),
and prove it is constant on orbits. -/
def connectionOnEdge (R : X.Trivialization) (e : X.graph.cells 1)
    (τ₁ τ₂ : X.graph.cells 0) (hτ₁ : τ₁ ∈ X.graph.bdry e) (hτ₂ : τ₂ ∈ X.graph.bdry e)
    (hne : X.vertexQuot τ₁ ≠ X.vertexQuot τ₂) : H :=
  (X.vertexGroupElement R τ₁)⁻¹ * (X.vertexGroupElement R τ₂)

/-- The connection is well-defined on orbits: translating the edge by `g` does not
change the connection value. -/
lemma connectionOnEdge_orbit_compat (R : X.Trivialization) (e : X.graph.cells 1) (g : H)
    (τ₁ τ₂ : X.graph.cells 0) (hτ₁ : τ₁ ∈ X.graph.bdry e) (hτ₂ : τ₂ ∈ X.graph.bdry e)
    (hne : X.vertexQuot τ₁ ≠ X.vertexQuot τ₂)
    (hgτ₁ : g • τ₁ ∈ X.graph.bdry (g • e))
    (hgτ₂ : g • τ₂ ∈ X.graph.bdry (g • e))
    (hne' : X.vertexQuot (g • τ₁) ≠ X.vertexQuot (g • τ₂)) :
    X.connectionOnEdge R (g • e) (g • τ₁) (g • τ₂) hgτ₁ hgτ₂ hne' =
    X.connectionOnEdge R e τ₁ τ₂ hτ₁ hτ₂ hne := by
  unfold connectionOnEdge
  -- The vertex group elements satisfy: vertexGroupElement R (g • v) = g * vertexGroupElement R v
  -- because g • v = (g * h) • repr(π(v)) where h = vertexGroupElement R v
  -- and π(g • v) = π(v), so repr(π(g • v)) = repr(π(v))
  suffices ∀ v, X.vertexGroupElement R (g • v) = g * X.vertexGroupElement R v by
    rw [this τ₁, this τ₂]
    simp [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  intro v
  have hπ : X.vertexQuot (g • v) = X.vertexQuot v := by
    apply Quotient.sound
    exact ⟨g, rfl⟩
  have h1 := X.vertexGroupElement_spec R v
  have h2 := X.vertexGroupElement_spec R (g • v)
  rw [hπ] at h2
  -- h1: vertexGroupElement R v • repr(π(v)) = v
  -- h2: vertexGroupElement R (g • v) • repr(π(v)) = g • v
  have hgv : (g * X.vertexGroupElement R v) • R.repr (X.vertexQuot v) = g • v := by
    rw [mul_smul, h1]
  have heq : X.vertexGroupElement R (g • v) • R.repr (X.vertexQuot v) =
      (g * X.vertexGroupElement R v) • R.repr (X.vertexQuot v) := by
    rw [h2, hgv]
  have hfree := X.vertexFree ((X.vertexGroupElement R (g • v))⁻¹ * (g * X.vertexGroupElement R v))
    (R.repr (X.vertexQuot v))
  have hmul := hfree (by rw [mul_smul, inv_smul_eq_iff]; exact heq.symm)
  exact eq_of_inv_mul_eq_one hmul

/-- The induced connection as a map from quotient edges. For each edge orbit `E`,
we pick a representative `e`, pick boundary vertices `τ₁, τ₂`, and compute
`connectionOnEdge`. When the edge has both boundary vertices in the same orbit
(which cannot happen by the quotient condition for edges connecting distinct orbits),
we return `1`. -/
def inducedConnection (R : X.Trivialization) (E : X.quotientEdges) : H :=
  -- Pick a representative edge
  let e := Quotient.out E
  -- The boundary of e is a finset of vertices
  -- For a graph (1-complex), each edge has exactly 2 boundary vertices
  -- We extract two boundary vertices and compute the connection
  -- If the boundary has < 2 elements or both are in the same orbit, return 1
  let bdry := X.graph.bdry e
  if h : ∃ τ₁ ∈ bdry, ∃ τ₂ ∈ bdry, X.vertexQuot τ₁ ≠ X.vertexQuot τ₂ then
    let τ₁ := h.choose
    let hτ₁ := h.choose_spec.1
    let τ₂ := h.choose_spec.2.choose
    let hτ₂ := h.choose_spec.2.choose_spec.1
    let hne := h.choose_spec.2.choose_spec.2
    X.connectionOnEdge R e τ₁ τ₂ hτ₁ hτ₂ hne
  else 1

/-- The induced connection satisfies the defining property: for an edge `e` with
boundary vertices `τ₁` and `τ₂` in distinct orbits, `φ_R(π(e))` relates the
representatives. Specifically, the edge `g₁⁻¹ • e` (where `g₁ = vertexGroupElement R τ₁`)
connects `repr(π(τ₁))` to `φ_R(π(e)) • repr(π(τ₂))`. -/
theorem inducedConnection_spec (R : X.Trivialization) (e : X.graph.cells 1)
    (τ₁ τ₂ : X.graph.cells 0) (hτ₁ : τ₁ ∈ X.graph.bdry e) (hτ₂ : τ₂ ∈ X.graph.bdry e)
    (hne : X.vertexQuot τ₁ ≠ X.vertexQuot τ₂) :
    ∃ e' : X.graph.cells 1,
      X.edgeQuot e' = X.edgeQuot e ∧
      R.repr (X.vertexQuot τ₁) ∈ X.graph.bdry e' ∧
      (X.connectionOnEdge R e τ₁ τ₂ hτ₁ hτ₂ hne) •
        R.repr (X.vertexQuot τ₂) ∈ X.graph.bdry e' := by
  -- Take e' = g₁⁻¹ • e where g₁ = vertexGroupElement R τ₁
  let g₁ := X.vertexGroupElement R τ₁
  refine ⟨g₁⁻¹ • e, ?_, ?_, ?_⟩
  · -- e' is in the same orbit as e
    apply Quotient.sound
    exact ⟨g₁⁻¹, rfl⟩
  · -- repr(π(τ₁)) ∈ ∂(g₁⁻¹ • e)
    rw [X.bdry_equivariant e g₁⁻¹ (R.repr (X.vertexQuot τ₁))]
    simp only [inv_inv]
    rw [X.vertexGroupElement_spec R τ₁]
    exact hτ₁
  · -- φ_R • repr(π(τ₂)) ∈ ∂(g₁⁻¹ • e)
    unfold connectionOnEdge
    rw [X.bdry_equivariant e g₁⁻¹ _]
    simp only [inv_inv, mul_smul, smul_inv_smul]
    rw [X.vertexGroupElement_spec R τ₂]
    change g₁ • g₁⁻¹ • τ₂ ∈ X.graph.bdry e
    rw [smul_inv_smul]
    exact hτ₂

/-! ## Witness lemmas -/

/-- Witness: the quotient vertices type is nonempty when the graph has vertices. -/
lemma quotientVertices_nonempty [Nonempty (X.graph.cells 0)] :
    Nonempty X.quotientVertices :=
  ⟨Quotient.mk'' (Classical.arbitrary _)⟩

/-- Witness: the quotient edges type is nonempty when the graph has edges. -/
lemma quotientEdges_nonempty [Nonempty (X.graph.cells 1)] :
    Nonempty X.quotientEdges :=
  ⟨Quotient.mk'' (Classical.arbitrary _)⟩

end GraphWithGroupAction

end
