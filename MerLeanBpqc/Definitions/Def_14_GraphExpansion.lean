import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Sqrt

/-!
# Definition 14: Graph Expansion

## Main Results
- `adjMatrix_isHermitian`: The adjacency matrix of a simple graph over ℝ is Hermitian.
- `adjEigenvalues`: The eigenvalues of the adjacency matrix, sorted in decreasing order.
- `adjEigenvalues_antitone`: The eigenvalues are sorted in decreasing order.
- `secondLargestEigenvalue`: The second-largest eigenvalue λ₂.
- `spectralGap`: The spectral gap s - λ₂.
- `IsExpanderFamily`: A family of s-regular graphs is expanding if the spectral gap is uniformly bounded below.
- `IsRamanujan`: A connected s-regular graph is Ramanujan if |λ| ≤ 2√(s-1) for all eigenvalues with |λ| < s.
-/

open Matrix SimpleGraph Fintype

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace GraphExpansion

/-! ## Adjacency matrix is Hermitian -/

/-- The adjacency matrix of a simple graph over `ℝ` is Hermitian.
For real matrices, Hermitian is equivalent to symmetric, and the adjacency
matrix is symmetric by `SimpleGraph.isSymm_adjMatrix`. -/
lemma adjMatrix_isHermitian (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.adjMatrix ℝ).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, G.isSymm_adjMatrix]

/-! ## Eigenvalues of the adjacency matrix -/

/-- The eigenvalues of the adjacency matrix `G.adjMatrix ℝ`, sorted in decreasing
order and indexed by `Fin (Fintype.card V)`. -/
noncomputable def adjEigenvalues (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fin (Fintype.card V) → ℝ :=
  (adjMatrix_isHermitian G).eigenvalues₀

/-- The eigenvalues of the adjacency matrix are sorted in decreasing order
(antitone): `adjEigenvalues G i ≥ adjEigenvalues G j` whenever `i ≤ j`. -/
theorem adjEigenvalues_antitone (G : SimpleGraph V) [DecidableRel G.Adj] :
    Antitone (adjEigenvalues G) :=
  (adjMatrix_isHermitian G).eigenvalues₀_antitone

/-! ## Second-largest eigenvalue and spectral gap -/

/-- The second-largest eigenvalue `λ₂` of the adjacency matrix, defined when the
graph has at least 2 vertices (`2 ≤ Fintype.card V`). This is `adjEigenvalues G ⟨1, _⟩`,
the eigenvalue at index 1 in the decreasing sequence. -/
noncomputable def secondLargestEigenvalue (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 2 ≤ Fintype.card V) : ℝ :=
  adjEigenvalues G ⟨1, by omega⟩

/-- The spectral gap of a finite `s`-regular graph is `(s : ℝ) - λ₂`, where `λ₂`
is the second-largest eigenvalue of the adjacency matrix. A larger spectral gap
indicates better expansion properties. -/
noncomputable def spectralGap (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hcard : 2 ≤ Fintype.card V) : ℝ :=
  (s : ℝ) - secondLargestEigenvalue G hcard

/-! ## Expander families -/

/-- A family of `s`-regular simple graphs `{X_i}_{i : ι}` is a family of **expanders**
if there exists `ε > 0` such that the second-largest eigenvalue satisfies
`λ₂(X_i) ≤ s - ε` for all `i`. Equivalently, the spectral gap is uniformly bounded
below by `ε` across the family. The vertex sets are `Fin (n i)` with varying sizes
`n : ι → ℕ`, each having at least 2 vertices (ensured by `hcard`). The regularity
degree `s` is uniform across the family. -/
def IsExpanderFamily (ι : Type*) (n : ι → ℕ) (s : ℕ)
    (G : ∀ i, SimpleGraph (Fin (n i)))
    [∀ i, DecidableRel (G i).Adj]
    (hcard : ∀ i, 2 ≤ Fintype.card (Fin (n i))) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ i, secondLargestEigenvalue (G i) (hcard i) ≤ (s : ℝ) - ε

/-! ## Ramanujan graphs -/

/-- A finite `s`-regular graph is **Ramanujan** if the second-largest eigenvalue
satisfies the optimal bound `λ₂ ≤ 2√(s - 1)`. This is the best possible bound
on `λ₂` for `s`-regular graphs, achieved by Ramanujan graphs.

More precisely, a connected `s`-regular graph is Ramanujan if every eigenvalue
`λ` of the adjacency matrix with `|λ| < s` satisfies `|λ| ≤ 2√(s-1)`. -/
noncomputable def IsRamanujan (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hcard : 2 ≤ Fintype.card V) : Prop :=
  ∀ i : Fin (Fintype.card V),
    |adjEigenvalues G i| < (s : ℝ) →
    |adjEigenvalues G i| ≤ 2 * Real.sqrt ((s : ℝ) - 1)

end GraphExpansion
