import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import MerLeanBpqc.Definitions.Def_14_GraphExpansion

/-!
# Definition 20: Cayley Graph

## Main Results
- `cayleyGraph`: The Cayley graph `Cay(G, S)` of a finite group `G` with symmetric
  generating set `S ⊆ G \ {1}`.
- `cayleyGraph_isRegularOfDegree`: The Cayley graph is `|S|`-regular.
-/

open SimpleGraph Fintype Finset

namespace CayleyGraph

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- A symmetric generating set `S ⊆ G \ {1}`: a finite set of group elements not
containing the identity, closed under inverses. -/
structure SymmGenSet (G : Type*) [Group G] [DecidableEq G] where
  /-- The underlying finite set of generators. -/
  carrier : Finset G
  /-- The identity is not in `S`. -/
  one_not_mem : (1 : G) ∉ carrier
  /-- `S` is closed under inverses: `s ∈ S → s⁻¹ ∈ S`. -/
  inv_mem : ∀ s ∈ carrier, s⁻¹ ∈ carrier

variable (S : SymmGenSet G)

/-- The (undirected) Cayley graph `Cay(G, S)` is the simple graph with vertex set `G`,
where `g` and `g'` are adjacent iff there exists `s ∈ S` such that `g' = s * g`.
Since `S` is symmetric, adjacency is symmetric; since `1 ∉ S`, there are no self-loops. -/
def cayleyGraph : SimpleGraph G where
  Adj g g' := ∃ s ∈ S.carrier, g' = s * g
  symm := by
    intro g g' ⟨s, hs, hsg⟩
    refine ⟨s⁻¹, S.inv_mem s hs, ?_⟩
    subst hsg
    simp [mul_assoc]
  loopless := by
    intro g ⟨s, hs, hsg⟩
    have : s = 1 := by
      have := congr_arg (· * g⁻¹) hsg
      simp at this
      exact this.symm
    exact S.one_not_mem (this ▸ hs)

instance cayleyGraph_decidableAdj : DecidableRel (cayleyGraph S).Adj := by
  intro g g'
  unfold cayleyGraph
  exact decidable_of_iff (∃ s ∈ S.carrier, g' = s * g) Iff.rfl

/-- Each vertex `g` has exactly `|S|` neighbors `{s * g : s ∈ S}`, which are
pairwise distinct because left multiplication by distinct group elements yields
distinct results. -/
theorem cayleyGraph_isRegularOfDegree :
    (cayleyGraph S).IsRegularOfDegree S.carrier.card := by
  intro v
  -- The neighbor set of v is {s * v | s ∈ S}
  -- We show the degree equals |S| by constructing a bijection
  have h : (cayleyGraph S).neighborFinset v = S.carrier.image (· * v) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, cayleyGraph, Finset.mem_image]
    constructor
    · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
  simp only [SimpleGraph.degree, h, Finset.card_image_of_injective _ (fun a b hab => mul_right_cancel hab)]

/-- The neighbor finset of `v` in the Cayley graph is `{s * v | s ∈ S}`. -/
lemma cayleyGraph_neighborFinset (v : G) :
    (cayleyGraph S).neighborFinset v = S.carrier.image (· * v) := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, cayleyGraph, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩

/-- Witness: the Cayley graph has edges when `S` is nonempty. -/
lemma cayleyGraph_nonempty_of_nonempty (hS : S.carrier.Nonempty) :
    ∃ g g' : G, (cayleyGraph S).Adj g g' := by
  obtain ⟨s, hs⟩ := hS
  exact ⟨1, s * 1, s, hs, rfl⟩

end CayleyGraph
