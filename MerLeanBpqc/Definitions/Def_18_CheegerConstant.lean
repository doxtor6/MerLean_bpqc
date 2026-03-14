import MerLeanBpqc.Definitions.Def_14_GraphExpansion
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Definition 18: Cheeger Constant

The Cheeger constant of a finite graph `G`, viewed as a 1-dimensional cell complex (Def_7),
is `h(G) = min_{S} |δS| / |S|` where the minimum is over nonempty subsets `S ⊆ V` with
`2|S| ≤ |V|`, and `δS` is the edge boundary of `S`.

## Main Results
- `edgeBoundary` — the edge boundary `δS`
- `mem_edgeBoundary` — membership characterization
- `EligibleSubset` — eligible subsets for the Cheeger constant
- `isoperimetricRatio` — the ratio `|δS| / |S|`
- `cheegerConstant` — the Cheeger constant `h(G)`
- `eligibleSubset_nonempty` — eligible subsets exist when `|V| ≥ 2`
- `cheegerConstant_nonneg` — `h(G) ≥ 0`
- `cheegerInequalities` — the Cheeger inequalities relating `h(G)` to the spectral gap
-/

open Finset SimpleGraph BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace CheegerConstant

/-! ## Edge Boundary -/

/-- The edge boundary `δS = {{u,v} ∈ E(G) | u ∈ S, v ∉ S}` of a vertex subset `S`.
An edge is in `δS` iff it has one endpoint in `S` and one endpoint outside `S`.
By the symmetry of `Sym2`, it suffices to check that there exist `a ∈ S, b ∉ S`
with `e = s(a, b)`. -/
noncomputable def edgeBoundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e =>
    e.out.1 ∈ S ∧ e.out.2 ∉ S ∨ e.out.2 ∈ S ∧ e.out.1 ∉ S

/-- Membership in the edge boundary: `e ∈ δS` iff `e` is an edge of `G` and
there exist `a ∈ S, b ∉ S` with `e = s(a, b)`. -/
theorem mem_edgeBoundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (e : Sym2 V) :
    e ∈ edgeBoundary G S ↔
      e ∈ G.edgeFinset ∧ ∃ a b, s(a, b) = e ∧ a ∈ S ∧ b ∉ S := by
  constructor
  · intro he
    simp only [edgeBoundary, Finset.mem_filter] at he
    obtain ⟨hedge, h⟩ := he
    refine ⟨hedge, ?_⟩
    obtain ⟨ha, hb⟩ | ⟨hb, ha⟩ := h
    · exact ⟨e.out.1, e.out.2, by rw [Sym2.mk, e.out_eq], ha, hb⟩
    · exact ⟨e.out.2, e.out.1, by
        rw [Sym2.eq_swap, Sym2.mk, e.out_eq], hb, ha⟩
  · intro ⟨hedge, a, b, hab, ha, hb⟩
    simp only [edgeBoundary, Finset.mem_filter]
    refine ⟨hedge, ?_⟩
    subst hab
    -- Goal: out.1 ∈ S ∧ out.2 ∉ S ∨ out.2 ∈ S ∧ out.1 ∉ S
    have hout := (s(a, b)).out_eq
    -- hout : Sym2.mk (s(a,b)).out = s(a, b)
    -- i.e., s(out.1, out.2) = s(a, b)
    rcases Sym2.mk_eq_mk_iff.mp hout with heq | heq
    · -- heq : (out.1, out.2) = (a, b)
      have h1 : (Quot.out s(a, b)).1 = a := congr_arg Prod.fst heq
      have h2 : (Quot.out s(a, b)).2 = b := congr_arg Prod.snd heq
      left; rw [h1, h2]; exact ⟨ha, hb⟩
    · -- heq : (out.1, out.2) = (b, a)
      have h1 : (Quot.out s(a, b)).1 = b := congr_arg Prod.fst heq
      have h2 : (Quot.out s(a, b)).2 = a := congr_arg Prod.snd heq
      right; rw [h1, h2]; exact ⟨ha, hb⟩

/-- The edge boundary is a subset of the edge set. -/
theorem edgeBoundary_subset_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : edgeBoundary G S ⊆ G.edgeFinset :=
  Finset.filter_subset _ _

/-- An edge `{u, v}` with `u ∈ S` and `v ∉ S` is in the edge boundary. -/
theorem adj_mem_edgeBoundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {u v : V} (hadj : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S) :
    s(u, v) ∈ edgeBoundary G S := by
  rw [mem_edgeBoundary]
  exact ⟨G.mem_edgeFinset.mpr hadj, u, v, rfl, hu, hv⟩

/-! ## Eligible Subsets and Isoperimetric Ratio -/

/-- The eligible subsets for the Cheeger constant: nonempty subsets `S ⊆ V`
with `2|S| ≤ |V|`. The paper uses strict inequality `|S| < |V|/2` in one place,
but `|S| ≤ |V|/2` elsewhere; the standard convention is `2|S| ≤ |V|`. -/
def EligibleSubset (S : Finset V) : Prop :=
  S.Nonempty ∧ 2 * S.card ≤ Fintype.card V

/-- The isoperimetric ratio `|δS| / |S|` for a subset `S`. -/
noncomputable def isoperimetricRatio (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℝ :=
  (edgeBoundary G S).card / S.card

/-- The Cheeger constant `h(G) = inf_{S} |δS| / |S|` where the infimum is over
nonempty subsets `S ⊆ V` with `2|S| ≤ |V|`. When no eligible subset exists
(e.g., `|V| < 2`), the value is `0` by the convention `sInf ∅ = 0` for `ℝ`. -/
noncomputable def cheegerConstant (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sInf { r : ℝ | ∃ S : Finset V, EligibleSubset S ∧ isoperimetricRatio G S = r }

/-! ## Eligible Subsets Exist -/

/-- When `|V| ≥ 2`, there exists an eligible subset (any singleton). -/
theorem eligibleSubset_nonempty (hcard : 2 ≤ Fintype.card V) :
    ∃ S : Finset V, EligibleSubset S := by
  have hne := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  obtain ⟨v⟩ := hne
  exact ⟨{v}, Finset.singleton_nonempty v, by simp [Finset.card_singleton]; omega⟩

/-! ## Cheeger Constant is Nonneg -/

/-- The Cheeger constant is nonneg: `0 ≤ h(G)`. -/
theorem cheegerConstant_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] :
    0 ≤ cheegerConstant G := by
  unfold cheegerConstant
  by_cases h : 2 ≤ Fintype.card V
  · obtain ⟨S, hS⟩ := eligibleSubset_nonempty h
    apply le_csInf (Set.nonempty_of_mem (show isoperimetricRatio G S ∈ {r | ∃ S, EligibleSubset S ∧ isoperimetricRatio G S = r} from ⟨S, hS, rfl⟩))
    rintro r ⟨S', -, hr⟩
    rw [← hr]
    unfold isoperimetricRatio
    positivity
  · -- When |V| < 2, no eligible subsets exist, so the set is empty
    -- and sInf ∅ = 0 for ℝ (conditionally complete lattice convention)
    simp only [not_le] at h
    have hempty : { r : ℝ | ∃ S : Finset V, EligibleSubset S ∧ isoperimetricRatio G S = r } = ∅ := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨S, ⟨hne, hcard⟩, _⟩
      have := hne.card_pos
      omega
    rw [hempty, Real.sInf_empty]

end CheegerConstant

/-! ## Cheeger Inequalities -/

open GraphExpansion

/-- The **Cheeger inequalities** for a connected `s`-regular graph `G` with
second-largest adjacency eigenvalue `λ₂` (Def_14) state that
`(s - λ₂)/2 ≤ h(G) ≤ √(2s(s - λ₂))`.

The lower bound `(s - λ₂)/2 ≤ h(G)` follows from the variational characterization
of `λ₂` (Courant–Fischer), and the upper bound `h(G) ≤ √(2s(s - λ₂))` from the
sweep-cut argument on the second eigenvector.

This is stated as an axiom because the proof requires spectral theory infrastructure
(Courant–Fischer min-max theorem, sweep-cut analysis) not available in Mathlib. -/
axiom cheegerInequalities (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hcard : 2 ≤ Fintype.card V)
    (hconn : G.Connected) (hreg : G.IsRegularOfDegree s) :
    let lam2 := secondLargestEigenvalue G hcard
    let hG := CheegerConstant.cheegerConstant G
    ((s : ℝ) - lam2) / 2 ≤ hG ∧ hG ≤ Real.sqrt (2 * s * ((s : ℝ) - lam2))
