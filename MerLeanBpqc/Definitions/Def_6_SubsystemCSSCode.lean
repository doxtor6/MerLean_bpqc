import MerLeanBpqc.Definitions.Def_4_CSSCode
import Mathlib.LinearAlgebra.Projection

/-!
# Definition 6: Subsystem CSS Code

A subsystem CSS code is a CSS code (Def_4) where the homology
`H₀ = ker(H_X) / im(H_Z^T)` is split as a direct sum of `𝔽₂`-vector spaces
`H₀ = H₀^L ⊕ H₀^G`, where `H₀^L` corresponds to logical qubits and `H₀^G`
corresponds to gauge qubits.

The nondegenerate pairing between `H₀` and the cohomology `H⁰` (Def_2) induces
a compatible splitting `H⁰ = H⁰_L ⊕ H⁰_G`, where compatible means `H₀^L` pairs
nondegenerately with `H⁰_L` and `H₀^G` pairs nondegenerately with `H⁰_G`
(and the cross-pairings vanish).

The Z-distance `d_Z` is the minimum Hamming weight of a representative of a
homology class whose projection onto `H₀^L` is nonzero. The X-distance `d_X`
is defined equivalently using the cohomology splitting. The distance is
`d = min(d_X, d_Z)`.

## Main Definitions
- `SubsystemCSSCode` — a subsystem CSS code with direct sum splittings
- `SubsystemCSSCode.dZ` — the Z-distance (using homology projection)
- `SubsystemCSSCode.dX` — the X-distance (using cohomology projection)
- `SubsystemCSSCode.distance` — the overall distance `d = min(d_X, d_Z)`
- `SubsystemCSSCode.logicalQubits` — the number of logical qubits `dim H₀^L`
-/

open CategoryTheory

namespace CSSCode

variable {n rX rZ : ℕ} (Q : CSSCode n rX rZ)

/-! ## Homology and cohomology quotient types -/

/-- The submodule of boundaries inside cycles for the CSS code homology:
`im(H_Z^T) ∩ ker(H_X)` viewed as a submodule of `ker(H_X)`. -/
noncomputable abbrev boundariesInCycles : Submodule 𝔽₂ ↥(LinearMap.ker Q.HX) :=
  (LinearMap.range Q.HZT).comap (LinearMap.ker Q.HX).subtype

/-- The homology type `H₀ = ker(H_X) / im(H_Z^T)`. -/
noncomputable abbrev Homology₀ : Type :=
  ↥(LinearMap.ker Q.HX) ⧸ Q.boundariesInCycles

/-- The submodule of coboundaries inside cocycles for the CSS code cohomology:
`im(H_X^T) ∩ ker(H_Z)` viewed as a submodule of `ker(H_Z)`, where
`H_Z = (H_Z^T)^T = dualMap(H_Z^T)` and `H_X^T = dualMap(H_X)`. -/
noncomputable abbrev coboundariesInCocycles :
    Submodule 𝔽₂ ↥(LinearMap.ker Q.HZT.dualMap) :=
  (LinearMap.range Q.HX.dualMap).comap (LinearMap.ker Q.HZT.dualMap).subtype

/-- The cohomology type `H⁰ = ker(H_Z) / im(H_X^T)`. -/
noncomputable abbrev Cohomology₀ : Type :=
  ↥(LinearMap.ker Q.HZT.dualMap) ⧸ Q.coboundariesInCocycles

/-- The quotient map from `ker(H_X)` to the homology `H₀`. -/
noncomputable abbrev homologyMkQ :
    ↥(LinearMap.ker Q.HX) →ₗ[𝔽₂] Q.Homology₀ :=
  Q.boundariesInCycles.mkQ

/-- The quotient map from `ker(H_Z)` (= `ker(dualMap H_Z^T)`) to the cohomology `H⁰`. -/
noncomputable abbrev cohomologyMkQ :
    ↥(LinearMap.ker Q.HZT.dualMap) →ₗ[𝔽₂] Q.Cohomology₀ :=
  Q.coboundariesInCocycles.mkQ

end CSSCode

/-! ## Subsystem CSS Code Structure -/

/-- A subsystem CSS code is a CSS code (Def_4) together with a direct sum decomposition
of the homology `H₀ = H₀^L ⊕ H₀^G` and a compatible splitting of the cohomology
`H⁰ = H⁰_L ⊕ H⁰_G`, induced by a linear equivalence `H₀ ≃ H⁰` that respects the
decomposition.

The submodule `HL` (logical) and `HG` (gauge) of the homology quotient satisfy
`IsCompl HL HG`, giving the direct sum decomposition. The linear equivalence `equiv`
between homology and cohomology (encoding the nondegenerate pairing) induces
the cohomology splitting: `H⁰_L = equiv(H₀^L)` and `H⁰_G = equiv(H₀^G)`.
This ensures that `H₀^L` pairs nondegenerately with `H⁰_L`, `H₀^G` pairs
nondegenerately with `H⁰_G`, and the cross-pairings vanish. -/
structure SubsystemCSSCode (n rX rZ : ℕ) extends CSSCode n rX rZ where
  /-- The logical subspace `H₀^L` of the homology `H₀ = ker(H_X) / im(H_Z^T)`. -/
  HL : Submodule 𝔽₂ (toCSSCode.Homology₀)
  /-- The gauge subspace `H₀^G` of the homology. -/
  HG : Submodule 𝔽₂ (toCSSCode.Homology₀)
  /-- The direct sum decomposition `H₀ = H₀^L ⊕ H₀^G`. -/
  hcompl : IsCompl HL HG
  /-- The linear equivalence `H₀ ≃ H⁰` between homology and cohomology, encoding
  the nondegenerate pairing. The cohomology splitting is induced by this map:
  `H⁰_L = equiv(H₀^L)` and `H⁰_G = equiv(H₀^G)`. -/
  equiv : toCSSCode.Homology₀ ≃ₗ[𝔽₂] toCSSCode.Cohomology₀

namespace SubsystemCSSCode

variable {n rX rZ : ℕ} (S : SubsystemCSSCode n rX rZ)

/-! ## Derived cohomology splitting -/

/-- The logical subspace `H⁰_L` of the cohomology, defined as the image of `H₀^L`
under the equivalence `equiv : H₀ ≃ H⁰`. -/
noncomputable def coHL : Submodule 𝔽₂ (S.toCSSCode.Cohomology₀) :=
  Submodule.map S.equiv.toLinearMap S.HL

/-- The gauge subspace `H⁰_G` of the cohomology, defined as the image of `H₀^G`
under the equivalence `equiv : H₀ ≃ H⁰`. -/
noncomputable def coHG : Submodule 𝔽₂ (S.toCSSCode.Cohomology₀) :=
  Submodule.map S.equiv.toLinearMap S.HG

/-- The cohomology splitting `H⁰ = H⁰_L ⊕ H⁰_G` is induced by the homology splitting
and the linear equivalence. -/
theorem cohcompl : IsCompl S.coHL S.coHG := by
  constructor
  · -- Disjointness: coHL ⊓ coHG = ⊥
    rw [coHL, coHG, Submodule.disjoint_def]
    intro x hx1 hx2
    rw [Submodule.mem_map] at hx1 hx2
    obtain ⟨a, ha, rfl⟩ := hx1
    obtain ⟨b, hb, heq⟩ := hx2
    have hab : a = b := by
      have hinj := S.equiv.injective
      exact hinj (heq.symm)
    subst hab
    have hmem : a ∈ S.HL ⊓ S.HG := Submodule.mem_inf.mpr ⟨ha, hb⟩
    rw [S.hcompl.inf_eq_bot, Submodule.mem_bot] at hmem
    simp [hmem, map_zero]
  · -- Codisjointness: coHL ⊔ coHG = ⊤
    rw [codisjoint_iff, coHL, coHG, ← Submodule.map_sup]
    rw [S.hcompl.sup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr S.equiv.surjective

/-! ## Projection onto the logical subspace -/

/-- The linear projection from `H₀` onto the logical subspace `H₀^L`, using the
direct sum decomposition `H₀ = H₀^L ⊕ H₀^G`. -/
noncomputable def projL : S.toCSSCode.Homology₀ →ₗ[𝔽₂] ↥S.HL :=
  S.HL.linearProjOfIsCompl S.HG S.hcompl

/-- The linear projection from `H⁰` onto the logical cohomology subspace `H⁰_L`,
using the derived direct sum decomposition `H⁰ = H⁰_L ⊕ H⁰_G`. -/
noncomputable def coprojL : S.toCSSCode.Cohomology₀ →ₗ[𝔽₂] ↥S.coHL :=
  S.coHL.linearProjOfIsCompl S.coHG S.cohcompl

/-! ## Number of logical qubits -/

/-- The number of logical qubits `k = dim H₀^L`. In a subsystem code, only the
logical subspace `H₀^L` encodes information, while the gauge subspace `H₀^G`
corresponds to gauge degrees of freedom. -/
noncomputable def logicalQubits : ℕ :=
  Module.finrank 𝔽₂ ↥S.HL

/-! ## Subsystem Z-distance -/

/-- The Z-distance `d_Z` for a subsystem CSS code. This is the minimum Hamming weight
of a representative `z ∈ ker(H_X)` of a homology class `[z] ∈ H₀` whose projection
onto the logical subspace `H₀^L` is nonzero. Equivalently, `d_Z` is the largest
integer such that every representative of a class with nonzero logical projection
has Hamming weight at least `d_Z`.

By convention, `d_Z = 0` when there is no such class (i.e., `H₀^L = 0`). -/
noncomputable def dZ : ℕ :=
  sInf {w : ℕ | ∃ x : Fin n → 𝔽₂, ∃ (hx : x ∈ LinearMap.ker S.HX),
    S.projL (S.toCSSCode.homologyMkQ ⟨x, hx⟩) ≠ 0 ∧
    hammingWeight x = w}

/-! ## Subsystem X-distance -/

/-- The X-distance `d_X` for a subsystem CSS code. This is the minimum Hamming weight
(under the `dotProductEquiv` identification `Dual(𝔽₂^n) ≅ 𝔽₂^n`) of a representative
`ζ ∈ ker(H_Z)` of a cohomology class `[ζ] ∈ H⁰` whose projection onto `H⁰_L` is
nonzero.

By convention, `d_X = 0` when `H⁰_L = 0`. -/
noncomputable def dX : ℕ :=
  sInf {w : ℕ | ∃ φ : Module.Dual 𝔽₂ (Fin n → 𝔽₂), ∃ (hφ : φ ∈ LinearMap.ker S.HZT.dualMap),
    S.coprojL (S.toCSSCode.cohomologyMkQ ⟨φ, hφ⟩) ≠ 0 ∧
    hammingNorm ((dotProductEquiv 𝔽₂ (Fin n)).symm φ) = w}

/-! ## Overall distance -/

/-- The overall distance `d = min(d_X, d_Z)`. -/
noncomputable def distance : ℕ := min S.dX S.dZ

/-! ## Code parameter predicates -/

/-- A subsystem CSS code is an `[[n, k, d]]`-code if it has `k` logical qubits
and distance `d`. -/
def IsNKDCode (k d : ℕ) : Prop :=
  S.logicalQubits = k ∧ S.distance = d

/-- A subsystem CSS code is an `[[n, k, d_X, d_Z]]`-code when X- and Z-distances differ. -/
def IsNKDXZCode (k dX_val dZ_val : ℕ) : Prop :=
  S.logicalQubits = k ∧ S.dX = dX_val ∧ S.dZ = dZ_val

end SubsystemCSSCode
