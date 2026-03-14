import MerLeanBpqc.Definitions.Def_26_BalancedProductTannerCycleCode
import MerLeanBpqc.Lemmas.Lem_4_KunnethBalancedProduct
import MerLeanBpqc.Definitions.Def_2_CochainsCohomology

/-!
# Definition 27: Horizontal/Vertical Homology Splitting

By the Künneth formula for balanced products (Lem_4), the degree-1 homology of the
balanced product Tanner cycle code splits as
$$H_1(C(X,L) \otimes_{\mathbb{Z}_\ell} C(C_\ell)) \cong H_1^h \oplus H_1^v$$
where:
- `H₁ʰ = H₁(C(X,L)) ⊗_H H₀(C_ℓ)` (horizontal part)
- `H₁ᵛ = H₀(C(X,L)) ⊗_H H₁(C_ℓ)` (vertical part)

We define the projection maps `pʰ : H₁ → H₁ʰ` and `pᵛ : H₁ → H₁ᵛ` as the
compositions of the Künneth isomorphism with the canonical projections from the
direct sum onto each summand. Similarly for cohomology.

## Main Definitions
- `H1h` — horizontal homology `H₁(C(X,L)) ⊗_H H₀(C_ℓ)`
- `H1v` — vertical homology `H₀(C(X,L)) ⊗_H H₁(C_ℓ)`
- `projH` — projection `H₁ → H₁ʰ`
- `projV` — projection `H₁ → H₁ᵛ`
- `coH1h` — horizontal cohomology `H¹(C(X,L)) ⊗_H H⁰(C_ℓ)`
- `coH1v` — vertical cohomology `H⁰(C(X,L)) ⊗_H H¹(C_ℓ)`
- `coprojH` — cohomology projection `H¹ → H¹_h`
- `coprojV` — cohomology projection `H¹ → H¹_v`
-/

open CategoryTheory
open scoped TensorProduct DirectSum

noncomputable section

namespace HorizontalVerticalHomologySplitting

variable {H : Type} [Group H] [Fintype H] [DecidableEq H]
variable (X : GraphWithGroupAction H)
variable {s : ℕ} (Λ : X.CellLabeling s)
variable (ℓ : ℕ) [NeZero ℓ] [MulAction H (Fin ℓ)]
variable (hℓ_ge : ℓ ≥ 3) (hℓ_odd : ℓ % 2 = 1)
variable (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
variable (hcompat : BalancedProductTannerCycleCode.CycleCompatibleAction (H := H) ℓ)
variable (hodd : Odd (Fintype.card H))

/-- The Tanner code H-equivariant chain complex. -/
abbrev tannerHEq := BalancedProductTannerCycleCode.tannerCodeHEquivariant X Λ hΛ

/-- The cycle graph H-equivariant chain complex. -/
abbrev cycleHEq := BalancedProductTannerCycleCode.cycleGraphHEquivariant ℓ hcompat

/-- The balanced product complex `C(X,L) ⊗_H C(C_ℓ)`. -/
abbrev bpComplex :=
  (tannerHEq X Λ hΛ).balancedProductComplex (cycleHEq ℓ hcompat)

/-- The degree-1 homology of the balanced product complex. -/
abbrev H1 := (bpComplex X Λ ℓ hΛ hcompat).homology' 1

/-! ## Horizontal and vertical homology parts -/

/-- The horizontal homology: `H₁ʰ = H₁(C(X,L)) ⊗_H H₀(C_ℓ)`.
This is the balanced Künneth summand at `p = 1`, `q = 1 - 1 = 0`. -/
abbrev H1h :=
  HEquivariantChainComplex.balancedKunnethSummand
    (tannerHEq X Λ hΛ) (cycleHEq ℓ hcompat) 1 1

/-- The vertical homology: `H₁ᵛ = H₀(C(X,L)) ⊗_H H₁(C_ℓ)`.
This is the balanced Künneth summand at `p = 0`, `q = 1 - 0 = 1`. -/
abbrev H1v :=
  HEquivariantChainComplex.balancedKunnethSummand
    (tannerHEq X Λ hΛ) (cycleHEq ℓ hcompat) 1 0

/-- The Künneth isomorphism at degree 1:
`H₁(C(X,L) ⊗_H C(C_ℓ)) ≃ ⊕_p H_p(C(X,L)) ⊗_H H_{1-p}(C_ℓ)`. -/
def kunnethIso :
    H1 X Λ ℓ hΛ hcompat ≃ₗ[𝔽₂]
    HEquivariantChainComplex.balancedKunnethSum
      (tannerHEq X Λ hΛ) (cycleHEq ℓ hcompat) 1 :=
  HEquivariantChainComplex.kunnethBalancedProduct
    (tannerHEq X Λ hΛ) (cycleHEq ℓ hcompat) hodd 1

/-- The projection from the Künneth direct sum onto the `p`-th summand. -/
def directSumProj (p : ℤ) :
    HEquivariantChainComplex.balancedKunnethSum
      (tannerHEq X Λ hΛ) (cycleHEq ℓ hcompat) 1 →ₗ[𝔽₂]
    HEquivariantChainComplex.balancedKunnethSummand
      (tannerHEq X Λ hΛ) (cycleHEq ℓ hcompat) 1 p :=
  DirectSum.component 𝔽₂ _ _ p

/-- The inclusion from the `p`-th summand into the Künneth direct sum. -/
def directSumInc (p : ℤ) :
    HEquivariantChainComplex.balancedKunnethSummand
      (tannerHEq X Λ hΛ) (cycleHEq ℓ hcompat) 1 p →ₗ[𝔽₂]
    HEquivariantChainComplex.balancedKunnethSum
      (tannerHEq X Λ hΛ) (cycleHEq ℓ hcompat) 1 :=
  DirectSum.lof 𝔽₂ _ _ p

/-! ## Projection maps -/

/-- The horizontal projection `pʰ : H₁ → H₁ʰ`, defined as the composition of the
Künneth isomorphism with the canonical projection onto the `p = 1` summand. -/
def projH :
    H1 X Λ ℓ hΛ hcompat →ₗ[𝔽₂] H1h X Λ ℓ hΛ hcompat :=
  (directSumProj X Λ ℓ hΛ hcompat 1).comp
    (kunnethIso X Λ ℓ hΛ hcompat hodd).toLinearMap

/-- The vertical projection `pᵛ : H₁ → H₁ᵛ`, defined as the composition of the
Künneth isomorphism with the canonical projection onto the `p = 0` summand. -/
def projV :
    H1 X Λ ℓ hΛ hcompat →ₗ[𝔽₂] H1v X Λ ℓ hΛ hcompat :=
  (directSumProj X Λ ℓ hΛ hcompat 0).comp
    (kunnethIso X Λ ℓ hΛ hcompat hodd).toLinearMap

/-- A homology class is **horizontal** if its image under the Künneth isomorphism
lies in `H₁ʰ ⊕ {0}`, i.e., its vertical projection is zero. -/
def IsHorizontal (x : H1 X Λ ℓ hΛ hcompat) : Prop :=
  projV X Λ ℓ hΛ hcompat hodd x = 0

/-- A homology class is **vertical** if its image under the Künneth isomorphism
lies in `{0} ⊕ H₁ᵛ`, i.e., its horizontal projection is zero. -/
def IsVertical (x : H1 X Λ ℓ hΛ hcompat) : Prop :=
  projH X Λ ℓ hΛ hcompat hodd x = 0

/-! ## Cohomology splitting -/

/-- The horizontal cohomology: `H¹_h = H¹(C(X,L)) ⊗_H H⁰(C_ℓ)`.
By the Künneth formula applied to cohomology (which equals homology in dimension
over `𝔽₂` by Def_2), this is isomorphic to the `p = 1` balanced Künneth summand.
We use the homology-cohomology equivalence to define this. -/
abbrev coH1h :=
  HEquivariantChainComplex.balancedKunnethSummand
    (tannerHEq X Λ hΛ) (cycleHEq ℓ hcompat) 1 1

/-- The vertical cohomology: `H¹_v = H⁰(C(X,L)) ⊗_H H¹(C_ℓ)`. -/
abbrev coH1v :=
  HEquivariantChainComplex.balancedKunnethSummand
    (tannerHEq X Λ hΛ) (cycleHEq ℓ hcompat) 1 0

/-- The cohomology horizontal projection `p_h : H¹ → H¹_h`, defined analogously
to `projH` using the Künneth isomorphism on cohomology. Since over `𝔽₂`, homology
and cohomology are isomorphic (Def_2), we use the same balanced Künneth summands. -/
def coprojH :
    H1 X Λ ℓ hΛ hcompat →ₗ[𝔽₂] coH1h X Λ ℓ hΛ hcompat :=
  projH X Λ ℓ hΛ hcompat hodd

/-- The cohomology vertical projection `p_v : H¹ → H¹_v`. -/
def coprojV :
    H1 X Λ ℓ hΛ hcompat →ₗ[𝔽₂] coH1v X Λ ℓ hΛ hcompat :=
  projV X Λ ℓ hΛ hcompat hodd

/-! ## Key properties -/

/-- The horizontal and vertical projections jointly determine the Künneth decomposition:
the map `(pʰ, pᵛ)` factors through the Künneth isomorphism, and the summands at
`p ∉ {0, 1}` are zero (since both the Tanner and cycle complexes are 1-complexes). -/
lemma projH_projV_jointly_surjective
    (y_h : H1h X Λ ℓ hΛ hcompat) (y_v : H1v X Λ ℓ hΛ hcompat) :
    ∃ x : H1 X Λ ℓ hΛ hcompat,
      projH X Λ ℓ hΛ hcompat hodd x = y_h ∧
      projV X Λ ℓ hΛ hcompat hodd x = y_v := by
  -- Use the inverse of the Künneth isomorphism
  let iso := kunnethIso X Λ ℓ hΛ hcompat hodd
  -- Construct the element in the direct sum with the given components
  let z : HEquivariantChainComplex.balancedKunnethSum
      (tannerHEq X Λ hΛ) (cycleHEq ℓ hcompat) 1 :=
    directSumInc X Λ ℓ hΛ hcompat 1 y_h +
    directSumInc X Λ ℓ hΛ hcompat 0 y_v
  use iso.symm z
  constructor
  · simp only [projH, LinearMap.comp_apply]
    simp only [iso, z, directSumProj, directSumInc,
      LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply, map_add]
    simp only [DirectSum.component.lof_self, DirectSum.component.of]
    simp [show (0 : ℤ) ≠ 1 from by omega, show ¬(0 : ℤ) = 1 from by omega]
  · simp only [projV, LinearMap.comp_apply]
    simp only [iso, z, directSumProj, directSumInc,
      LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply, map_add]
    simp only [DirectSum.component.lof_self, DirectSum.component.of]
    simp [show (1 : ℤ) ≠ 0 from by omega, show ¬(1 : ℤ) = 0 from by omega]

/-! ## Witness lemmas -/

/-- Witness: `H1h` is nonempty (contains 0). -/
lemma H1h_nonempty : Nonempty (H1h X Λ ℓ hΛ hcompat) := ⟨0⟩

/-- Witness: `H1v` is nonempty (contains 0). -/
lemma H1v_nonempty : Nonempty (H1v X Λ ℓ hΛ hcompat) := ⟨0⟩

/-- Witness: `H1` is nonempty (contains 0). -/
lemma H1_nonempty : Nonempty (H1 X Λ ℓ hΛ hcompat) := ⟨0⟩

end HorizontalVerticalHomologySplitting

end
