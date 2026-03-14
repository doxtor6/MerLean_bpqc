import MerLeanBpqc.Definitions.Def_28_IotaPiMaps

/-!
# Theorem 12: Encoding Rate (Circle Case)

The horizontal part of the balanced product Tanner cycle code has dimension equal to
the dimension of the quotient Tanner code homology:
  `dim H₁ʰ(C(X,L) ⊗_{ℤ_ℓ} C(C_ℓ)) = dim H₁(C(X/H, L))`

This follows from the linear isomorphism `ι : H₁(C(X/H, L)) ≃ H₁ʰ` constructed
in Def_28 (the `iotaEquiv`), which preserves dimension.

## Main Results
- `encodingRateCircle` — the dimension equality
- `encodingRateCircle_satisfiable` — witness that the premises are satisfiable
-/

open CategoryTheory
open scoped TensorProduct DirectSum

noncomputable section

namespace EncodingRateCircle

variable {H : Type} [Group H] [Fintype H] [DecidableEq H]
variable (X : GraphWithGroupAction H)
variable {s : ℕ} (Λ : X.CellLabeling s)
variable (ℓ : ℕ) [NeZero ℓ] [MulAction H (Fin ℓ)]
variable (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
variable (hcompat : BalancedProductTannerCycleCode.CycleCompatibleAction (H := H) ℓ)

/-- **Encoding Rate (Circle Case).** The horizontal homology of the balanced product
Tanner cycle code has the same dimension as the quotient Tanner code homology:
  `dim H₁ʰ(C(X,L) ⊗_{ℤ_ℓ} C(C_ℓ)) = dim H₁(C(X/H, L))`

The proof uses the linear isomorphism `iotaEquiv` from Def_28, which gives
`H₁(C(X/H, L)) ≃ₗ[𝔽₂] H₁ʰ`. Since linear equivalences preserve `finrank`,
we obtain the dimension equality. -/
theorem encodingRateCircle
    (hℓ_odd : ℓ % 2 = 1) (hodd : Odd (Fintype.card H)) :
    Module.finrank 𝔽₂ (HorizontalVerticalHomologySplitting.H1h X Λ ℓ hΛ hcompat) =
    Module.finrank 𝔽₂ (IotaPiMaps.quotientTannerHomology X Λ hΛ) := by
  exact (LinearEquiv.finrank_eq (IotaPiMaps.iotaEquiv X Λ ℓ hΛ hcompat hℓ_odd hodd)).symm

/-- Witness: the premises of `encodingRateCircle` are satisfiable.
Follows from `piMap_comp_iotaMap_satisfiable` in Def_28. -/
lemma encodingRateCircle_satisfiable :
    ∃ (H : Type) (_ : Group H) (_ : Fintype H) (_ : DecidableEq H)
      (X : GraphWithGroupAction H) (s : ℕ) (Λ : X.CellLabeling s)
      (ℓ : ℕ) (_ : NeZero ℓ) (_ : MulAction H (Fin ℓ))
      (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
      (hcompat : BalancedProductTannerCycleCode.CycleCompatibleAction (H := H) ℓ)
      (_ : ℓ % 2 = 1) (_ : Odd (Fintype.card H)),
      True := by
  obtain ⟨H, hG, hF, hD, X, s, Λ, ℓ, hNZ, hMA, hΛ, hcompat, _, hℓ_odd, hodd, _⟩ :=
    IotaPiMaps.piMap_comp_iotaMap_satisfiable
  exact ⟨H, hG, hF, hD, X, s, Λ, ℓ, hNZ, hMA, hΛ, hcompat, hℓ_odd, hodd, trivial⟩

end EncodingRateCircle

end
