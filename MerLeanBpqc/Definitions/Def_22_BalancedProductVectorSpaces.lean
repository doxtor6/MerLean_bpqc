import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import MerLeanBpqc.Remarks.Rem_1_BaseField

/-!
# Definition 22: Balanced Product of Vector Spaces

The **balanced product** `V ⊗_H W` of `𝔽₂[H]`-modules is defined as the coinvariants of the
diagonal `H`-action on `V ⊗ W`. In the paper's right-action convention `vh = ρ_V(h⁻¹)(v)`,
the balanced relation is `[vh ⊗ w] = [v ⊗ hw]`.

## Main Definitions
- `balancedProduct`: `V ⊗_H W` as coinvariants of `ρ_V ⊗ ρ_W`.
- `balancedProduct.mk`: quotient map `V ⊗ W → V ⊗_H W`.

## Main Results
- `balancedProduct.balanced`: `[ρ_V(h⁻¹)(v) ⊗ w] = [v ⊗ ρ_W(h)(w)]`.
- `balancedProductInvariantsEquiv`: `V ⊗_H W ≅ (V ⊗ W)^H` when `|H|` is odd.
- `balancedProductCoinvariantsEquiv`: `V ⊗_H 𝔽₂ ≅ V_H`.
-/

open scoped TensorProduct
open Representation

noncomputable section

universe u
variable {H : Type u} [Group H]
variable {V W : Type u} [AddCommGroup V] [Module 𝔽₂ V] [AddCommGroup W] [Module 𝔽₂ W]
variable (ρV : Representation 𝔽₂ H V) (ρW : Representation 𝔽₂ H W)

/-! ## The Balanced Product -/

/-- The balanced product `V ⊗_H W`, defined as the coinvariants of the diagonal
`H`-action `h · (v ⊗ w) = ρ_V(h)(v) ⊗ ρ_W(h)(w)` on `V ⊗ W`.
Equivalently, `V ⊗_{𝔽₂[H]} W` — the tensor product over the group algebra. -/
abbrev balancedProduct : Type u :=
  Coinvariants (ρV.tprod ρW)

namespace balancedProduct

/-- The quotient map `V ⊗ W → V ⊗_H W`. -/
def mk : V ⊗[𝔽₂] W →ₗ[𝔽₂] balancedProduct ρV ρW :=
  Coinvariants.mk (ρV.tprod ρW)

/-- `[ρ_V(h)(v) ⊗ ρ_W(h)(w)] = [v ⊗ w]` in `V ⊗_H W`. -/
theorem diagonal_balanced (h : H) (v : V) (w : W) :
    Coinvariants.mk (ρV.tprod ρW) ((ρV h) v ⊗ₜ[𝔽₂] (ρW h) w) =
    Coinvariants.mk (ρV.tprod ρW) (v ⊗ₜ[𝔽₂] w) := by
  rw [show (ρV h) v ⊗ₜ[𝔽₂] (ρW h) w = (ρV.tprod ρW) h (v ⊗ₜ[𝔽₂] w) from by
    simp [Representation.tprod_apply, TensorProduct.map_tmul]]
  exact Coinvariants.mk_self_apply _ h (v ⊗ₜ[𝔽₂] w)

/-- The paper's balancing relation: `[ρ_V(h⁻¹)(v) ⊗ w] = [v ⊗ ρ_W(h)(w)]`.
In right-action notation, this says `[vh ⊗ w] = [v ⊗ hw]`.
Proof: apply diagonal relation at `h` to `(ρ_V(h⁻¹)(v), w)`. -/
theorem balanced (h : H) (v : V) (w : W) :
    Coinvariants.mk (ρV.tprod ρW) ((ρV h⁻¹) v ⊗ₜ[𝔽₂] w) =
    Coinvariants.mk (ρV.tprod ρW) (v ⊗ₜ[𝔽₂] (ρW h) w) := by
  have := diagonal_balanced ρV ρW h ((ρV h⁻¹) v) w
  have hρ : (ρV h) ((ρV h⁻¹) v) = v := by
    have h1 : (ρV h * ρV h⁻¹) v = v := by
      rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rwa [Module.End.mul_apply] at h1
  rw [hρ] at this
  exact this.symm

/-- Equivalent: `[ρ_V(h)(v) ⊗ w] = [v ⊗ ρ_W(h⁻¹)(w)]`. -/
theorem balanced' (h : H) (v : V) (w : W) :
    Coinvariants.mk (ρV.tprod ρW) ((ρV h) v ⊗ₜ[𝔽₂] w) =
    Coinvariants.mk (ρV.tprod ρW) (v ⊗ₜ[𝔽₂] (ρW h⁻¹) w) := by
  have := balanced ρV ρW h⁻¹ v w
  simp only [inv_inv] at this
  exact this

/-- Extensionality for maps from `V ⊗_H W`. -/
theorem ext' {X : Type u} [AddCommGroup X] [Module 𝔽₂ X]
    (f g : Coinvariants (ρV.tprod ρW) →ₗ[𝔽₂] X)
    (h : ∀ v : V, ∀ w : W,
      f (Coinvariants.mk (ρV.tprod ρW) (v ⊗ₜ[𝔽₂] w)) =
      g (Coinvariants.mk (ρV.tprod ρW) (v ⊗ₜ[𝔽₂] w))) :
    f = g := by
  apply Coinvariants.hom_ext (ρ := ρV.tprod ρW)
  apply TensorProduct.ext'
  exact h

/-- The quotient map is surjective. -/
theorem mk_surjective : Function.Surjective (mk ρV ρW) :=
  Coinvariants.mk_surjective (ρV.tprod ρW)

end balancedProduct

/-! ## Isomorphism with Invariants (Odd Order Case) -/

section InvariantsEquiv

variable [Fintype H] [Invertible (Fintype.card H : 𝔽₂)]

/-- The averaging map kills the coinvariant kernel. -/
private lemma averageMap_mem_ker (x : V ⊗[𝔽₂] W)
    (hx : x ∈ Coinvariants.ker (ρV.tprod ρW)) :
    averageMap (ρV.tprod ρW) x = 0 := by
  refine Submodule.span_induction
    (p := fun y _ => averageMap (ρV.tprod ρW) y = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨⟨g, v⟩, rfl⟩
    simp only [map_sub, sub_eq_zero]
    rw [averageMap, ← asAlgebraHom_single_one (ρV.tprod ρW) g,
      ← Module.End.mul_apply, ← map_mul (asAlgebraHom (ρV.tprod ρW)),
      GroupAlgebra.mul_average_right]
  · simp
  · intro a b _ _ ha hb
    rw [map_add, ha, hb, add_zero]
  · intro c a _ ha
    rw [map_smul, ha, smul_zero]

/-- `avg(x) - x ∈ ker` for all `x`, so `[avg(x)] = [x]` in coinvariants. -/
private lemma averageMap_sub_mem_ker (x : V ⊗[𝔽₂] W) :
    averageMap (ρV.tprod ρW) x - x ∈ Coinvariants.ker (ρV.tprod ρW) := by
  have key : Coinvariants.mk (ρV.tprod ρW) (averageMap (ρV.tprod ρW) x) =
    Coinvariants.mk (ρV.tprod ρW) x := by
    rw [averageMap, GroupAlgebra.average]
    simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply]
    have hg : ∀ g : H, asAlgebraHom (ρV.tprod ρW) (MonoidAlgebra.of 𝔽₂ H g) x =
      (ρV.tprod ρW) g x := fun g => by
      rw [← asAlgebraHom_single_one, MonoidAlgebra.of_apply]
    simp_rw [hg, Coinvariants.mk_self_apply, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul 𝔽₂, smul_smul, invOf_mul_self, one_smul]
  rwa [Coinvariants.mk_eq_iff] at key

/-- The descended averaging map: `V ⊗_H W → (V ⊗ W)^H`. -/
def avgDescended :
    balancedProduct ρV ρW →ₗ[𝔽₂] ↥(ρV.tprod ρW).invariants :=
  (Coinvariants.ker (ρV.tprod ρW)).liftQ
    ((averageMap (ρV.tprod ρW)).codRestrict _ (averageMap_invariant _))
    (by
      intro x hx
      simp only [LinearMap.mem_ker, LinearMap.codRestrict_apply, Subtype.mk.injEq]
      ext
      exact averageMap_mem_ker ρV ρW x hx)

/-- The inclusion map: `(V ⊗ W)^H → V ⊗_H W`. -/
def invToBalanced :
    ↥(ρV.tprod ρW).invariants →ₗ[𝔽₂] balancedProduct ρV ρW :=
  (Coinvariants.mk (ρV.tprod ρW)).comp (Submodule.subtype _)

/-- When `H` is finite of odd order, `V ⊗_H W ≅ (V ⊗ W)^H`.

The forward map sends `[v ⊗ w] ↦ (1/|H|) ∑_h ρ_V(h)(v) ⊗ ρ_W(h)(w)`.
The inverse is the composition of the inclusion and the quotient map. -/
noncomputable def balancedProductInvariantsEquiv :
    balancedProduct ρV ρW ≃ₗ[𝔽₂] ↥(ρV.tprod ρW).invariants where
  toFun := avgDescended ρV ρW
  invFun := invToBalanced ρV ρW
  left_inv := by
    intro x
    induction x using Coinvariants.induction_on with
    | h v =>
      simp only [avgDescended, invToBalanced, LinearMap.coe_comp, Function.comp_apply,
        Submodule.liftQ_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply]
      rw [Coinvariants.mk_eq_iff]
      exact averageMap_sub_mem_ker ρV ρW v
  right_inv := by
    intro ⟨v, hv⟩
    simp only [invToBalanced, LinearMap.coe_comp, Function.comp_apply,
      Submodule.subtype_apply, avgDescended, Submodule.liftQ_apply,
      LinearMap.codRestrict_apply]
    ext
    exact averageMap_id _ v hv
  map_add' := (avgDescended ρV ρW).map_add
  map_smul' := (avgDescended ρV ρW).map_smul

end InvariantsEquiv

/-! ## Coinvariants Specialization -/

section CoinvariantsEquiv

/-- The diagonal action `ρ_V ⊗ trivial` on `V ⊗ 𝔽₂` has kernel (for coinvariants)
that corresponds to the kernel of `ρ_V` under `TensorProduct.rid : V ⊗ 𝔽₂ ≅ V`. -/
private lemma tprod_trivial_ker_map :
    (Coinvariants.ker (ρV.tprod (Representation.trivial 𝔽₂ H 𝔽₂))).map
      (TensorProduct.rid 𝔽₂ V).toLinearMap =
    Coinvariants.ker ρV := by
  -- Both kernels are spanned by `ρ(g)(x) - x` for g ∈ H
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro x hx
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe]
    refine Submodule.span_induction
      (p := fun y _ => (TensorProduct.rid 𝔽₂ V) y ∈ Coinvariants.ker ρV) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨⟨g, t⟩, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul v a =>
        simp only [Representation.tprod_apply, TensorProduct.map_tmul,
          Representation.trivial, MonoidHom.one_apply,
          map_sub, TensorProduct.rid_tmul]
        show (1 : Module.End 𝔽₂ 𝔽₂) a • (ρV g) v - a • v ∈ _
        rw [Module.End.one_apply]
        rw [show a • (ρV g) v - a • v = a • ((ρV g) v - v) from by rw [smul_sub]]
        exact Submodule.smul_mem _ a (Coinvariants.sub_mem_ker g v)
      | add x y ihx ihy =>
        simp only [map_add, map_sub] at ihx ihy ⊢
        have key : (TensorProduct.rid 𝔽₂ V) (((ρV.tprod (Representation.trivial 𝔽₂ H 𝔽₂)) g) x) +
          (TensorProduct.rid 𝔽₂ V) (((ρV.tprod (Representation.trivial 𝔽₂ H 𝔽₂)) g) y) -
          ((TensorProduct.rid 𝔽₂ V) x + (TensorProduct.rid 𝔽₂ V) y) =
          ((TensorProduct.rid 𝔽₂ V) (((ρV.tprod (Representation.trivial 𝔽₂ H 𝔽₂)) g) x) -
            (TensorProduct.rid 𝔽₂ V) x) +
          ((TensorProduct.rid 𝔽₂ V) (((ρV.tprod (Representation.trivial 𝔽₂ H 𝔽₂)) g) y) -
            (TensorProduct.rid 𝔽₂ V) y) := by abel
        rw [key]
        exact Submodule.add_mem _ ihx ihy
    · simp
    · intro _ _ _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
    · intro c _ _ ha; rw [map_smul]; exact Submodule.smul_mem _ c ha
  · intro v hv
    rw [Submodule.mem_map]
    refine Submodule.span_induction
      (p := fun y _ => y ∈ Submodule.map (TensorProduct.rid 𝔽₂ V).toLinearMap
        (Coinvariants.ker (ρV.tprod (Representation.trivial 𝔽₂ H 𝔽₂)))) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨⟨g, v'⟩, rfl⟩
      rw [Submodule.mem_map]
      exact ⟨ρV g v' ⊗ₜ (1 : 𝔽₂) - v' ⊗ₜ 1,
        Submodule.subset_span ⟨(g, v' ⊗ₜ 1), by
          simp [Representation.tprod, Representation.trivial]⟩,
        by simp [TensorProduct.rid_tmul]⟩
    · show 0 ∈ Submodule.map _ _
      rw [Submodule.mem_map]; exact ⟨0, Submodule.zero_mem _, map_zero _⟩
    · intro _ _ _ _ ha hb
      show _ + _ ∈ Submodule.map _ _
      change _ ∈ Submodule.map _ _ at ha
      change _ ∈ Submodule.map _ _ at hb
      rw [Submodule.mem_map] at ha hb ⊢
      obtain ⟨a, ha, rfl⟩ := ha; obtain ⟨b, hb, rfl⟩ := hb
      exact ⟨a + b, Submodule.add_mem _ ha hb, map_add _ a b⟩
    · intro c _ _ ha
      show _ • _ ∈ Submodule.map _ _
      change _ ∈ Submodule.map _ _ at ha
      rw [Submodule.mem_map] at ha ⊢
      obtain ⟨a, ha, rfl⟩ := ha
      exact ⟨c • a, Submodule.smul_mem _ c ha, map_smul _ c a⟩

/-- `V ⊗_H 𝔽₂ ≅ V_H` when `𝔽₂` has trivial `H`-action.
This identifies `(V ⊗ 𝔽₂)/⟨ρ_V(h)(v) ⊗ a - v ⊗ a⟩ ≅ V/⟨ρ_V(h)(v) - v⟩`
via `TensorProduct.rid : V ⊗ 𝔽₂ ≅ V`. -/
def balancedProductCoinvariantsEquiv :
    Coinvariants (ρV.tprod (Representation.trivial 𝔽₂ H 𝔽₂)) ≃ₗ[𝔽₂]
    Coinvariants ρV :=
  Submodule.Quotient.equiv
    (Coinvariants.ker (ρV.tprod (Representation.trivial 𝔽₂ H 𝔽₂)))
    (Coinvariants.ker ρV)
    (TensorProduct.rid 𝔽₂ V)
    (tprod_trivial_ker_map ρV)

end CoinvariantsEquiv

/-! ## Witness -/

/-- The balanced product contains 0. -/
lemma balancedProduct_nonempty : Nonempty (balancedProduct ρV ρW) :=
  ⟨0⟩

end
