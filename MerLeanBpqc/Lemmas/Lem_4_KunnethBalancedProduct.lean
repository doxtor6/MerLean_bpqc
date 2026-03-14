import MerLeanBpqc.Definitions.Def_23_BalancedProductChainComplex
import MerLeanBpqc.Definitions.Def_22_BalancedProductVectorSpaces
import MerLeanBpqc.Definitions.Def_1_ChainComplex
import MerLeanBpqc.Theorems.Thm_1_KunnethFormula
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Lemma 4: Künneth Formula for Balanced Products

Let `H` be a finite group of odd order, and let `C`, `D` be `H`-equivariant chain complexes
over `𝔽₂`. Then there is an isomorphism
$$H_n(C \otimes_H D) \cong \bigoplus_{p+q=n} H_p(C) \otimes_H H_q(D)$$

The proof uses:
1. Over `𝔽₂` with `|H|` odd, coinvariants `(-)_H` is an exact functor
2. Exactness means coinvariants commutes with homology
3. The ordinary Künneth formula (Thm_1) gives `H_n(C ⊗ D) ≅ ⊕ H_p(C) ⊗ H_q(D)`
4. Applying coinvariants: `H_n(C ⊗_H D) ≅ ⊕ H_p(C) ⊗_H H_q(D)`

## Main Definitions
- `homologyAction`: the induced `H`-action on `H_p(C)`
- `balancedKunnethSummand`: `H_p(C) ⊗_H H_q(D)`
- `balancedKunnethSum`: `⊕_{p+q=n} H_p(C) ⊗_H H_q(D)`

## Main Results
- `kunnethBalancedProduct`: the isomorphism `H_n(C ⊗_H D) ≃ₗ[𝔽₂] ⊕ H_p(C) ⊗_H H_q(D)`
-/

open scoped TensorProduct DirectSum
open Representation CategoryTheory

noncomputable section

universe u

namespace HEquivariantChainComplex

variable {H : Type u} [Group H] [Fintype H]
variable (C D : HEquivariantChainComplex H)

/-! ## Induced H-action on homology

Since the differentials are `H`-equivariant, `H` acts on cycles `Z_p = ker ∂_p`
and boundaries `B_p = im ∂_{p+1}`. The induced action on `H_p(C) = Z_p / B_p`
is well-defined. -/

/-- `H` acts on cycles `Z_p(C) = ker ∂_p`, since `∂(h · z) = h · ∂(z) = h · 0 = 0`
for `z ∈ ker ∂`. -/
def cyclesAction (p : ℤ) : Representation 𝔽₂ H ↥(C.complex.cycles p) where
  toFun h := {
    toFun := fun ⟨z, hz⟩ => by
      refine ⟨(C.action p h) z, ?_⟩
      rw [ChainComplex𝔽₂.cycles, LinearMap.mem_ker] at hz ⊢
      -- hz : C.complex.differential p z = 0
      -- goal : C.complex.differential p ((C.action p h) z) = 0
      unfold ChainComplex𝔽₂.differential at hz ⊢
      have heq := C.equivariant p (p - 1) h
      have hfun := LinearMap.congr_fun heq z
      simp only [LinearMap.comp_apply] at hfun
      rw [hfun, hz, map_zero]
    map_add' := fun ⟨a, _⟩ ⟨b, _⟩ => by
      ext; simp [map_add]
    map_smul' := fun r ⟨a, _⟩ => by
      ext; simp only [SetLike.mk_smul_mk, map_smul, RingHom.id_apply]
  }
  map_one' := by
    ext ⟨z, hz⟩
    show ((C.action p 1) z : ↥(C.complex.X p)) = z
    exact congr_fun (congr_arg DFunLike.coe (map_one (C.action p))) z
  map_mul' g₁ g₂ := by
    ext ⟨z, hz⟩
    show ((C.action p (g₁ * g₂)) z : ↥(C.complex.X p)) =
      (C.action p g₁) ((C.action p g₂) z)
    exact congr_fun (congr_arg DFunLike.coe (map_mul (C.action p) g₁ g₂)) z

/-- `H` acts on boundaries `B_p(C) = im ∂_{p+1}`, since for `b = ∂(x)`,
`h · b = h · ∂(x) = ∂(h · x) ∈ im ∂`. -/
def boundariesAction (p : ℤ) : Representation 𝔽₂ H ↥(C.complex.boundaries p) where
  toFun h := {
    toFun := fun ⟨b, hb⟩ => by
      refine ⟨(C.action p h) b, ?_⟩
      rw [ChainComplex𝔽₂.boundaries, LinearMap.mem_range] at hb ⊢
      unfold ChainComplex𝔽₂.incomingDifferential at hb ⊢
      obtain ⟨x, hx⟩ := hb
      exact ⟨(C.action (p + 1) h) x, by
        have heq := C.equivariant (p + 1) p h
        have hfun := LinearMap.congr_fun heq x
        simp only [LinearMap.comp_apply] at hfun
        rw [← hx, hfun]⟩
    map_add' := fun ⟨a, _⟩ ⟨b, _⟩ => by
      ext; simp [map_add]
    map_smul' := fun r ⟨a, _⟩ => by
      ext; simp only [SetLike.mk_smul_mk, map_smul, RingHom.id_apply]
  }
  map_one' := by
    ext ⟨z, hz⟩
    show ((C.action p 1) z : ↥(C.complex.X p)) = z
    exact congr_fun (congr_arg DFunLike.coe (map_one (C.action p))) z
  map_mul' g₁ g₂ := by
    ext ⟨z, hz⟩
    show ((C.action p (g₁ * g₂)) z : ↥(C.complex.X p)) =
      (C.action p g₁) ((C.action p g₂) z)
    exact congr_fun (congr_arg DFunLike.coe (map_mul (C.action p) g₁ g₂)) z

/-- The boundaries submodule of cycles inherits an `H`-action from `cyclesAction`,
compatible with the inclusion. -/
def boundariesSubCyclesAction (p : ℤ) :
    Representation 𝔽₂ H ↥(C.complex.boundariesSubCycles p) where
  toFun h := {
    toFun := fun ⟨⟨z, hzc⟩, hzb⟩ => by
      refine ⟨⟨(C.action p h) z, ?_⟩, ?_⟩
      · -- z is a cycle, so h·z is a cycle
        exact ((C.cyclesAction p h) ⟨z, hzc⟩).2
      · -- z is a boundary, so h·z is a boundary
        simp only [ChainComplex𝔽₂.boundariesSubCycles, Submodule.mem_comap] at hzb ⊢
        exact ((C.boundariesAction p h) ⟨z, hzb⟩).2
    map_add' := fun ⟨⟨a, _⟩, _⟩ ⟨⟨b, _⟩, _⟩ => by
      ext; simp [map_add]
    map_smul' := fun r ⟨⟨a, _⟩, _⟩ => by
      ext; simp only [SetLike.mk_smul_mk, map_smul, RingHom.id_apply]
  }
  map_one' := by
    ext ⟨⟨z, _⟩, _⟩
    show ((C.action p 1) z : ↥(C.complex.X p)) = z
    exact congr_fun (congr_arg DFunLike.coe (map_one (C.action p))) z
  map_mul' g₁ g₂ := by
    ext ⟨⟨z, _⟩, _⟩
    show ((C.action p (g₁ * g₂)) z : ↥(C.complex.X p)) =
      (C.action p g₁) ((C.action p g₂) z)
    exact congr_fun (congr_arg DFunLike.coe (map_mul (C.action p) g₁ g₂)) z

/-- The induced `H`-action on homology `H_p(C) = Z_p / B_p`.
Since `H` acts on both `Z_p` and `B_p` compatibly, the quotient action is well-defined. -/
def homologyAction (p : ℤ) : Representation 𝔽₂ H (C.complex.homology' p) where
  toFun h :=
    (C.complex.boundariesSubCycles p).mapQ
      (C.complex.boundariesSubCycles p)
      (C.cyclesAction p h)
      (fun ⟨z, hz⟩ hzb => by
        show C.cyclesAction p h ⟨z, hz⟩ ∈ C.complex.boundariesSubCycles p
        have : ⟨z, hz⟩ ∈ C.complex.boundariesSubCycles p := hzb
        simp only [ChainComplex𝔽₂.boundariesSubCycles, Submodule.mem_comap] at this ⊢
        exact ((C.boundariesAction p h) ⟨z, this⟩).2)
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [Submodule.mapQ_apply, Module.End.one_apply]
    congr 1; ext
    exact congr_fun (congr_arg DFunLike.coe (map_one (C.action p))) z.1
  map_mul' g₁ g₂ := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [Submodule.mapQ_apply, Module.End.mul_apply]
    congr 1; ext
    exact congr_fun (congr_arg DFunLike.coe (map_mul (C.action p) g₁ g₂)) z.1

/-! ## Balanced Künneth summands -/

/-- The summand of the balanced Künneth decomposition at index `p`:
`H_p(C) ⊗_H H_{n-p}(D)`, the balanced product of homology groups.
Defined as coinvariants of the tensor product representation, which avoids
universe constraints of the `balancedProduct` abbreviation. -/
abbrev balancedKunnethSummand (n p : ℤ) :=
  Coinvariants ((C.homologyAction p).tprod (D.homologyAction (n - p)))

instance balancedKunnethSummand_addCommGroup (n p : ℤ) :
    AddCommGroup (balancedKunnethSummand C D n p) :=
  inferInstance

instance balancedKunnethSummand_module (n p : ℤ) :
    Module 𝔽₂ (balancedKunnethSummand C D n p) :=
  inferInstance

/-- The balanced Künneth direct sum `⊕_{p : ℤ} H_p(C) ⊗_H H_{n-p}(D)`. -/
abbrev balancedKunnethSum (n : ℤ) :=
  ⨁ (p : ℤ), balancedKunnethSummand C D n p

instance balancedKunnethSum_addCommGroup (n : ℤ) :
    AddCommGroup (balancedKunnethSum C D n) :=
  DirectSum.instAddCommGroup _

instance balancedKunnethSum_module (n : ℤ) :
    Module 𝔽₂ (balancedKunnethSum C D n) :=
  DirectSum.instModule

/-! ## Exactness of coinvariants in characteristic 2 with odd order group

Over `𝔽₂` with `H` of odd order, `|H| = 1` in `𝔽₂`, so the averaging map
`a(v) = ∑_h h·v` is an idempotent splitting: `V = V^H ⊕ ker(a)`.
This makes `(-)_H ≅ (-)^H` an exact functor.
-/

/-- The cardinality of `H` is invertible in `𝔽₂` when `|H|` is odd. -/
def invertible_card_of_odd_order (hodd : Odd (Fintype.card H)) :
    Invertible (Fintype.card H : 𝔽₂) := by
  have : (Fintype.card H : 𝔽₂) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have : (2 : 𝔽₂) = 0 := by decide
    rw [this, zero_mul, zero_add, Nat.cast_one]
  rw [this]
  exact invertibleOne

/-! ## Main theorem: Künneth formula for balanced products -/

/-- **Künneth Formula for Balanced Products (Lemma 4).**

For `H` a finite group of odd order and `C`, `D` `H`-equivariant chain complexes over `𝔽₂`,
$$H_n(C \otimes_H D) \cong \bigoplus_{p+q=n} H_p(C) \otimes_H H_q(D).$$

The proof proceeds as follows:
1. Over `𝔽₂` with `|H|` odd, `|H| = 1` in `𝔽₂`, so the averaging map `a = ∑_h ρ(h)`
   is an idempotent with `im(a) = V^H`. This gives `V = V^H ⊕ ker(a)`, making
   coinvariants `(-)_H ≅ (-)^H` an exact functor (Def_22, `balancedProductInvariantsEquiv`).
2. Since `(-)_H` is exact, it commutes with homology:
   `H_n((C ⊗ D)_H) ≅ (H_n(C ⊗ D))_H`.
3. By the Künneth formula (Thm_1): `H_n(C ⊗ D) ≅ ⊕_{p+q=n} H_p(C) ⊗ H_q(D)`.
4. Taking coinvariants and using `(-)_H` commutes with finite direct sums:
   `(H_n(C ⊗ D))_H ≅ ⊕_{p+q=n} (H_p(C) ⊗ H_q(D))_H = ⊕_{p+q=n} H_p(C) ⊗_H H_q(D)`.

Accepted as axiom: the full proof requires showing that the balanced product complex
`C ⊗_H D` equals the coinvariants of the tensor product complex `(C ⊗ D)_H` at the
chain complex level (connecting `totalComplex` from Def_10 with `balancedProductComplex`
from Def_23), and then constructing the chain of isomorphisms through exact functor
arguments. This infrastructure for coinvariant-homology interchange and for connecting
the two total complex constructions is not available in Mathlib. -/
axiom kunnethBalancedProduct (hodd : Odd (Fintype.card H)) (n : ℤ) :
    (C.balancedProductComplex D).homology' n ≃ₗ[𝔽₂] balancedKunnethSum C D n

/-! ## Satisfiability witnesses -/

/-- Witness: the premises of `kunnethBalancedProduct` are satisfiable.
The trivial group `H = Unit` has odd order `|H| = 1`, and any chain complexes
(e.g., the zero complex) are equivariant. -/
lemma kunnethBalancedProduct_satisfiable :
    ∃ (H : Type) (_ : Group H) (_ : Fintype H),
    ∃ (C D : HEquivariantChainComplex.{0, 0} H),
    Odd (@Fintype.card H _) := by
  refine ⟨Unit, inferInstance, inferInstance, ?_⟩
  -- Construct trivial H-equivariant chain complexes
  let zeroComplex : ChainComplex𝔽₂ :=
    (HomologicalComplex.single (ModuleCat 𝔽₂) (ComplexShape.down ℤ) 0).obj (ModuleCat.of 𝔽₂ 𝔽₂)
  let trivAction : ∀ (i : ℤ), Representation 𝔽₂ Unit ↥(zeroComplex.X i) :=
    fun i => Representation.trivial 𝔽₂ Unit _
  let C : @HEquivariantChainComplex Unit _ := {
    complex := zeroComplex
    action := trivAction
    equivariant := fun i j h => by
      ext x; simp [trivAction, Representation.trivial]
  }
  exact ⟨C, C, odd_one⟩

/-- Witness: the balanced Künneth summand is nonempty (contains 0). -/
lemma balancedKunnethSummand_nonempty (n p : ℤ) :
    Nonempty (balancedKunnethSummand C D n p) := ⟨0⟩

/-- Witness: the balanced Künneth sum is nonempty (contains 0). -/
lemma balancedKunnethSum_nonempty (n : ℤ) :
    Nonempty (balancedKunnethSum C D n) := ⟨0⟩

end HEquivariantChainComplex

end
