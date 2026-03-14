import MerLeanBpqc.Definitions.Def_22_BalancedProductVectorSpaces
import MerLeanBpqc.Definitions.Def_10_TotalComplex
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Definition 23: Balanced Product Chain Complex

Given a group `H`, chain complexes `C` and `D` with `H`-equivariant differentials (where each
`C_i` carries a right `H`-action and each `D_j` carries a left `H`-action), the **balanced
product double complex** `C ⊠_H D` has objects `(C ⊠_H D)_{p,q} = C_p ⊗_H D_q` (Def_22)
with differentials:
- horizontal `∂^h = ∂^C ⊗_H id_D` (changes `p`, keeps `q`)
- vertical `∂^v = id_C ⊗_H ∂^D` (changes `q`, keeps `p`)

These satisfy the double complex  (Def_9) because `(∂^C)² = 0`, `(∂^D)² = 0`,
and `∂^C ⊗ ∂^D = ∂^C ⊗ ∂^D` (commutativity).

The **balanced product complex** is `C ⊗_H D = Tot(C ⊠_H D)` (Def_10).

## Main Definitions
- `HEquivariantChainComplex`: chain complex with `H`-action and equivariant differentials
- `balancedProductDoubleComplex`: the double complex `C ⊠_H D`
- `balancedProductComplex`: the total complex `C ⊗_H D = Tot(C ⊠_H D)`

## Main Results
- Double complex : `(∂^h)² = 0`, `(∂^v)² = 0`, `∂^h ∘ ∂^v = ∂^v ∘ ∂^h`
-/

open scoped TensorProduct
open Representation CategoryTheory

noncomputable section

universe u

/-! ## H-Equivariant Chain Complexes -/

/-- A chain complex with `H`-action on each degree, where differentials are `H`-equivariant:
`∂(h · x) = h · ∂(x)` for all `x ∈ C_i, h ∈ H`. -/
structure HEquivariantChainComplex (H : Type u) [Group H] where
  /-- The underlying chain complex over `𝔽₂`. -/
  complex : ChainComplex𝔽₂
  /-- The `H`-action on each degree. -/
  action : ∀ (i : ℤ), Representation 𝔽₂ H ↥(complex.X i)
  /-- The differentials commute with the `H`-action. -/
  equivariant : ∀ (i j : ℤ) (h : H),
    (complex.d i j).hom ∘ₗ (action i h) = (action j h) ∘ₗ (complex.d i j).hom

namespace HEquivariantChainComplex

variable {H : Type u} [Group H]
variable (C D : HEquivariantChainComplex H)

/-! ## Balanced Product Objects -/

/-- The balanced product object at `(p, q)`: `C_p ⊗_H D_q`. -/
def bpObj (p q : ℤ) : ModuleCat 𝔽₂ :=
  ModuleCat.of 𝔽₂ (balancedProduct (C.action p) (D.action q))

/-! ## Equivariance lemmas for tensor product maps -/

private lemma equivariant_map_dC_id (p p' q : ℤ) (h : H) :
    TensorProduct.map (C.complex.d p p').hom LinearMap.id ∘ₗ
      ((C.action p).tprod (D.action q)) h =
    ((C.action p').tprod (D.action q)) h ∘ₗ
      TensorProduct.map (C.complex.d p p').hom LinearMap.id := by
  apply TensorProduct.ext'
  intro v w
  simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
    LinearMap.id_apply]
  have heq := C.equivariant p p' h
  have := LinearMap.congr_fun heq v
  simp only [LinearMap.comp_apply] at this
  rw [this]

private lemma equivariant_map_id_dD (p q q' : ℤ) (h : H) :
    TensorProduct.map LinearMap.id (D.complex.d q q').hom ∘ₗ
      ((C.action p).tprod (D.action q)) h =
    ((C.action p).tprod (D.action q')) h ∘ₗ
      TensorProduct.map LinearMap.id (D.complex.d q q').hom := by
  apply TensorProduct.ext'
  intro v w
  simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
    LinearMap.id_apply]
  have heq := D.equivariant q q' h
  have := LinearMap.congr_fun heq w
  simp only [LinearMap.comp_apply] at this
  rw [this]

/-! ## Balanced Product Differentials -/

/-- The horizontal differential `∂^C ⊗_H id_D : C_p ⊗_H D_q → C_{p'} ⊗_H D_q`.
Well-defined on the balanced product by `H`-equivariance of `∂^C`. -/
def bpDh (p p' q : ℤ) : C.bpObj D p q ⟶ C.bpObj D p' q :=
  ModuleCat.ofHom (Coinvariants.map _ _
    (TensorProduct.map (C.complex.d p p').hom LinearMap.id)
    (fun h => C.equivariant_map_dC_id D p p' q h))

/-- The vertical differential `id_C ⊗_H ∂^D : C_p ⊗_H D_q → C_p ⊗_H D_{q'}`.
Well-defined on the balanced product by `H`-equivariance of `∂^D`. -/
def bpDv (p q q' : ℤ) : C.bpObj D p q ⟶ C.bpObj D p q' :=
  ModuleCat.ofHom (Coinvariants.map _ _
    (TensorProduct.map LinearMap.id (D.complex.d q q').hom)
    (fun h => C.equivariant_map_id_dD D p q q' h))

/-! ## Shape conditions -/

private lemma bpDh_shape (p p' : ℤ) (hp : ¬(ComplexShape.down ℤ).Rel p p') (q : ℤ) :
    C.bpDh D p p' q = 0 := by
  have hd : C.complex.d p p' = 0 := C.complex.shape p p' hp
  simp only [bpDh]
  apply ModuleCat.hom_ext
  apply Coinvariants.hom_ext
  ext v w
  simp [TensorProduct.map_tmul, hd, ModuleCat.hom_zero]

private lemma bpDv_shape (p : ℤ) (q q' : ℤ) (hq : ¬(ComplexShape.down ℤ).Rel q q') :
    C.bpDv D p q q' = 0 := by
  have hd : D.complex.d q q' = 0 := D.complex.shape q q' hq
  simp only [bpDv]
  apply ModuleCat.hom_ext
  apply Coinvariants.hom_ext
  ext v w
  simp [TensorProduct.map_tmul, hd, ModuleCat.hom_zero]

/-! ## d² = 0 conditions -/

private lemma bpDh_comp (p p' p'' q : ℤ) :
    C.bpDh D p p' q ≫ C.bpDh D p' p'' q = 0 := by
  simp only [bpDh]
  have hd : C.complex.d p p' ≫ C.complex.d p' p'' = 0 := C.complex.d_comp_d p p' p''
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
  rw [Coinvariants.map_comp]
  apply Coinvariants.hom_ext
  apply TensorProduct.ext'
  intro v w
  simp only [Coinvariants.map_mk, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearMap.zero_apply]
  have hcomp : (C.complex.d p' p'').hom.comp (C.complex.d p p').hom = 0 := by
    have h := congr_arg ModuleCat.Hom.hom hd
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact h
  have hv : (C.complex.d p' p'').hom ((C.complex.d p p').hom v) = 0 :=
    LinearMap.congr_fun hcomp v
  rw [hv, TensorProduct.zero_tmul, map_zero]
  rfl

private lemma bpDv_comp (p q q' q'' : ℤ) :
    C.bpDv D p q q' ≫ C.bpDv D p q' q'' = 0 := by
  simp only [bpDv]
  have hd : D.complex.d q q' ≫ D.complex.d q' q'' = 0 := D.complex.d_comp_d q q' q''
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
  rw [Coinvariants.map_comp]
  apply Coinvariants.hom_ext
  apply TensorProduct.ext'
  intro v w
  simp only [Coinvariants.map_mk, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearMap.zero_apply]
  have hcomp : (D.complex.d q' q'').hom.comp (D.complex.d q q').hom = 0 := by
    have h := congr_arg ModuleCat.Hom.hom hd
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact h
  have hw : (D.complex.d q' q'').hom ((D.complex.d q q').hom w) = 0 :=
    LinearMap.congr_fun hcomp w
  rw [hw, TensorProduct.tmul_zero, map_zero]
  rfl

/-! ## Commutativity: ∂^h ∘ ∂^v = ∂^v ∘ ∂^h -/

private lemma bpDh_comm_bpDv (p p' q q' : ℤ) :
    C.bpDh D p p' q ≫ C.bpDv D p' q q' =
    C.bpDv D p q q' ≫ C.bpDh D p p' q' := by
  apply ModuleCat.hom_ext
  simp only [bpDh, bpDv, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
  rw [Coinvariants.map_comp, Coinvariants.map_comp]
  congr 1
  apply TensorProduct.ext'
  intro v w
  simp [TensorProduct.map_tmul]

/-! ## The Balanced Product Double Complex -/

/-- The balanced product double complex `C ⊠_H D` as a `DoubleComplex𝔽₂`.
Objects are `(C ⊠_H D)_{p,q} = C_p ⊗_H D_q` with:
- horizontal differential `∂^h = ∂^C ⊗_H id_D` (changes `p`)
- vertical differential `∂^v = id_C ⊗_H ∂^D` (changes `q`) -/
def balancedProductDoubleComplex : DoubleComplex𝔽₂ :=
  HomologicalComplex₂.ofGradedObject
    (ComplexShape.down ℤ) (ComplexShape.down ℤ)
    (fun ⟨p, q⟩ => C.bpObj D p q)
    (fun p p' q => C.bpDh D p p' q)
    (fun p q q' => C.bpDv D p q q')
    (fun p p' h q => C.bpDh_shape D p p' h q)
    (fun p q q' h => C.bpDv_shape D p q q' h)
    (fun p p' p'' q => C.bpDh_comp D p p' p'' q)
    (fun p q q' q'' => C.bpDv_comp D p q q' q'')
    (fun p p' q q' => C.bpDh_comm_bpDv D p p' q q')

/-! ## Total complex -/

instance balancedProductDoubleComplex_hasTotal :
    (C.balancedProductDoubleComplex D).HasTotal (ComplexShape.down ℤ) := by
  unfold HomologicalComplex₂.HasTotal
  intro j
  infer_instance

/-- The balanced product complex `C ⊗_H D = Tot(C ⊠_H D)`.
This is the total complex of the balanced product double complex. -/
def balancedProductComplex : ChainComplex𝔽₂ :=
  (C.balancedProductDoubleComplex D).totalComplex

/-! ## Basic properties -/

/-- The object `(C ⊠_H D)_{p,q} = C_p ⊗_H D_q`. -/
theorem balancedProductDoubleComplex_obj (p q : ℤ) :
    (C.balancedProductDoubleComplex D).obj p q = C.bpObj D p q := rfl

/-- The vertical differential of the balanced product double complex is `id_C ⊗_H ∂^D`. -/
theorem balancedProductDoubleComplex_dv_eq (p q : ℤ) :
    (C.balancedProductDoubleComplex D).dv p q =
    (C.bpDv D p q (q - 1)).hom := rfl

/-- The horizontal differential of the balanced product double complex is `∂^C ⊗_H id_D`. -/
theorem balancedProductDoubleComplex_dh_eq (p q : ℤ) :
    (C.balancedProductDoubleComplex D).dh p q =
    (C.bpDh D p (p - 1) q).hom := rfl

/-! ## Witness: the balanced product is nonempty -/

lemma balancedProductComplex_nonempty (n : ℤ) :
    Nonempty ((C.balancedProductComplex D).X n) := ⟨0⟩

end HEquivariantChainComplex

end
