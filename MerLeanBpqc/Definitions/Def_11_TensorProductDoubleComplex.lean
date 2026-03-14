import MerLeanBpqc.Definitions.Def_10_TotalComplex
import MerLeanBpqc.Definitions.Def_4_CSSCode
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Definition 11: Tensor Product Double Complex

Given two chain complexes `C = (C_•, ∂^C)` and `D = (D_•, ∂^D)` over `𝔽₂`, the tensor product
double complex `C ⊠ D` is the double complex (Def_9) defined by:
- `(C ⊠ D)_{p,q} = C_p ⊗ D_q`
- vertical differential `∂^v_{p,q} = id_{C_p} ⊗ ∂^D_q : C_p ⊗ D_q → C_p ⊗ D_{q-1}`
- horizontal differential `∂^h_{p,q} = ∂^C_p ⊗ id_{D_q} : C_p ⊗ D_q → C_{p-1} ⊗ D_q`

The tensor product complex is `C ⊗ D = Tot(C ⊠ D)` (Def_10), so that
`(C ⊗ D)_n = ⊕_{p+q=n} C_p ⊗ D_q` with differential `∂ = ∂^C ⊗ id + id ⊗ ∂^D`.

Over `𝔽₂` the usual sign `(-1)^p` is trivial.

When `C` and `D` are both 1-complexes (concentrated in degrees 0 and 1), the resulting
CSS code obtained from the total complex is called a hypergraph product code.

## Main Definitions
- `tensorDoubleComplex` — the tensor product double complex `C ⊠ D`
- `tensorComplex` — the tensor product complex `C ⊗ D = Tot(C ⊠ D)`
- `hypergraphProductCode` — the CSS code from the tensor product of two 1-complexes

## Main Results
- `tensorDoubleComplex_obj` — `(C ⊠ D)_{p,q} = C_p ⊗ D_q`
- `tensorDoubleComplex_dv` — vertical differential is `id_C ⊗ ∂^D`
- `tensorDoubleComplex_dh` — horizontal differential is `∂^C ⊗ id_D`
-/

open CategoryTheory MonoidalCategory

namespace ChainComplex𝔽₂

variable (C D : ChainComplex𝔽₂)

/-! ## The tensor product double complex -/

/-- The graded object underlying the tensor product double complex:
`(C ⊠ D)_{p,q} = C_p ⊗ D_q`. -/
noncomputable def tensorObj' (p q : ℤ) : ModuleCat 𝔽₂ := C.X p ⊗ D.X q

/-- The horizontal differential `∂^C_p ⊗ id_{D_q} : C_p ⊗ D_q → C_{p'} ⊗ D_q`.
This maps in the `p`-direction (first index). -/
noncomputable def tensorDh (p p' q : ℤ) : C.X p ⊗ D.X q ⟶ C.X p' ⊗ D.X q :=
  C.d p p' ▷ D.X q

/-- The vertical differential `id_{C_p} ⊗ ∂^D_q : C_p ⊗ D_q → C_p ⊗ D_{q'}`.
This maps in the `q`-direction (second index). -/
noncomputable def tensorDv (p q q' : ℤ) : C.X p ⊗ D.X q ⟶ C.X p ⊗ D.X q' :=
  C.X p ◁ D.d q q'

/-! ## Shape conditions -/

private lemma tensorDh_shape (p p' : ℤ) (h : ¬(ComplexShape.down ℤ).Rel p p') (q : ℤ) :
    C.tensorDh D p p' q = 0 := by
  simp [tensorDh, C.shape p p' h]

private lemma tensorDv_shape (p : ℤ) (q q' : ℤ) (h : ¬(ComplexShape.down ℤ).Rel q q') :
    C.tensorDv D p q q' = 0 := by
  simp [tensorDv, D.shape q q' h]

/-! ## d² = 0 conditions -/

private lemma tensorDh_comp (p p' p'' q : ℤ) :
    C.tensorDh D p p' q ≫ C.tensorDh D p' p'' q = 0 := by
  simp [tensorDh, ← comp_whiskerRight, C.d_comp_d]

private lemma tensorDv_comp (p q q' q'' : ℤ) :
    C.tensorDv D p q q' ≫ C.tensorDv D p q' q'' = 0 := by
  simp [tensorDv, ← whiskerLeft_comp, D.d_comp_d]

/-! ## Commutativity: ∂^h ∘ ∂^v = ∂^v ∘ ∂^h -/

private lemma tensorDh_comm_tensorDv (p p' q q' : ℤ) :
    C.tensorDh D p p' q ≫ C.tensorDv D p' q q' =
    C.tensorDv D p q q' ≫ C.tensorDh D p p' q' := by
  simp only [tensorDh, tensorDv]
  exact (whisker_exchange (C.d p p') (D.d q q')).symm

/-! ## The tensor product double complex -/

/-- The tensor product double complex `C ⊠ D` as a `DoubleComplex𝔽₂`.
Objects are `(C ⊠ D)_{p,q} = C_p ⊗ D_q` with:
- horizontal differential `∂^h_{p,q} = ∂^C_p ⊗ id_{D_q}` (the paper's `∂^C ⊗ id_D`)
- vertical differential `∂^v_{p,q} = id_{C_p} ⊗ ∂^D_q` (the paper's `id_C ⊗ ∂^D`) -/
noncomputable def tensorDoubleComplex : DoubleComplex𝔽₂ :=
  HomologicalComplex₂.ofGradedObject
    (ComplexShape.down ℤ) (ComplexShape.down ℤ)
    (fun ⟨p, q⟩ => C.X p ⊗ D.X q)
    (fun p p' q => C.tensorDh D p p' q)
    (fun p q q' => C.tensorDv D p q q')
    (fun p p' h q => C.tensorDh_shape D p p' h q)
    (fun p q q' h => C.tensorDv_shape D p q q' h)
    (fun p p' p'' q => C.tensorDh_comp D p p' p'' q)
    (fun p q q' q'' => C.tensorDv_comp D p q q' q'')
    (fun p p' q q' => C.tensorDh_comm_tensorDv D p p' q q')

/-! ## Accessor lemmas for the tensor double complex -/

/-- The object `(C ⊠ D)_{p,q} = C_p ⊗ D_q`. -/
theorem tensorDoubleComplex_obj (p q : ℤ) :
    (C.tensorDoubleComplex D).obj p q = (C.X p ⊗ D.X q) := rfl

/-- The vertical differential of the tensor double complex is `id_{C_p} ⊗ ∂^D_q`. -/
theorem tensorDoubleComplex_dv_eq (p q : ℤ) :
    ((C.tensorDoubleComplex D).X p).d q (q - 1) = C.tensorDv D p q (q - 1) := rfl

/-- The horizontal differential of the tensor double complex is `∂^C_p ⊗ id_{D_q}`. -/
theorem tensorDoubleComplex_dh_eq (p q : ℤ) :
    ((C.tensorDoubleComplex D).d p (p - 1)).f q = C.tensorDh D p (p - 1) q := rfl

/-! ## HasTotal instance for the tensor double complex -/

/-- The tensor product double complex has a total complex. -/
noncomputable instance tensorDoubleComplex_hasTotal :
    (C.tensorDoubleComplex D).HasTotal (ComplexShape.down ℤ) := by
  unfold HomologicalComplex₂.HasTotal
  intro j
  infer_instance

/-! ## The tensor product complex -/

/-- The tensor product complex `C ⊗ D = Tot(C ⊠ D)` (Def_10).
This is a chain complex over `𝔽₂` with `(C ⊗ D)_n = ⊕_{p+q=n} C_p ⊗ D_q` and
differential `∂ = ∂^C ⊗ id + id ⊗ ∂^D`. Over `𝔽₂` the sign `(-1)^p` is trivial. -/
noncomputable def tensorComplex : ChainComplex𝔽₂ :=
  (C.tensorDoubleComplex D).totalComplex

/-- The inclusion of the summand `C_p ⊗ D_q` into `(C ⊗ D)_n` when `p + q = n`. -/
noncomputable def ιTensorComplex (p q n : ℤ) (h : p + q = n) :
    C.X p ⊗ D.X q ⟶ (C.tensorComplex D).X n :=
  (C.tensorDoubleComplex D).ιTotalComplex p q n h

/-! ## Hypergraph product code -/

/-- A hypergraph product code is the CSS code obtained from the tensor product complex
of two 1-complexes `C₁ →[∂^C] C₀` and `D₁ →[∂^D] D₀`. The total complex of
`C ⊠ D` has three nontrivial degrees:
- degree 2: `C₁ ⊗ D₁`
- degree 1: `(C₁ ⊗ D₀) ⊕ (C₀ ⊗ D₁)`
- degree 0: `C₀ ⊗ D₀`

The resulting CSS code has `H_Z^T` as the differential from degree 2 to degree 1
and `H_X` as the differential from degree 1 to degree 0 in the total complex,
shifted by 1 to match the CSS code convention `C₁ →[H_Z^T] C₀ →[H_X] C_{-1}`. -/
noncomputable def hypergraphProductCode
    {n₁ m₁ n₂ m₂ : ℕ}
    (dC : (Fin n₁ → 𝔽₂) →ₗ[𝔽₂] (Fin m₁ → 𝔽₂))
    (dD : (Fin n₂ → 𝔽₂) →ₗ[𝔽₂] (Fin m₂ → 𝔽₂)) :
    ChainComplex𝔽₂ :=
  (ClassicalCode.parityCheckComplex dC).tensorComplex (ClassicalCode.parityCheckComplex dD)

end ChainComplex𝔽₂
