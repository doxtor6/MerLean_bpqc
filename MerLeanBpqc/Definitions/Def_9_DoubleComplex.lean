import MerLeanBpqc.Remarks.Rem_2_NotationConventions
import Mathlib.Algebra.Homology.HomologicalBicomplex

/-!
# Definition 9: Double Complex

A double complex `E = (E_{•,•}, ∂^v, ∂^h)` is an array of `𝔽₂`-vector spaces `E_{p,q}`
indexed by `(p, q) ∈ ℤ × ℤ`, equipped with vertical and horizontal differentials:
- `∂^v_{p,q} : E_{p,q} → E_{p,q-1}` (vertical, decreasing q)
- `∂^h_{p,q} : E_{p,q} → E_{p-1,q}` (horizontal, decreasing p)

satisfying:
1. `∂^v_{p,q-1} ∘ ∂^v_{p,q} = 0` for all `p, q`
2. `∂^h_{p-1,q} ∘ ∂^h_{p,q} = 0` for all `p, q`
3. `∂^v_{p-1,q} ∘ ∂^h_{p,q} = ∂^h_{p,q-1} ∘ ∂^v_{p,q}` for all `p, q` (commutativity)

Over `𝔽₂`, commutativity and anticommutativity coincide since `-1 = 1`.

We use Mathlib's `HomologicalComplex₂` as the underlying type, with both complex shapes
being `ComplexShape.down ℤ` (decreasing indices).

## Main Definitions
- `DoubleComplex𝔽₂` — a double complex of `𝔽₂`-vector spaces, as a bicomplex
- `DoubleComplex𝔽₂.obj` — the vector space `E_{p,q}` at position `(p, q)`
- `DoubleComplex𝔽₂.dv` — the vertical differential `∂^v_{p,q} : E_{p,q} → E_{p,q-1}`
- `DoubleComplex𝔽₂.dh` — the horizontal differential `∂^h_{p,q} : E_{p,q} → E_{p-1,q}`

## Main Results
- `DoubleComplex𝔽₂.dv_comp_dv` — `∂^v ∘ ∂^v = 0`
- `DoubleComplex𝔽₂.dh_comp_dh` — `∂^h ∘ ∂^h = 0`
- `DoubleComplex𝔽₂.comm` — commutativity: `∂^v ∘ ∂^h = ∂^h ∘ ∂^v`
- `DoubleComplex𝔽₂.anticomm_eq_comm` — over `𝔽₂`, anticommutativity = commutativity
-/

open CategoryTheory

/-! ## Definition -/

/-- A double complex of `𝔽₂`-vector spaces indexed by `ℤ × ℤ`.
This is `HomologicalComplex₂ (ModuleCat 𝔽₂) (ComplexShape.down ℤ) (ComplexShape.down ℤ)`,
where the first `ComplexShape.down ℤ` is the horizontal direction (decreasing `p`)
and the second is the vertical direction (decreasing `q`).

For `E : DoubleComplex𝔽₂`:
- `(E.X p).X q` is the vector space `E_{p,q}`
- `(E.X p).d q q'` is the vertical differential `∂^v_{p,q}` when `q' + 1 = q`
- `(E.d p p').f q` is the horizontal differential `∂^h_{p,q}` when `p' + 1 = p` -/
abbrev DoubleComplex𝔽₂ :=
  HomologicalComplex₂ (ModuleCat 𝔽₂) (ComplexShape.down ℤ) (ComplexShape.down ℤ)

namespace DoubleComplex𝔽₂

variable (E : DoubleComplex𝔽₂)

/-! ## Accessor functions -/

/-- The `𝔽₂`-vector space `E_{p,q}` at position `(p, q)`. -/
noncomputable def obj (p q : ℤ) : ModuleCat 𝔽₂ := (E.X p).X q

/-- The vertical differential `∂^v_{p,q} : E_{p,q} → E_{p,q-1}` as a linear map. -/
noncomputable def dv (p q : ℤ) : ↥(E.obj p q) →ₗ[𝔽₂] ↥(E.obj p (q - 1)) :=
  ((E.X p).d q (q - 1)).hom

/-- The horizontal differential `∂^h_{p,q} : E_{p,q} → E_{p-1,q}` as a linear map. -/
noncomputable def dh (p q : ℤ) : ↥(E.obj p q) →ₗ[𝔽₂] ↥(E.obj (p - 1) q) :=
  ((E.d p (p - 1)).f q).hom



/-- The vertical differential squares to zero: `∂^v_{p,q-1} ∘ ∂^v_{p,q} = 0`. -/
theorem dv_comp_dv (p q : ℤ) :
    (E.dv p (q - 1)).comp (E.dv p q) = 0 := by
  simp only [dv]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  have h := (E.X p).d_comp_d q (q - 1) (q - 1 - 1)
  have : ((E.X p).d q (q - 1) ≫ (E.X p).d (q - 1) (q - 1 - 1)) x = 0 := by
    rw [h]; simp
  rwa [ModuleCat.comp_apply] at this

/-- The horizontal differential squares to zero: `∂^h_{p-1,q} ∘ ∂^h_{p,q} = 0`. -/
theorem dh_comp_dh (p q : ℤ) :
    (E.dh (p - 1) q).comp (E.dh p q) = 0 := by
  simp only [dh]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  have h := E.d_comp_d p (p - 1) (p - 1 - 1)
  have hfq : ((E.d p (p - 1) ≫ E.d (p - 1) (p - 1 - 1)).f q) x = 0 := by
    rw [h]; simp
  rwa [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hfq

/-- The differentials commute: `∂^v_{p-1,q} ∘ ∂^h_{p,q} = ∂^h_{p,q-1} ∘ ∂^v_{p,q}`.
This is the commutativity condition for the double complex. -/
theorem comm (p q : ℤ) :
    (E.dv (p - 1) q).comp (E.dh p q) = (E.dh p (q - 1)).comp (E.dv p q) := by
  simp only [dv, dh]
  ext x
  simp only [LinearMap.comp_apply]
  have h := HomologicalComplex₂.d_comm E p (p - 1) q (q - 1)
  have := congr_arg (fun f => f x) (congr_arg ModuleCat.Hom.hom h)
  simp only [ModuleCat.comp_apply] at this
  exact this

/-! ## Commutativity and anticommutativity over 𝔽₂ -/

/-- Over `𝔽₂`, anticommutativity `∂^v ∘ ∂^h + ∂^h ∘ ∂^v = 0` is equivalent to
commutativity `∂^v ∘ ∂^h = ∂^h ∘ ∂^v`, since `-1 = 1` in characteristic 2. -/
theorem anticomm_eq_comm (p q : ℤ) :
    (E.dv (p - 1) q).comp (E.dh p q) + (E.dh p (q - 1)).comp (E.dv p q) = 0 := by
  rw [E.comm p q]
  ext x
  simp only [LinearMap.add_apply, LinearMap.zero_apply]
  have h2 : (2 : 𝔽₂) = 0 := by decide
  have : (2 : 𝔽₂) • ((E.dh p (q - 1) ∘ₗ E.dv p q) x) = 0 := by rw [h2, zero_smul]
  rwa [two_smul] at this

end DoubleComplex𝔽₂
