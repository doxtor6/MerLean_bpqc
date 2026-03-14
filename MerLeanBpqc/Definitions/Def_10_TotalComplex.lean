import MerLeanBpqc.Definitions.Def_9_DoubleComplex
import MerLeanBpqc.Definitions.Def_1_ChainComplex
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Definition 10: Total Complex

Given a double complex `E = (E_{•,•}, ∂^v, ∂^h)` (Def_9), the total complex `Tot(E)` is the
chain complex (Def_1) defined by:
- `Tot(E)_n = ⊕_{p+q=n} E_{p,q}` (direct sum over all pairs with `p + q = n`)
- `∂_n|_{E_{p,q}} = ∂^v_{p,q} + ∂^h_{p,q}` (the differential on summand `E_{p,q}`)

where `∂^v_{p,q} : E_{p,q} → E_{p,q-1}` maps into the `(p, q-1)`-summand and
`∂^h_{p,q} : E_{p,q} → E_{p-1,q}` maps into the `(p-1, q)`-summand of `Tot(E)_{n-1}`.

This is indeed a differential since `∂² = (∂^v + ∂^h)² = (∂^v)² + (∂^v∂^h + ∂^h∂^v) + (∂^h)²
= 0 + 0 + 0 = 0`, using that `E` is a double complex and we work over `𝔽₂` where
`∂^v∂^h + ∂^h∂^v = 2∂^v∂^h = 0`.

We use Mathlib's `HomologicalComplex₂.total` construction, which builds the total complex
with sign conventions. Over `𝔽₂`, the signs are trivial (`-1 = 1`), so Mathlib's total
complex agrees with the paper's sign-free definition.

## Main Definitions
- `tensorSigns_down_int` — `TensorSigns` instance for `ComplexShape.down ℤ`
- `DoubleComplex𝔽₂.totalComplex` — the total complex `Tot(E)` as a chain complex over `𝔽₂`
- `DoubleComplex𝔽₂.ιTotal` — the inclusion `E_{p,q} ↪ Tot(E)_n` when `p + q = n`

## Main Results
- `DoubleComplex𝔽₂.totalComplex_d_sq_zero` — the differential squares to zero: `∂² = 0`
- `DoubleComplex𝔽₂.totalComplex_obj_eq` — `Tot(E)_n` is the coproduct of `E_{p,q}` with `p+q=n`
-/

open CategoryTheory

/-! ## TensorSigns instance for `ComplexShape.down ℤ` -/

/-- `TensorSigns` instance for the descending complex shape on `ℤ`.
The sign map is `ε(n) = (-1)^n`, implemented via `Int.negOnePow`.
For `ComplexShape.down ℤ`, `Rel i j ↔ j + 1 = i`. -/
instance tensorSigns_down_int : ComplexShape.TensorSigns (ComplexShape.down ℤ) where
  ε' := MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r (hpq : q + 1 = p) := show q + r + 1 = p + r by omega
  add_rel p q r (hpq : q + 1 = p) := show r + q + 1 = r + p by omega
  ε'_succ p q (hpq : q + 1 = p) := by
    simp only [MonoidHom.mk'_apply]
    rw [← hpq, Int.negOnePow_succ, neg_neg]

@[simp]
lemma ε_down_int (n : ℤ) : (ComplexShape.down ℤ).ε n = n.negOnePow := rfl

namespace DoubleComplex𝔽₂

variable (E : DoubleComplex𝔽₂)

/-! ## HasTotal instance -/

/-- A double complex of `𝔽₂`-vector spaces has a total complex, since `ModuleCat 𝔽₂`
has all coproducts. -/
noncomputable instance hasTotal : E.HasTotal (ComplexShape.down ℤ) := by
  unfold HomologicalComplex₂.HasTotal
  intro j
  infer_instance

/-! ## The total complex -/

/-- The total complex `Tot(E)` of a double complex `E`. This is a chain complex over `𝔽₂`
indexed by `ℤ`, where `Tot(E)_n = ⊕_{p+q=n} E_{p,q}` and the differential is
`∂_n|_{E_{p,q}} = ∂^v_{p,q} + ∂^h_{p,q}`. -/
noncomputable def totalComplex : ChainComplex𝔽₂ :=
  E.total (ComplexShape.down ℤ)

/-! ## Inclusion maps -/

/-- The inclusion of summand `E_{p,q}` into `Tot(E)_n` when `p + q = n`. -/
noncomputable def ιTotalComplex (p q n : ℤ) (h : p + q = n) :
    E.obj p q ⟶ (E.totalComplex).X n :=
  E.ιTotal (ComplexShape.down ℤ) p q n h

/-! ## The total complex is a chain complex (∂² = 0) -/

/-- The differential of the total complex squares to zero: `∂_{n-1} ∘ ∂_n = 0`.
This follows from `(∂^v + ∂^h)² = (∂^v)² + (∂^v∂^h + ∂^h∂^v) + (∂^h)² = 0`,
using the double complex  and the fact that over `𝔽₂`, `∂^v∂^h + ∂^h∂^v = 0`. -/
theorem totalComplex_d_sq_zero (n m k : ℤ) :
    (E.totalComplex).d n m ≫ (E.totalComplex).d m k = 0 :=
  (E.totalComplex).d_comp_d n m k

/-- The `n`-th object of the total complex is the coproduct `⊕_{p+q=n} E_{p,q}`. -/
theorem totalComplex_obj_eq (n : ℤ) :
    (E.totalComplex).X n =
      E.toGradedObject.mapObj (ComplexShape.π (ComplexShape.down ℤ)
        (ComplexShape.down ℤ) (ComplexShape.down ℤ)) n := rfl

/-! ## Extensionality for morphisms from the total complex -/

/-- To show two morphisms from `Tot(E)_n` are equal, it suffices to check on each summand. -/
theorem totalComplex_hom_ext {A : ModuleCat 𝔽₂} {n : ℤ}
    {f g : (E.totalComplex).X n ⟶ A}
    (h : ∀ (p q : ℤ) (hpq : p + q = n),
      E.ιTotalComplex p q n hpq ≫ f = E.ιTotalComplex p q n hpq ≫ g) :
    f = g :=
  HomologicalComplex₂.total.hom_ext (ComplexShape.down ℤ) h

end DoubleComplex𝔽₂
