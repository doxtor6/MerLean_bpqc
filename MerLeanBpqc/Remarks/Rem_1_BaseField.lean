import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# Remark 1: Base Field

For the remainder of this manuscript we will only consider vector spaces over the
field $\mathbb{F}_2$. All tensor products, linear maps, and homology computations
are taken over $\mathbb{F}_2$ unless stated otherwise.

## Main Definitions
- `𝔽₂`: abbreviation for `ZMod 2`, the field with two elements

## Main Results
- `𝔽₂.field`: `ZMod 2` is a field
- `𝔽₂.charTwo`: `ZMod 2` has characteristic 2
- `𝔽₂.fintype`: `ZMod 2` is finite with cardinality 2
- `𝔽₂.neg_eq_self`: in characteristic 2, negation is the identity
- `𝔽₂.add_self_eq_zero`: in characteristic 2, `a + a = 0`
-/

open scoped TensorProduct

/-! ## Base field definition -/

/-- `𝔽₂` is the field with two elements, `ZMod 2`. All vector spaces, tensor products,
    linear maps, and homology computations in this paper are over `𝔽₂`. -/
abbrev 𝔽₂ : Type := ZMod 2

namespace 𝔽₂

/-! ## Field and finiteness instances -/

instance prime_two : Fact (Nat.Prime 2) := Nat.fact_prime_two

instance field : Field 𝔽₂ := ZMod.instField 2

instance fintype : Fintype 𝔽₂ := ZMod.fintype 2

instance charTwo : CharP 𝔽₂ 2 := ZMod.charP 2

/-! ## Basic properties of 𝔽₂ arithmetic -/

/-- In `𝔽₂`, the cardinality is 2. -/
theorem card_eq : Fintype.card 𝔽₂ = 2 := ZMod.card 2

/-- In `𝔽₂`, every element equals its own negation. -/
theorem neg_eq_self (a : 𝔽₂) : -a = a :=
  CharTwo.neg_eq a

/-- In `𝔽₂`, `a + a = 0` for all `a`. -/
theorem add_self_eq_zero (a : 𝔽₂) : a + a = 0 :=
  CharTwo.add_self_eq_zero a

/-- In `𝔽₂`, subtraction equals addition. -/
theorem sub_eq_add (a b : 𝔽₂) : a - b = a + b :=
  CharTwo.sub_eq_add a b

end 𝔽₂
