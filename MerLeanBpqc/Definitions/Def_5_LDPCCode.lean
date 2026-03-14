import MerLeanBpqc.Definitions.Def_4_CSSCode

/-!
# Definition 5: LDPC Code

A family of CSS codes (Def_4) is called low-density parity-check (LDPC) if there exists some
`w ∈ ℕ` such that for each member of the family, the parity-check matrices `H_X` and `H_Z`
satisfy: (1) every row has Hamming weight at most `w`, and (2) every column has Hamming weight
at most `w`. Equivalently, both `H_X` and `H_Z` have row weight and column weight bounded
by `w`, uniformly across the family.

## Main Definitions
- `rowWeight` — the Hamming weight of a row of a linear map (viewed as a matrix)
- `colWeight` — the Hamming weight of a column of a linear map (viewed as a matrix)
- `HasBoundedWeight` — a linear map has all row and column weights bounded by `w`
- `CSSCode.IsLDPC` — a family of CSS codes is LDPC
-/

/-! ## Row and column weight of a linear map

For a linear map `f : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)`, corresponding to an `m × n` matrix:
- The `i`-th row vector is `fun j : Fin n => f (Pi.single j 1) i`
- The `j`-th column vector is `f (Pi.single j 1) : Fin m → 𝔽₂`
-/

/-- The Hamming weight of row `i` of the matrix representation of `f`.
For `f : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)` and `i : Fin m`, this counts the number
of columns `j` such that the `(i, j)`-entry of the matrix is nonzero. -/
def rowWeight {n m : ℕ} (f : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) (i : Fin m) : ℕ :=
  hammingWeight (fun j : Fin n => f (Pi.single j 1) i)

/-- The Hamming weight of column `j` of the matrix representation of `f`.
For `f : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)` and `j : Fin n`, this counts the number
of rows `i` such that the `(i, j)`-entry of the matrix is nonzero. -/
def colWeight {n m : ℕ} (f : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) (j : Fin n) : ℕ :=
  hammingWeight (f (Pi.single j 1))

/-- A linear map `f : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)` has bounded weight `w` if
every row and every column of its matrix representation has Hamming weight at most `w`. -/
def HasBoundedWeight {n m : ℕ} (f : (Fin n → 𝔽₂) →ₗ[𝔽₂] (Fin m → 𝔽₂)) (w : ℕ) : Prop :=
  (∀ i : Fin m, rowWeight f i ≤ w) ∧ (∀ j : Fin n, colWeight f j ≤ w)

/-! ## LDPC property for CSS code families

The LDPC property is defined for a family of CSS codes indexed by some type `ι`.
For each member, both `H_X` and `H_Z` must have bounded row and column weight.

Since the `CSSCode` structure stores `H_Z^T` rather than `H_Z`, we observe that
row weight of `H_Z` = column weight of `H_Z^T` and column weight of `H_Z` = row weight of `H_Z^T`.
Thus "H_Z has bounded weight w" is equivalent to "H_Z^T has bounded weight w", since both
row and column weights are bounded by the same `w`.
-/

namespace CSSCode

/-- A family of CSS codes indexed by `ι` is low-density parity-check (LDPC) if there
exists a uniform bound `w : ℕ` such that for every member of the family, both `H_X`
and `H_Z` have all row weights and column weights at most `w`.

Since the CSS code stores `H_Z^T` and the weight bound `w` applies to both rows and
columns, `HasBoundedWeight HZT w` captures exactly that `H_Z` has bounded row and
column weight `w` (with rows and columns swapped). -/
def IsLDPC {ι : Type*} {n rX rZ : ι → ℕ} (family : ∀ α : ι, CSSCode (n α) (rX α) (rZ α)) : Prop :=
  ∃ w : ℕ, ∀ α : ι, HasBoundedWeight (family α).HX w ∧ HasBoundedWeight (family α).HZT w

end CSSCode
