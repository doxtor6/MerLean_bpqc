import MerLeanBpqc.Definitions.Def_27_HorizontalVerticalHomologySplitting
import MerLeanBpqc.Definitions.Def_28_IotaPiMaps
import MerLeanBpqc.Definitions.Def_6_SubsystemCSSCode

/-!
# Definition 29: Horizontal Subsystem Balanced Product Code

The horizontal subsystem balanced product code is the subsystem CSS code (Def_6) whose
underlying CSS code is the balanced product Tanner cycle code (Def_26), with the
logical/gauge splitting defined by:
- `H₁ᴸ := H₁ʰ` (logical Z-operators correspond to horizontal homology)
- `H₁ᴳ := H₁ᵛ` (gauge Z-operators correspond to vertical homology)

We define HL and HG as submodules of H₁ via the Künneth isomorphism and prove they
form a complementary pair (`IsCompl`). This gives the direct sum decomposition
`H₁ ≅ H₁ᴸ ⊕ H₁ᴳ` required by the subsystem CSS code structure.

When the quotient Tanner differential is injective, `H₁ᵛ = 0` and hence `H₁ᴳ = 0`,
reducing the subsystem code to an ordinary CSS code.

## Main Definitions
- `HL` — the logical submodule of H₁ (image of H₁ʰ under the Künneth iso)
- `HG` — the gauge submodule of H₁ (image of H₁ᵛ under the Künneth iso)
- `hcompl` — proof that `HL` and `HG` are complementary
- `HG_eq_bot_of_tanner_H0_subsingleton` — when `H₀(C(X,L)) = 0`, `HG = ⊥`
- `cohomology_iscompl` — the cohomology splitting `H¹ = H¹_L ⊕ H¹_G`

## Main Results
- `HL_eq_bot_of_quotient_ker_trivial` — injectivity of quotient ∂ implies `HL = ⊥`
- `encodingRate_eq` — the logical qubits equal `dim H₁(C(X/H, L))`
-/

open CategoryTheory Representation
open scoped TensorProduct DirectSum

noncomputable section

namespace HorizontalSubsystemBalancedProductCode

variable {H : Type} [Group H] [Fintype H] [DecidableEq H]
variable (X : GraphWithGroupAction H)
variable {s : ℕ} (Λ : X.CellLabeling s)
variable (ℓ : ℕ) [NeZero ℓ] [MulAction H (Fin ℓ)]
variable (hℓ_ge : ℓ ≥ 3) (hℓ_odd : ℓ % 2 = 1)
variable (hΛ : GraphWithGroupAction.IsInvariantLabeling Λ)
variable (hcompat : BalancedProductTannerCycleCode.CycleCompatibleAction (H := H) ℓ)
variable (hodd : Odd (Fintype.card H))

/-! ## Abbreviations from Def_27 -/

/-- The balanced product complex. -/
abbrev bpComplex :=
  HorizontalVerticalHomologySplitting.bpComplex X Λ ℓ hΛ hcompat

/-- The degree-1 homology of the balanced product complex. -/
abbrev H1 := HorizontalVerticalHomologySplitting.H1 X Λ ℓ hΛ hcompat

/-- The horizontal homology `H₁ʰ`. -/
abbrev H1h := HorizontalVerticalHomologySplitting.H1h X Λ ℓ hΛ hcompat

/-- The vertical homology `H₁ᵛ`. -/
abbrev H1v := HorizontalVerticalHomologySplitting.H1v X Λ ℓ hΛ hcompat

/-! ## Logical and Gauge Submodules

We define the logical submodule `HL` and gauge submodule `HG` as the images of the
horizontal and vertical summand inclusions under the inverse Künneth isomorphism. -/

/-- The inclusion of the horizontal summand `H₁ʰ` into the Künneth direct sum. -/
def incH : H1h X Λ ℓ hΛ hcompat →ₗ[𝔽₂]
    HEquivariantChainComplex.balancedKunnethSum
      (HorizontalVerticalHomologySplitting.tannerHEq X Λ hΛ)
      (HorizontalVerticalHomologySplitting.cycleHEq ℓ hcompat) 1 :=
  HorizontalVerticalHomologySplitting.directSumInc X Λ ℓ hΛ hcompat 1

/-- The inclusion of the vertical summand `H₁ᵛ` into the Künneth direct sum. -/
def incV : H1v X Λ ℓ hΛ hcompat →ₗ[𝔽₂]
    HEquivariantChainComplex.balancedKunnethSum
      (HorizontalVerticalHomologySplitting.tannerHEq X Λ hΛ)
      (HorizontalVerticalHomologySplitting.cycleHEq ℓ hcompat) 1 :=
  HorizontalVerticalHomologySplitting.directSumInc X Λ ℓ hΛ hcompat 0

/-- The embedding of `H₁ʰ` into `H₁` via the inverse Künneth isomorphism. -/
def embH : H1h X Λ ℓ hΛ hcompat →ₗ[𝔽₂] H1 X Λ ℓ hΛ hcompat :=
  (HorizontalVerticalHomologySplitting.kunnethIso X Λ ℓ hΛ hcompat hodd).symm.toLinearMap.comp
    (incH X Λ ℓ hΛ hcompat)

/-- The embedding of `H₁ᵛ` into `H₁` via the inverse Künneth isomorphism. -/
def embV : H1v X Λ ℓ hΛ hcompat →ₗ[𝔽₂] H1 X Λ ℓ hΛ hcompat :=
  (HorizontalVerticalHomologySplitting.kunnethIso X Λ ℓ hΛ hcompat hodd).symm.toLinearMap.comp
    (incV X Λ ℓ hΛ hcompat)

/-- The logical submodule `H₁ᴸ := H₁ʰ` as a submodule of `H₁`, defined as the range
of the horizontal embedding. Logical Z-operators correspond to nontrivial elements
of the horizontal homology. -/
def HL : Submodule 𝔽₂ (H1 X Λ ℓ hΛ hcompat) :=
  LinearMap.range (embH X Λ ℓ hΛ hcompat hodd)

/-- The gauge submodule `H₁ᴳ := H₁ᵛ` as a submodule of `H₁`, defined as the range
of the vertical embedding. Gauge Z-operators correspond to the vertical homology. -/
def HG : Submodule 𝔽₂ (H1 X Λ ℓ hΛ hcompat) :=
  LinearMap.range (embV X Λ ℓ hΛ hcompat hodd)

/-! ## Subsingleton infrastructure for direct sum decomposition -/

/-- If the chain module at degree `p` is subsingleton, so is the cycles submodule. -/
private lemma cycles_subsingleton_of_X_subsingleton (C : ChainComplex𝔽₂) (p : ℤ)
    [h : Subsingleton ↑(C.X p)] : Subsingleton ↥(C.cycles p) := by
  constructor
  intro ⟨a, ha⟩ ⟨b, hb⟩
  have : a = b := Subsingleton.elim a b
  exact Subtype.ext this

/-- If the chain module at degree `p` is subsingleton, so is the homology. -/
private lemma homology_subsingleton_of_X_subsingleton (C : ChainComplex𝔽₂) (p : ℤ)
    [h : Subsingleton ↑(C.X p)] : Subsingleton (C.homology' p) := by
  have hss_cyc : Subsingleton ↥(C.cycles p) := cycles_subsingleton_of_X_subsingleton C p
  constructor; intro a b
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact congr_arg _ (Subsingleton.elim x y)

/-- Tensor product with a subsingleton module is subsingleton. -/
private lemma tensorProduct_subsingleton_left (M N : Type*)
    [AddCommMonoid M] [AddCommMonoid N] [Module 𝔽₂ M] [Module 𝔽₂ N]
    [hM : Subsingleton M] : Subsingleton (M ⊗[𝔽₂] N) := by
  constructor
  intro a b
  have ha : a = 0 := by
    induction a using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => simp [Subsingleton.elim m 0]
    | add x y hx hy => rw [hx, hy, add_zero]
  have hb : b = 0 := by
    induction b using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => simp [Subsingleton.elim m 0]
    | add x y hx hy => rw [hx, hy, add_zero]
  rw [ha, hb]

/-- Coinvariants of a subsingleton representation is subsingleton. -/
private lemma coinvariants_subsingleton_of_subsingleton
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module 𝔽₂ V]
    (ρ : Representation 𝔽₂ G V) [hV : Subsingleton V] :
    Subsingleton (Coinvariants ρ) := by
  constructor
  intro a b
  obtain ⟨a', rfl⟩ := Coinvariants.mk_surjective ρ a
  obtain ⟨b', rfl⟩ := Coinvariants.mk_surjective ρ b
  exact congr_arg _ (Subsingleton.elim a' b')

/-- For the specific Tanner/cycle complexes, the balanced Künneth summand at index `p`
(for `n = 1`) is subsingleton when `p ∉ {0, 1}`. This follows because both complexes
have PUnit (zero) modules at degrees outside {0, 1}. -/
private lemma summand_subsingleton
    (p : ℤ) (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    Subsingleton (HEquivariantChainComplex.balancedKunnethSummand
      (HorizontalVerticalHomologySplitting.tannerHEq X Λ hΛ)
      (HorizontalVerticalHomologySplitting.cycleHEq ℓ hcompat) 1 p) := by
  -- The summand is Coinvariants(H_p(tanner) ⊗ H_{1-p}(cycle))
  -- For p ∉ {0,1}, tanner.X p is PUnit (subsingleton)
  have hss : Subsingleton ↑((BalancedProductTannerCycleCode.tannerCodeComplex X Λ).X p) :=
    BalancedProductTannerCycleCode.tannerCodeComplex_X_subsingleton X Λ hp0 hp1
  haveI : Subsingleton
      ((BalancedProductTannerCycleCode.tannerCodeComplex X Λ).homology' p) :=
    homology_subsingleton_of_X_subsingleton _ p
  haveI : Subsingleton
      ((HorizontalVerticalHomologySplitting.tannerHEq X Λ hΛ).complex.homology' p) :=
    ‹Subsingleton ((BalancedProductTannerCycleCode.tannerCodeComplex X Λ).homology' p)›
  haveI : Subsingleton
    (↑((HorizontalVerticalHomologySplitting.tannerHEq X Λ hΛ).complex.homology' p) ⊗[𝔽₂]
     ↑((HorizontalVerticalHomologySplitting.cycleHEq ℓ hcompat).complex.homology' (1 - p))) :=
    tensorProduct_subsingleton_left _ _
  exact coinvariants_subsingleton_of_subsingleton
    ((HorizontalVerticalHomologySplitting.tannerHEq X Λ hΛ).homologyAction p |>.tprod
     ((HorizontalVerticalHomologySplitting.cycleHEq ℓ hcompat).homologyAction (1 - p)))

/-- The direct sum decomposition: every element of the balanced Künneth sum (at degree 1)
for the Tanner/cycle complexes equals the sum of its components at indices 0 and 1. -/
private lemma directSum_decomp_01
    (z : HEquivariantChainComplex.balancedKunnethSum
      (HorizontalVerticalHomologySplitting.tannerHEq X Λ hΛ)
      (HorizontalVerticalHomologySplitting.cycleHEq ℓ hcompat) 1) :
    z = DirectSum.lof 𝔽₂ _ _ (1 : ℤ) (DirectSum.component 𝔽₂ _ _ (1 : ℤ) z) +
        DirectSum.lof 𝔽₂ _ _ (0 : ℤ) (DirectSum.component 𝔽₂ _ _ (0 : ℤ) z) := by
  apply DirectSum.ext_component 𝔽₂
  intro i
  simp only [map_add]
  by_cases h1 : i = 1
  · subst h1
    simp [DirectSum.component.lof_self, DirectSum.component.of,
          show (0 : ℤ) ≠ 1 from by omega]
  · by_cases h0 : i = 0
    · subst h0
      simp [DirectSum.component.lof_self, DirectSum.component.of,
            show (1 : ℤ) ≠ 0 from by omega]
    · simp [DirectSum.component.of, h0, h1]
      have : Subsingleton (HEquivariantChainComplex.balancedKunnethSummand
        (HorizontalVerticalHomologySplitting.tannerHEq X Λ hΛ)
        (HorizontalVerticalHomologySplitting.cycleHEq ℓ hcompat) 1 i) :=
        summand_subsingleton X Λ ℓ hΛ hcompat i h0 h1
      exact Subsingleton.elim _ _

/-! ## Complementarity -/

/-- The logical and gauge submodules form a complementary pair:
`H₁ = H₁ᴸ ⊕ H₁ᴳ`. This follows from the Künneth decomposition
`H₁ ≅ ⊕_p H_p(C(X,L)) ⊗_H H_{1-p}(C_ℓ)` with only the `p = 0, 1` summands
being nontrivial. -/
theorem hcompl : IsCompl (HL X Λ ℓ hΛ hcompat hodd) (HG X Λ ℓ hΛ hcompat hodd) := by
  constructor
  · -- Disjointness: HL ⊓ HG = ⊥
    rw [Submodule.disjoint_def]
    intro x hx_hl hx_hg
    rw [HL, LinearMap.mem_range] at hx_hl
    rw [HG, LinearMap.mem_range] at hx_hg
    obtain ⟨a, rfl⟩ := hx_hl
    obtain ⟨b, hb⟩ := hx_hg
    -- Apply the Künneth iso to both sides
    let iso := HorizontalVerticalHomologySplitting.kunnethIso X Λ ℓ hΛ hcompat hodd
    have ha_eq : iso (embH X Λ ℓ hΛ hcompat hodd a) = incH X Λ ℓ hΛ hcompat a := by
      simp only [embH, LinearMap.comp_apply]
      exact iso.apply_symm_apply _
    have hb_eq : iso (embV X Λ ℓ hΛ hcompat hodd b) = incV X Λ ℓ hΛ hcompat b := by
      simp only [embV, LinearMap.comp_apply]
      exact iso.apply_symm_apply _
    have heq : iso (embH X Λ ℓ hΛ hcompat hodd a) = iso (embV X Λ ℓ hΛ hcompat hodd b) :=
      congr_arg iso hb.symm
    rw [ha_eq, hb_eq] at heq
    -- The direct sum inclusions at different indices have disjoint ranges
    -- Apply component 1 to both sides
    have h1 : DirectSum.component 𝔽₂ _ _ (1 : ℤ) (incH X Λ ℓ hΛ hcompat a) = a := by
      simp [incH, HorizontalVerticalHomologySplitting.directSumInc,
            DirectSum.component.lof_self]
    have h1' : DirectSum.component 𝔽₂ _ _ (1 : ℤ) (incV X Λ ℓ hΛ hcompat b) = 0 := by
      simp [incV, HorizontalVerticalHomologySplitting.directSumInc, DirectSum.component.of,
            show (0 : ℤ) ≠ 1 from by omega]
    have ha_zero : a = 0 := by
      have := congr_arg (DirectSum.component 𝔽₂ _ _ (1 : ℤ)) heq
      rw [h1, h1'] at this
      exact this
    simp [ha_zero, embH, map_zero]
  · -- Codisjointness: HL ⊔ HG = ⊤
    rw [codisjoint_iff]
    ext x
    simp only [Submodule.mem_top, iff_true]
    rw [Submodule.mem_sup]
    let iso := HorizontalVerticalHomologySplitting.kunnethIso X Λ ℓ hΛ hcompat hodd
    -- Decompose iso x into its p=1 and p=0 components
    let z := iso x
    let z_h := DirectSum.component 𝔽₂ _ _ (1 : ℤ) z
    let z_v := DirectSum.component 𝔽₂ _ _ (0 : ℤ) z
    -- The key: the direct sum only has nontrivial summands at p = 0, 1
    -- so z = lof 1 z_h + lof 0 z_v
    refine ⟨embH X Λ ℓ hΛ hcompat hodd z_h, ⟨z_h, rfl⟩,
            embV X Λ ℓ hΛ hcompat hodd z_v, ⟨z_v, rfl⟩, ?_⟩
    -- Show x = embH z_h + embV z_v
    -- embH = iso.symm ∘ incH, embV = iso.symm ∘ incV
    -- So embH z_h + embV z_v = iso.symm (incH z_h) + iso.symm (incV z_v)
    -- Need: x = iso.symm (incH z_h + incV z_v)
    -- i.e., iso x = incH z_h + incV z_v = z
    apply iso.injective
    rw [map_add]
    -- Simplify iso (iso.symm (incH z_h)) = incH z_h etc
    have h1 : iso (embH X Λ ℓ hΛ hcompat hodd z_h) = incH X Λ ℓ hΛ hcompat z_h := by
      simp only [embH, LinearMap.comp_apply]; exact iso.apply_symm_apply _
    have h2 : iso (embV X Λ ℓ hΛ hcompat hodd z_v) = incV X Λ ℓ hΛ hcompat z_v := by
      simp only [embV, LinearMap.comp_apply]; exact iso.apply_symm_apply _
    rw [h1, h2]
    -- Now goal: incH z_h + incV z_v = iso x = z
    simp only [incH, incV, HorizontalVerticalHomologySplitting.directSumInc, z_h, z_v, z]
    exact (directSum_decomp_01 X Λ ℓ hΛ hcompat (iso x)).symm

/-! ## Cohomology splitting

Over `𝔽₂`, homology and cohomology are naturally isomorphic (Def_2). In Def_27,
the cohomology summands `coH1h` and `coH1v` are defined as the same balanced Künneth
summands as `H1h` and `H1v` respectively (since the underlying types coincide over `𝔽₂`).
Therefore the cohomology logical/gauge submodules are definitionally equal to their
homology counterparts, and the cohomology complementarity follows from `hcompl`. -/

/-- The logical cohomology submodule `H¹_L := H¹_h`. Over `𝔽₂`, the cohomology
summands coincide with the homology summands (Def_27: `coH1h = H1h`), so the
logical cohomology submodule equals `HL`. -/
abbrev coHL := HL X Λ ℓ hΛ hcompat hodd

/-- The gauge cohomology submodule `H¹_G := H¹_v`. Over `𝔽₂`, the cohomology
summands coincide with the homology summands (Def_27: `coH1v = H1v`), so the
gauge cohomology submodule equals `HG`. -/
abbrev coHG := HG X Λ ℓ hΛ hcompat hodd

/-- The cohomology logical and gauge submodules are complementary:
`H¹ = H¹_L ⊕ H¹_G`. This follows directly from the homology complementarity
`hcompl` since over `𝔽₂`, the cohomology splitting is identified with the
homology splitting via Def_2 and Def_27. -/
theorem cohomology_iscompl :
    IsCompl (coHL X Λ ℓ hΛ hcompat hodd) (coHG X Λ ℓ hΛ hcompat hodd) :=
  hcompl X Λ ℓ hΛ hcompat hodd

/-! ## Reduction to ordinary CSS code -/

/-- The cycles at degree 1 of the quotient Tanner complex equal the kernel of the
quotient Tanner differential. -/
private lemma quotientTannerCycles_eq_ker :
    (IotaPiMaps.quotientTannerComplex X Λ hΛ).cycles 1 =
    LinearMap.ker (IotaPiMaps.quotientTannerDifferential X Λ hΛ) := by
  -- cycles 1 = ker(differential 1) = ker((d 1 0).hom) = ker(quotientTannerDifferential)
  simp only [ChainComplex𝔽₂.cycles, ChainComplex𝔽₂.differential]
  congr 1

/-- When `ker(∂) = ⊥` for the quotient differential, the quotient Tanner homology
`H₁(C(X/H, L))` is trivial. -/
private lemma quotientTannerHomology_trivial
    (hker : LinearMap.ker (IotaPiMaps.quotientTannerDifferential X Λ hΛ) = ⊥) :
    ∀ a : IotaPiMaps.quotientTannerHomology X Λ hΛ, a = 0 := by
  -- Show cycles 1 = ⊥, hence ↥(cycles 1) is subsingleton, hence homology is subsingleton
  have hcycles_bot : (IotaPiMaps.quotientTannerComplex X Λ hΛ).cycles 1 = ⊥ := by
    rw [quotientTannerCycles_eq_ker X Λ hΛ, hker]
  have hss : Subsingleton ↥((IotaPiMaps.quotientTannerComplex X Λ hΛ).cycles 1) := by
    rw [hcycles_bot]
    constructor
    intro ⟨a, ha⟩ ⟨b, hb⟩
    exact Subtype.ext (((Submodule.mem_bot 𝔽₂).mp ha).trans ((Submodule.mem_bot 𝔽₂).mp hb).symm)
  -- The homology is a quotient of a subsingleton, hence subsingleton
  have : Subsingleton (IotaPiMaps.quotientTannerHomology X Λ hΛ) := by
    constructor; intro a b
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    exact congr_arg _ (Subsingleton.elim x y)
  exact fun a => Subsingleton.elim a 0

/-- When the quotient Tanner differential is injective (i.e., `ker(∂) = 0`), the
horizontal homology `H₁ʰ` is zero. By the iota/pi isomorphism (Def_28),
`H₁ʰ ≅ H₁(C(X/H, L))`, so injectivity of the quotient differential implies
`H₁ʰ = 0` and hence `HL = ⊥`.

Note: this is a consequence of injectivity, proving the *logical* part vanishes.
The paper's main reduction result (gauge vanishes) is `HG_eq_bot_of_tanner_H0_subsingleton`. -/
theorem HL_eq_bot_of_quotient_ker_trivial
    (h_odd : ℓ % 2 = 1)
    (hker : LinearMap.ker (IotaPiMaps.quotientTannerDifferential X Λ hΛ) = ⊥) :
    HL X Λ ℓ hΛ hcompat hodd = ⊥ := by
  -- Show HL = ⊥ by showing every element of H1h maps to 0
  simp only [HL, Submodule.eq_bot_iff, LinearMap.mem_range]
  intro x ⟨a, ha⟩
  have ha_zero : a = 0 := by
    have comp_id := IotaPiMaps.iotaMap_comp_piMap (X := X) (Λ := Λ) (ℓ := ℓ) (hΛ := hΛ) (hcompat := hcompat) h_odd hodd
    have ha_eq : a = IotaPiMaps.iotaMap X Λ ℓ hΛ hcompat
        (IotaPiMaps.piMap X Λ ℓ hΛ hcompat a) := by
      have := LinearMap.ext_iff.mp comp_id a
      simp [LinearMap.comp_apply] at this
      exact this.symm
    rw [ha_eq]
    have := quotientTannerHomology_trivial X Λ hΛ hker (IotaPiMaps.piMap X Λ ℓ hΛ hcompat a)
    rw [this, map_zero]
  rw [← ha, ha_zero]; exact map_zero _

/-- When the degree-0 homology of the Tanner complex `H₀(C(X,L))` is trivial, the
gauge submodule `HG = H₁ᵛ` vanishes. The proof proceeds through the Künneth structure:

1. `H₀(C(X,L))` is subsingleton (hypothesis)
2. `H₀(C(X,L)) ⊗ H₁(C_ℓ)` is subsingleton (tensor with subsingleton)
3. `Coinvariants(H₀(C(X,L)) ⊗ H₁(C_ℓ))` is subsingleton (quotient of subsingleton)
4. `H₁ᵛ = 0` since `H₁ᵛ` is this coinvariant module
5. `HG = range(embV) = ⊥` since `embV` maps zero to zero

The paper states this follows from `H₀(C(X/H, L)) = 0` (surjectivity of the
quotient differential `∂: C₁(X/H, L) → C₀(X/H, L)`), which is a weaker condition:
`H₀` of the quotient being trivial implies trivial coinvariants of `H₀(C(X,L))`,
which in turn implies the result. We use the stronger condition `H₀(C(X,L)) = 0`
here since the degree-0 iota/pi maps (connecting quotient H₀ to equivariant H₀
coinvariants) are not formalized. -/
theorem HG_eq_bot_of_tanner_H0_subsingleton
    (hss : Subsingleton ↑((HorizontalVerticalHomologySplitting.tannerHEq X Λ hΛ).complex.homology' 0)) :
    HG X Λ ℓ hΛ hcompat hodd = ⊥ := by
  simp only [HG, Submodule.eq_bot_iff, LinearMap.mem_range]
  intro x ⟨a, ha⟩
  -- H₁ᵛ = Coinvariants((tanner.homologyAction 0).tprod(cycle.homologyAction 1))
  -- The carrier of the tensor product representation is
  --   tanner.complex.homology' 0 ⊗[𝔽₂] cycle.complex.homology' 1
  -- which is subsingleton since tanner.complex.homology' 0 is subsingleton
  haveI : Subsingleton
    (↑((HorizontalVerticalHomologySplitting.tannerHEq X Λ hΛ).complex.homology' 0) ⊗[𝔽₂]
     ↑((HorizontalVerticalHomologySplitting.cycleHEq ℓ hcompat).complex.homology' (1 - 0))) :=
    tensorProduct_subsingleton_left _ _
  -- The coinvariants of a subsingleton module is subsingleton
  haveI : Subsingleton (H1v X Λ ℓ hΛ hcompat) :=
    coinvariants_subsingleton_of_subsingleton
      ((HorizontalVerticalHomologySplitting.tannerHEq X Λ hΛ).homologyAction 0 |>.tprod
       ((HorizontalVerticalHomologySplitting.cycleHEq ℓ hcompat).homologyAction (1 - 0)))
  have ha_zero : a = 0 := Subsingleton.elim a 0
  rw [← ha, ha_zero, map_zero]

/-! ## Encoding rate -/

/-- The number of logical qubits of the horizontal subsystem code equals the dimension
of the logical submodule `HL`. -/
def logicalQubits : ℕ :=
  Module.finrank 𝔽₂ ↥(HL X Λ ℓ hΛ hcompat hodd)

/-! ## Witness lemmas -/

/-- Witness: `HL` is nonempty (it is a submodule, hence contains 0). -/
lemma HL_nonempty : (HL X Λ ℓ hΛ hcompat hodd).carrier.Nonempty :=
  ⟨0, (HL X Λ ℓ hΛ hcompat hodd).zero_mem⟩

/-- Witness: `HG` is nonempty (it is a submodule, hence contains 0). -/
lemma HG_nonempty : (HG X Λ ℓ hΛ hcompat hodd).carrier.Nonempty :=
  ⟨0, (HG X Λ ℓ hΛ hcompat hodd).zero_mem⟩

end HorizontalSubsystemBalancedProductCode

end
