import MerLeanBpqc.Definitions.Def_10_TotalComplex
import MerLeanBpqc.Definitions.Def_1_ChainComplex
import MerLeanBpqc.Theorems.Thm_1_KunnethFormula
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Projection

/-!
# Theorem 2: Small Double Complex Homology

If `E` is a 2×2-double complex (meaning `E_{p,q} = 0` for all `(p,q) ∉ {0,1}²`),
then `H_n(Tot(E)) ≅ ⊕_{p+q=n} H_p(H_q(E_{•,•}, ∂^v), ∂̄^h)`.

## Main Results
- `SmallDC` — a concrete 2×2 double complex
- `homologyEquiv_n0` — isomorphism at degree 0
- `homologyEquiv_n2` — isomorphism at degree 2
- `homologyEquiv_n1` — isomorphism at degree 1
-/

open CategoryTheory LinearMap

noncomputable section

/-- A concrete 2×2 double complex over `𝔽₂`. -/
structure SmallDC where
  A₀₀ : Type*
  A₀₁ : Type*
  A₁₀ : Type*
  A₁₁ : Type*
  [inst₀₀ : AddCommGroup A₀₀] [mod₀₀ : Module 𝔽₂ A₀₀]
  [inst₀₁ : AddCommGroup A₀₁] [mod₀₁ : Module 𝔽₂ A₀₁]
  [inst₁₀ : AddCommGroup A₁₀] [mod₁₀ : Module 𝔽₂ A₁₀]
  [inst₁₁ : AddCommGroup A₁₁] [mod₁₁ : Module 𝔽₂ A₁₁]
  dv₀ : A₀₁ →ₗ[𝔽₂] A₀₀
  dv₁ : A₁₁ →ₗ[𝔽₂] A₁₀
  dh₀ : A₁₀ →ₗ[𝔽₂] A₀₀
  dh₁ : A₁₁ →ₗ[𝔽₂] A₀₁
  comm : dv₀.comp dh₁ = dh₀.comp dv₁

attribute [instance] SmallDC.inst₀₀ SmallDC.mod₀₀ SmallDC.inst₀₁ SmallDC.mod₀₁
attribute [instance] SmallDC.inst₁₀ SmallDC.mod₁₀ SmallDC.inst₁₁ SmallDC.mod₁₁

namespace SmallDC

variable (E : SmallDC)

/-! ## Total complex -/

def d₂ : E.A₁₁ →ₗ[𝔽₂] E.A₁₀ × E.A₀₁ := LinearMap.prod E.dv₁ E.dh₁
def d₁ : E.A₁₀ × E.A₀₁ →ₗ[𝔽₂] E.A₀₀ := LinearMap.coprod E.dh₀ E.dv₀

lemma d₂_fst (x : E.A₁₁) : (E.d₂ x).1 = E.dv₁ x := by
  have := LinearMap.ext_iff.mp (LinearMap.fst_prod E.dv₁ E.dh₁) x
  simpa [d₂, LinearMap.comp_apply, fst_apply] using this

lemma d₂_snd (x : E.A₁₁) : (E.d₂ x).2 = E.dh₁ x := by
  have := LinearMap.ext_iff.mp (LinearMap.snd_prod E.dv₁ E.dh₁) x
  simpa [d₂, LinearMap.comp_apply, snd_apply] using this

lemma d₁_comp_d₂ : E.d₁.comp E.d₂ = 0 := by
  ext x
  simp only [LinearMap.comp_apply, zero_apply, d₁, coprod_apply]
  rw [E.d₂_fst, E.d₂_snd]
  have := LinearMap.ext_iff.mp E.comm x
  simp only [LinearMap.comp_apply] at this
  rw [this]; exact ZModModule.add_self _

/-! ## Total complex homology types -/

def totH₀ := E.A₀₀ ⧸ range E.d₁
instance : AddCommGroup E.totH₀ := Submodule.Quotient.addCommGroup _
instance : Module 𝔽₂ E.totH₀ := Submodule.Quotient.module _

def totZ₁ : Submodule 𝔽₂ (E.A₁₀ × E.A₀₁) := ker E.d₁
def totB₁ : Submodule 𝔽₂ (E.A₁₀ × E.A₀₁) := range E.d₂

lemma totB₁_le_totZ₁ : E.totB₁ ≤ E.totZ₁ := by
  intro x hx; obtain ⟨y, rfl⟩ := mem_range.mp hx
  have h := LinearMap.ext_iff.mp E.d₁_comp_d₂ y
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  exact mem_ker.mpr h

def totB₁InZ₁ : Submodule 𝔽₂ ↥E.totZ₁ := E.totB₁.comap E.totZ₁.subtype

def totH₁ := ↥E.totZ₁ ⧸ E.totB₁InZ₁
instance : AddCommGroup E.totH₁ := Submodule.Quotient.addCommGroup _
instance : Module 𝔽₂ E.totH₁ := Submodule.Quotient.module _

def totH₂ := ↥(ker E.d₂)
instance : AddCommGroup E.totH₂ := Submodule.addCommGroup _
instance : Module 𝔽₂ E.totH₂ := Submodule.module _

/-! ## Vertical homology -/

abbrev vH₀₀ := E.A₀₀ ⧸ range E.dv₀

abbrev vH₁₀ := E.A₁₀ ⧸ range E.dv₁

abbrev vH₀₁ := ↥(ker E.dv₀)

abbrev vH₁₁ := ↥(ker E.dv₁)

/-! ## Induced horizontal differentials -/

lemma dh₀_maps_range : range E.dv₁ ≤ (range E.dv₀).comap E.dh₀ := by
  intro x hx; obtain ⟨z, rfl⟩ := mem_range.mp hx
  exact Submodule.mem_comap.mpr (mem_range.mpr ⟨E.dh₁ z, by
    have := LinearMap.ext_iff.mp E.comm z; simp only [LinearMap.comp_apply] at this; exact this⟩)

def barDh₀ : E.vH₁₀ →ₗ[𝔽₂] E.vH₀₀ := Submodule.mapQ _ _ E.dh₀ E.dh₀_maps_range

lemma dh₁_maps_ker (x : E.A₁₁) (hx : x ∈ ker E.dv₁) : E.dh₁ x ∈ ker E.dv₀ := by
  rw [mem_ker] at hx ⊢
  have := LinearMap.ext_iff.mp E.comm x; simp only [LinearMap.comp_apply] at this
  rw [this, hx, map_zero]

def barDh₁ : E.vH₁₁ →ₗ[𝔽₂] E.vH₀₁ :=
  LinearMap.codRestrict (ker E.dv₀) (E.dh₁.domRestrict (ker E.dv₁))
    (fun ⟨x, hx⟩ => E.dh₁_maps_ker x hx)

/-! ## Iterated homology types -/

def itH₀ := E.vH₀₀ ⧸ range E.barDh₀
instance : AddCommGroup E.itH₀ := Submodule.Quotient.addCommGroup _
instance : Module 𝔽₂ E.itH₀ := Submodule.Quotient.module _

def itH₂ := ↥(ker E.barDh₁)
instance : AddCommGroup E.itH₂ := Submodule.addCommGroup _
instance : Module 𝔽₂ E.itH₂ := Submodule.module _

def itH₁_fst := ↥(ker E.barDh₀)
instance : AddCommGroup E.itH₁_fst := Submodule.addCommGroup _
instance : Module 𝔽₂ E.itH₁_fst := Submodule.module _

def itH₁_snd := E.vH₀₁ ⧸ range E.barDh₁
instance : AddCommGroup E.itH₁_snd := Submodule.Quotient.addCommGroup _
instance : Module 𝔽₂ E.itH₁_snd := Submodule.Quotient.module _

/-! ## Isomorphism at degree 2 -/

lemma ker_d₂_eq : ker E.d₂ = ker E.dv₁ ⊓ ker E.dh₁ := by
  exact LinearMap.ker_prod E.dv₁ E.dh₁

lemma barDh₁_val (x : E.vH₁₁) :
    (E.barDh₁ x).val = E.dh₁ x.val := rfl

lemma barDh₁_ker_iff (x : E.vH₁₁) :
    x ∈ ker E.barDh₁ ↔ x.val ∈ ker E.dh₁ := by
  rw [mem_ker, mem_ker]
  constructor
  · intro h
    have : (E.barDh₁ x).val = (0 : E.vH₀₁).val := congr_arg Subtype.val h
    simp only [ZeroMemClass.coe_zero] at this
    rwa [E.barDh₁_val] at this
  · intro h
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero, E.barDh₁_val]; exact h

def homologyEquiv_n2 : E.totH₂ ≃ₗ[𝔽₂] E.itH₂ where
  toFun := fun ⟨x, hx⟩ =>
    ⟨⟨x, (Submodule.mem_inf.mp (E.ker_d₂_eq ▸ hx)).1⟩,
     (E.barDh₁_ker_iff _).mpr (Submodule.mem_inf.mp (E.ker_d₂_eq ▸ hx)).2⟩
  map_add' := fun ⟨_, _⟩ ⟨_, _⟩ => Subtype.ext (Subtype.ext rfl)
  map_smul' := fun _ ⟨_, _⟩ => Subtype.ext (Subtype.ext rfl)
  invFun := fun ⟨⟨x, hx_dv⟩, hx_dh⟩ =>
    ⟨x, E.ker_d₂_eq ▸ Submodule.mem_inf.mpr ⟨hx_dv, (E.barDh₁_ker_iff _).mp hx_dh⟩⟩
  left_inv := fun ⟨_, _⟩ => Subtype.ext rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ => Subtype.ext (Subtype.ext rfl)

/-! ## Isomorphism at degree 0 -/

lemma range_d₁_eq : range E.d₁ = range E.dh₀ ⊔ range E.dv₀ := by
  ext y; simp only [d₁, Submodule.mem_sup]; constructor
  · intro hy; obtain ⟨⟨a, b⟩, hab⟩ := mem_range.mp hy
    simp only [coprod_apply] at hab
    exact ⟨E.dh₀ a, mem_range.mpr ⟨a, rfl⟩, E.dv₀ b, mem_range.mpr ⟨b, rfl⟩, hab⟩
  · intro ⟨u, hu, v, hv, huv⟩
    obtain ⟨a, rfl⟩ := mem_range.mp hu; obtain ⟨b, rfl⟩ := mem_range.mp hv
    exact mem_range.mpr ⟨(a, b), by simp [coprod_apply, huv]⟩

lemma barDh₀_range_eq :
    range E.barDh₀ = (range E.dh₀ ⊔ range E.dv₀).map (range E.dv₀).mkQ := by
  ext y; constructor
  · intro hy; obtain ⟨a_cl, ha⟩ := mem_range.mp hy
    induction a_cl using Submodule.Quotient.induction_on with
    | H a =>
      exact Submodule.mem_map.mpr ⟨E.dh₀ a, Submodule.mem_sup_left (mem_range.mpr ⟨a, rfl⟩),
        by simp [barDh₀, Submodule.mapQ_apply] at ha; exact ha.symm ▸ rfl⟩
  · intro hy; obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a, rfl⟩ := mem_range.mp hu
    rw [← hzy, ← huv, map_add]
    have : (range E.dv₀).mkQ v = 0 := by
      rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero _).mpr hv
    have goal : E.dv₀.range.mkQ (E.dh₀ a) ∈ E.barDh₀.range := by
      exact mem_range.mpr ⟨Submodule.Quotient.mk a, by simp [barDh₀, Submodule.mapQ_apply]⟩
    rwa [this, add_zero]

def homologyEquiv_n0 : E.totH₀ ≃ₗ[𝔽₂] E.itH₀ :=
  (Submodule.quotEquivOfEq _ _ E.range_d₁_eq).trans
    ((Submodule.quotientQuotientEquivQuotient _ _ le_sup_right).symm.trans
      (Submodule.quotEquivOfEq _ _ E.barDh₀_range_eq.symm))

/-! ## Isomorphism at degree 1

We construct the isomorphism `H₁(Tot(E)) ≃ ker(barDh₀) × (vH₀₁ / range(barDh₁))`
via a short exact sequence that splits over 𝔽₂.

The short exact sequence is:
  0 → vH₀₁/range(barDh₁) →ⁱ totH₁ →^π ker(barDh₀) → 0
where i([b]) = [(0,b)] and π([(a,b)]) = [a].
Over 𝔽₂, this splits by `Submodule.exists_isCompl`.
-/

/-- The projection π: totZ₁ → vH₁₀ sending (a,b) ↦ [a]. -/
def piMap : ↥E.totZ₁ →ₗ[𝔽₂] E.vH₁₀ :=
  (range E.dv₁).mkQ.comp ((fst 𝔽₂ E.A₁₀ E.A₀₁).comp E.totZ₁.subtype)

/-- π lands in ker(barDh₀). -/
lemma piMap_mem_ker (z : E.totZ₁) : E.piMap z ∈ ker E.barDh₀ := by
  rw [mem_ker]
  obtain ⟨⟨a, b⟩, hab⟩ := z
  simp only [piMap, LinearMap.comp_apply, Submodule.coe_subtype, fst_apply]
  rw [totZ₁, mem_ker, d₁, coprod_apply] at hab
  simp only [barDh₀, Submodule.mapQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact mem_range.mpr ⟨b, by
    have h : E.dh₀ a + E.dv₀ b = 0 := hab
    have := eq_neg_of_add_eq_zero_left h
    rw [ZModModule.neg_eq_self] at this; exact this.symm⟩

/-- π lifted to land in ker(barDh₀) = itH₁_fst. -/
def piMap' : ↥E.totZ₁ →ₗ[𝔽₂] ↥(ker E.barDh₀) :=
  LinearMap.codRestrict (ker E.barDh₀) E.piMap E.piMap_mem_ker

/-- π vanishes on totB₁InZ₁, so it descends to totH₁. -/
lemma piMap'_vanishes_on_B₁ :
    E.totB₁InZ₁ ≤ ker E.piMap' := by
  intro ⟨v, hv_Z⟩ hv_B
  rw [mem_ker]; ext
  simp only [piMap', LinearMap.codRestrict_apply, piMap,
    LinearMap.comp_apply, Submodule.coe_subtype, fst_apply, ZeroMemClass.coe_zero]
  have hv_range : v ∈ range E.d₂ := Submodule.mem_comap.mp hv_B
  obtain ⟨x, rfl⟩ := mem_range.mp hv_range
  rw [E.d₂_fst]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (mem_range.mpr ⟨x, rfl⟩)

/-- π descended to totH₁ → itH₁_fst. -/
def piBar : E.totH₁ →ₗ[𝔽₂] E.itH₁_fst :=
  Submodule.liftQ E.totB₁InZ₁ E.piMap' E.piMap'_vanishes_on_B₁

/-- The inclusion ι: ker(dv₀) → totZ₁ sending b ↦ (0,b). -/
def iotaMap : ↥(ker E.dv₀) →ₗ[𝔽₂] ↥E.totZ₁ :=
  LinearMap.codRestrict E.totZ₁
    ((LinearMap.inr 𝔽₂ E.A₁₀ E.A₀₁).comp (ker E.dv₀).subtype)
    (fun ⟨b, hb⟩ => by
      show _ ∈ ker E.d₁
      rw [mem_ker, d₁, coprod_apply]
      simp only [LinearMap.comp_apply, Submodule.coe_subtype, inr_apply]
      rw [map_zero, zero_add]
      exact mem_ker.mp hb)

/-- ι vanishes on range(barDh₁). -/
lemma iotaMap_vanishes_on_barDh₁ :
    range E.barDh₁ ≤ ker (E.totB₁InZ₁.mkQ.comp E.iotaMap) := by
  intro v hv
  obtain ⟨⟨w, hw⟩, rfl⟩ := mem_range.mp hv
  rw [mem_ker, LinearMap.comp_apply]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  -- Need: iotaMap(barDh₁(⟨w, hw⟩)) ∈ totB₁InZ₁
  -- barDh₁(⟨w, hw⟩) = ⟨dh₁ w, _⟩ ∈ ker(dv₀)
  -- iotaMap(⟨dh₁ w, _⟩) = ⟨(0, dh₁ w), _⟩ ∈ totZ₁
  -- Need: (0, dh₁ w) ∈ range(d₂) = totB₁
  -- d₂(w) = (dv₁ w, dh₁ w). Since w ∈ ker(dv₁): dv₁ w = 0.
  -- So d₂(w) = (0, dh₁ w). ✓
  show E.iotaMap (E.barDh₁ ⟨w, hw⟩) ∈ E.totB₁InZ₁
  show _ ∈ E.totB₁.comap E.totZ₁.subtype
  rw [Submodule.mem_comap]
  show _ ∈ range E.d₂
  refine mem_range.mpr ⟨w, ?_⟩
  ext <;> simp only [iotaMap, barDh₁, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    Submodule.coe_subtype, inr_apply, LinearMap.domRestrict_apply]
  · rw [E.d₂_fst]; exact mem_ker.mp hw
  · rw [E.d₂_snd]

/-- ι descended to itH₁_snd = vH₀₁/range(barDh₁) → totH₁. -/
def iotaBar : E.itH₁_snd →ₗ[𝔽₂] E.totH₁ :=
  Submodule.liftQ (range E.barDh₁) (E.totB₁InZ₁.mkQ.comp E.iotaMap)
    E.iotaMap_vanishes_on_barDh₁

/-- Exactness: piBar ∘ iotaBar = 0. -/
lemma piBar_comp_iotaBar : E.piBar.comp E.iotaBar = 0 := by
  ext y
  induction y using Submodule.Quotient.induction_on with
  | H v =>
    obtain ⟨b, hb⟩ := v
    simp only [LinearMap.comp_apply, zero_apply]
    show E.piBar (E.iotaBar (Submodule.Quotient.mk ⟨b, hb⟩)) = 0
    -- Step 1: iotaBar(mk v) = mkQ(iotaMap v)
    have h1 : E.iotaBar (Submodule.Quotient.mk ⟨b, hb⟩) =
      E.totB₁InZ₁.mkQ (E.iotaMap ⟨b, hb⟩) := by unfold iotaBar; rfl
    rw [h1]
    -- Step 2: piBar(mkQ z) = piMap' z
    have h2 : E.piBar (E.totB₁InZ₁.mkQ (E.iotaMap ⟨b, hb⟩)) =
      E.piMap' (E.iotaMap ⟨b, hb⟩) := by unfold piBar; rfl
    rw [h2]
    -- piMap'(iotaMap(⟨b,hb⟩)) = 0 since piMap(iotaMap(⟨b,hb⟩)) = mkQ(fst(0,b)) = mkQ(0) = 0
    apply Subtype.ext
    simp only [ZeroMemClass.coe_zero]
    show (E.piMap (E.iotaMap ⟨b, hb⟩) : E.vH₁₀) = 0
    unfold piMap iotaMap
    simp [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.coe_subtype,
      inr_apply, fst_apply, map_zero]

/-- Helper: if (0,b) with b ∈ ker(dv₀) lies in range(d₂), then b ∈ range(barDh₁). -/
lemma mem_range_barDh₁_of_inr_mem_range_d₂ {b : E.A₀₁} (hb : b ∈ ker E.dv₀)
    (h : (0, b) ∈ range E.d₂) : (⟨b, hb⟩ : E.vH₀₁) ∈ range E.barDh₁ := by
  obtain ⟨w, hw⟩ := mem_range.mp h
  have h1 : E.dv₁ w = 0 := by
    have := congr_arg Prod.fst hw; simp only at this; rw [E.d₂_fst] at this; exact this
  have h2 : E.dh₁ w = b := by
    have := congr_arg Prod.snd hw; simp only at this; rw [E.d₂_snd] at this; exact this
  exact mem_range.mpr ⟨⟨w, mem_ker.mpr h1⟩, by
    ext; simp [barDh₁, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply, h2]⟩

/-- iotaBar is injective. -/
lemma iotaBar_injective : Function.Injective E.iotaBar := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  induction y using Submodule.Quotient.induction_on with
  | H v =>
    obtain ⟨b, hb⟩ := v
    rw [Submodule.Quotient.mk_eq_zero]
    -- hy says iotaBar([⟨b,hb⟩]) = 0 in totH₁
    have h0 : E.iotaBar (Submodule.Quotient.mk ⟨b, hb⟩) = 0 := mem_ker.mp hy
    -- iotaBar(mk v) = mkQ(iotaMap v)
    have h1 : E.iotaBar (Submodule.Quotient.mk ⟨b, hb⟩) =
      E.totB₁InZ₁.mkQ (E.iotaMap ⟨b, hb⟩) := by unfold iotaBar; rfl
    rw [h1, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    -- h0: iotaMap(⟨b,hb⟩) ∈ totB₁InZ₁ = totB₁.comap totZ₁.subtype
    have h0' : ((0 : E.A₁₀), b) ∈ range E.d₂ := by
      have := h0; unfold totB₁InZ₁ at this
      have hcomap := Submodule.mem_comap.mp this
      convert hcomap using 1
    exact E.mem_range_barDh₁_of_inr_mem_range_d₂ hb h0'

/-- piBar is surjective. -/
lemma piBar_surjective : Function.Surjective E.piBar := by
  intro ⟨q, hq⟩
  -- q ∈ ker(barDh₀) ⊆ vH₁₀ = A₁₀/range(dv₁)
  -- Lift q to some a ∈ A₁₀
  induction q using Submodule.Quotient.induction_on with
  | H a =>
    -- [a] ∈ ker(barDh₀) means dh₀(a) ∈ range(dv₀)
    rw [mem_ker] at hq
    simp only [barDh₀, Submodule.mapQ_apply, Submodule.mkQ_apply] at hq
    have hq' : E.dh₀ a ∈ range E.dv₀ := (Submodule.Quotient.mk_eq_zero _).mp hq
    obtain ⟨b, hb⟩ := mem_range.mp hq'
    -- dh₀(a) = dv₀(b), so dh₀(a) + dv₀(b) = 2·dv₀(b) = 0 over 𝔽₂
    have hab_ker : (a, b) ∈ ker E.d₁ := by
      rw [mem_ker, d₁, coprod_apply, hb]
      exact ZModModule.add_self _
    refine ⟨Submodule.Quotient.mk ⟨(a, b), hab_ker⟩, ?_⟩
    apply Subtype.ext
    -- Goal: ↑(E.piBar (mk ⟨(a,b), _⟩)) = Submodule.Quotient.mk a
    -- piBar(mk z) = piMap'(z), and piMap'(z).val = piMap(z) = mkQ(fst(z))
    have h1 : E.piBar (Submodule.Quotient.mk ⟨(a, b), hab_ker⟩) =
      E.piMap' ⟨(a, b), hab_ker⟩ := by unfold piBar; rfl
    rw [h1]
    show (E.piMap ⟨(a, b), hab_ker⟩ : E.vH₁₀) = Submodule.Quotient.mk a
    unfold piMap
    simp [LinearMap.comp_apply, Submodule.coe_subtype, fst_apply]

/-- ker(piBar) = range(iotaBar). -/
lemma piBar_ker_eq_iotaBar_range :
    ker E.piBar = range E.iotaBar := by
  ext ⟨z⟩
  simp only [mem_ker, mem_range]
  constructor
  · intro hz
    simp only [piBar, Submodule.liftQ_apply, piMap', LinearMap.codRestrict_apply,
      piMap, LinearMap.comp_apply, Submodule.coe_subtype, fst_apply] at hz
    have ha : (z : E.A₁₀ × E.A₀₁).1 ∈ range E.dv₁ := by
      have hval := congr_arg Subtype.val hz
      simp only [ZeroMemClass.coe_zero] at hval
      exact (Submodule.Quotient.mk_eq_zero _).mp hval
    obtain ⟨w, hw⟩ := mem_range.mp ha
    set ab := (z : E.A₁₀ × E.A₀₁)
    have hd₁_ab : E.d₁ ab = 0 := by
      have hz : (z : E.A₁₀ × E.A₀₁) ∈ ker E.d₁ := z.2
      exact mem_ker.mp hz
    set b' := ab.2 + E.dh₁ w
    have hb'_ker : b' ∈ ker E.dv₀ := by
      rw [mem_ker, map_add]
      have h1 : E.dh₀ ab.1 + E.dv₀ ab.2 = 0 := by
        simp only [d₁, coprod_apply] at hd₁_ab; exact hd₁_ab
      have h2 : E.dv₀ (E.dh₁ w) = E.dh₀ (E.dv₁ w) := by
        have := LinearMap.ext_iff.mp E.comm w; simp only [LinearMap.comp_apply] at this; exact this
      rw [h2, hw]
      have h3 := eq_neg_of_add_eq_zero_right h1
      rw [ZModModule.neg_eq_self] at h3; rw [h3]; exact ZModModule.add_self _
    -- We need to show [(0, b')] = [(a, b)] in totH₁, i.e., (a, b) - (0, b') ∈ totB₁InZ₁
    -- (a, b) - (0, b') = (a, b - b') = (a, -dh₁ w) = (dv₁ w, dh₁ w) = d₂(w) over 𝔽₂
    have h_diff : (z : ↥E.totZ₁) - E.iotaMap ⟨b', hb'_ker⟩ ∈ E.totB₁InZ₁ := by
      show _ ∈ E.totB₁.comap E.totZ₁.subtype
      rw [Submodule.mem_comap]
      show _ ∈ range E.d₂
      refine mem_range.mpr ⟨w, ?_⟩
      ext
      · -- Goal: (E.d₂ w).1 = (E.totZ₁.subtype (z - E.iotaMap ⟨b', hb'_ker⟩)).1
        rw [E.d₂_fst, map_sub, Prod.fst_sub]
        have : (E.totZ₁.subtype (E.iotaMap ⟨b', hb'_ker⟩)).1 = (0 : E.A₁₀) := by
          unfold iotaMap; simp [LinearMap.comp_apply, LinearMap.codRestrict_apply,
            Submodule.coe_subtype, inr_apply]
        rw [this, sub_zero]; exact hw
      · -- Goal: (E.d₂ w).2 = (E.totZ₁.subtype (z - E.iotaMap ⟨b', hb'_ker⟩)).2
        rw [E.d₂_snd, map_sub, Prod.snd_sub]
        have hiota : (E.totZ₁.subtype (E.iotaMap ⟨b', hb'_ker⟩)).2 = b' := by
          unfold iotaMap; simp [LinearMap.comp_apply, LinearMap.codRestrict_apply,
            Submodule.coe_subtype, inr_apply]
        rw [hiota]
        -- Goal: dh₁ w = ab.2 - b'
        show E.dh₁ w = ab.2 - b'
        simp only [b', sub_add_eq_sub_sub, sub_self, zero_sub]
        exact (ZModModule.neg_eq_self _).symm
    refine ⟨Submodule.Quotient.mk ⟨b', hb'_ker⟩, ?_⟩
    -- Goal: iotaBar(mk ⟨b', hb'_ker⟩) = mk z in totH₁
    -- iotaBar(mk v) = mkQ(iotaMap v)
    have h_iota : E.iotaBar (Submodule.Quotient.mk ⟨b', hb'_ker⟩) =
      E.totB₁InZ₁.mkQ (E.iotaMap ⟨b', hb'_ker⟩) := by unfold iotaBar; rfl
    rw [h_iota, Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq _).mpr (by
      have hneg : E.iotaMap ⟨b', hb'_ker⟩ - z = -(z - E.iotaMap ⟨b', hb'_ker⟩) := by abel
      rw [hneg]; exact neg_mem h_diff)
  · intro ⟨y, hy⟩
    rw [← hy]
    have := LinearMap.ext_iff.mp E.piBar_comp_iotaBar y
    simp only [LinearMap.comp_apply, zero_apply] at this; exact this

set_option maxHeartbeats 800000 in
/-- The isomorphism H₁(Tot) ≃ ker(barDh₀) × (vH₀₁ / im(barDh₁)).
    Constructed via a split short exact sequence over 𝔽₂:
    0 → itH₁_snd →^iotaBar totH₁ →^piBar itH₁_fst → 0
    which splits because 𝔽₂ is a field. -/
def homologyEquiv_n1 :
    E.totH₁ ≃ₗ[𝔽₂] E.itH₁_fst × E.itH₁_snd := by
  -- Over 𝔽₂ (a division ring), choose a complement K of range(iotaBar)
  let iotaRange := range E.iotaBar
  let K := (Submodule.exists_isCompl iotaRange).choose
  have hK : IsCompl iotaRange K := (Submodule.exists_isCompl iotaRange).choose_spec
  -- totH₁ ≃ range(iotaBar) × K
  let e1 := iotaRange.prodEquivOfIsCompl K hK
  -- range(iotaBar) ≃ itH₁_snd
  let e2 := LinearEquiv.ofInjective E.iotaBar E.iotaBar_injective
  -- K ≃ totH₁/range(iotaBar) via quotientEquivOfIsCompl
  let e3 := iotaRange.quotientEquivOfIsCompl K hK
  -- totH₁/range(iotaBar) = totH₁/ker(piBar)
  let e4 := Submodule.quotEquivOfEq _ _ E.piBar_ker_eq_iotaBar_range
  -- totH₁/ker(piBar) ≃ range(piBar)
  let e5 := E.piBar.quotKerEquivRange
  -- range(piBar) = ⊤
  have h_top : range E.piBar = ⊤ := LinearMap.range_eq_top.mpr E.piBar_surjective
  let e6 := LinearEquiv.ofTop _ h_top
  -- Compose: K ≃ itH₁_fst
  let eK : ↥K ≃ₗ[𝔽₂] E.itH₁_fst := e3.symm.trans (e4.symm.trans (e5.trans e6))
  -- Final: totH₁ ≃ iotaRange × K ≃ itH₁_snd × itH₁_fst ≃ itH₁_fst × itH₁_snd
  -- e2.symm : iotaRange ≃ itH₁_snd, eK : K ≃ itH₁_fst
  exact e1.symm.trans
    ((e2.symm.prodCongr eK).trans (LinearEquiv.prodComm 𝔽₂ E.itH₁_snd E.itH₁_fst))

end SmallDC

end
