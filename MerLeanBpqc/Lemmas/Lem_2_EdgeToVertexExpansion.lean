import MerLeanBpqc.Theorems.Cor_1_AlonChungContrapositive

/-!
# Lemma 2: Edge-to-Vertex Expansion

## Main Results
- `edgeToVertexExpansion`: For a finite, connected `s`-regular graph with second-largest
  eigenvalue `lam2`, if `|E| <= alpha|X1|` then `|Gamma(E)| >= beta|E|` where
  `beta = (sqrt(lam2^2 + 4s(s-lam2)alpha) - lam2) / (s(s-lam2)alpha)`.
-/

open SimpleGraph Fintype BigOperators Finset AlonChung AlonChungContrapositive GraphExpansion
open Real (sqrt)

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace EdgeToVertexExpansion

/-! ## The quadratic inverse gamma(at) -/

/-- The quadratic inverse: given `at`, solve `at = g^2 + (lam2/s)g(1-g)` for `g`.
Gives `g(at) = (sqrt(lam2^2 + 4s(s-lam2)at) - lam2) / (2(s-lam2))`. -/
noncomputable def gammaOfAlpha (s : ℝ) (lam2 : ℝ) (a : ℝ) : ℝ :=
  (sqrt (lam2 ^ 2 + 4 * s * (s - lam2) * a) - lam2) / (2 * (s - lam2))

/-- The expansion parameter `beta = 2*gamma(alpha)/(s*alpha)`. -/
noncomputable def betaParam (s : ℝ) (lam2 : ℝ) (a : ℝ) : ℝ :=
  (sqrt (lam2 ^ 2 + 4 * s * (s - lam2) * a) - lam2) / (s * (s - lam2) * a)

lemma betaParam_eq (s : ℝ) (lam2 : ℝ) (a : ℝ) (hs : s ≠ 0) (ha : a ≠ 0) :
    betaParam s lam2 a = 2 * gammaOfAlpha s lam2 a / (s * a) := by
  unfold betaParam gammaOfAlpha
  field_simp

/-! ## Discriminant positivity -/

lemma discriminant_nonneg (s : ℝ) (lam2 : ℝ) (a : ℝ)
    (hs : 0 < s) (hsl : lam2 < s) (ha : 0 ≤ a) :
    0 ≤ lam2 ^ 2 + 4 * s * (s - lam2) * a := by
  have h1 : 0 ≤ lam2 ^ 2 := sq_nonneg lam2
  have h2 : 0 < s - lam2 := sub_pos.mpr hsl
  have h3 : 0 ≤ 4 * s * (s - lam2) * a := by positivity
  linarith

/-! ## sqrt >= lam2 -/

lemma sqrt_ge_lam2 (s : ℝ) (lam2 : ℝ) (a : ℝ)
    (hs : 0 < s) (hsl : lam2 < s) (ha : 0 ≤ a) :
    lam2 ≤ sqrt (lam2 ^ 2 + 4 * s * (s - lam2) * a) := by
  by_cases hlam : 0 ≤ lam2
  · exact Real.le_sqrt_of_sq_le (by nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 4) hs.le) (sub_pos.mpr hsl).le) ha])
  · push_neg at hlam
    exact le_trans (le_of_lt hlam) (Real.sqrt_nonneg _)

/-! ## gammaOfAlpha is nonneg -/

lemma gammaOfAlpha_nonneg (s : ℝ) (lam2 : ℝ) (a : ℝ)
    (hs : 0 < s) (hsl : lam2 < s) (ha : 0 ≤ a) :
    0 ≤ gammaOfAlpha s lam2 a := by
  unfold gammaOfAlpha
  exact div_nonneg (sub_nonneg.mpr (sqrt_ge_lam2 s lam2 a hs hsl ha))
    (by linarith)

/-! ## gammaOfAlpha at zero -/

lemma gammaOfAlpha_zero (s : ℝ) (lam2 : ℝ)
    (_hs : 0 < s) (_hsl : lam2 < s) (hlam_nn : 0 ≤ lam2) :
    gammaOfAlpha s lam2 0 = 0 := by
  unfold gammaOfAlpha
  simp [mul_zero, add_zero, Real.sqrt_sq hlam_nn, sub_self]

/-! ## Concavity: gamma(at) * alpha >= gamma(alpha) * at for at <= alpha -/

lemma gammaOfAlpha_concavity (s : ℝ) (lam2 : ℝ) (alpha at_ : ℝ)
    (hs : 0 < s) (hsl : lam2 < s)
    (halpha : 0 < alpha) (hat_nn : 0 ≤ at_) (hat_le : at_ ≤ alpha) :
    gammaOfAlpha s lam2 alpha * at_ ≤ gammaOfAlpha s lam2 at_ * alpha := by
  -- Reduce to (sqrt(D) - lam2) * at_ <= (sqrt(Dt) - lam2) * alpha
  -- where D = lam2^2 + c*alpha, Dt = lam2^2 + c*at_, c = 4s(s-lam2)
  unfold gammaOfAlpha
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  rw [div_le_div_iff₀ (by linarith : 0 < 2 * (s - lam2))
    (by linarith : 0 < 2 * (s - lam2))]
  -- Need: (sqrt D - lam2) * at_ <= (sqrt Dt - lam2) * alpha
  -- Set u = sqrt Dt, v = sqrt D. Need (v - lam2)*at_ <= (u - lam2)*alpha
  -- This is equivalent to (u - lam2)(v - lam2) >= 0, see derivation in comments.
  set c := 4 * s * (s - lam2)
  set D := lam2 ^ 2 + c * alpha
  set Dt := lam2 ^ 2 + c * at_
  have hsl_pos : 0 < s - lam2 := sub_pos.mpr hsl
  have hc_pos : 0 < c := by show 0 < 4 * s * (s - lam2); nlinarith
  have hD_nn : 0 ≤ D := discriminant_nonneg s lam2 alpha hs hsl (le_of_lt halpha)
  have hDt_nn : 0 ≤ Dt := discriminant_nonneg s lam2 at_ hs hsl hat_nn
  set u := sqrt Dt
  set v := sqrt D
  have hu_nn : 0 ≤ u := Real.sqrt_nonneg _
  have hv_nn : 0 ≤ v := Real.sqrt_nonneg _
  have hu_ge : lam2 ≤ u := sqrt_ge_lam2 s lam2 at_ hs hsl hat_nn
  have hv_ge : lam2 ≤ v := sqrt_ge_lam2 s lam2 alpha hs hsl (le_of_lt halpha)
  have huv : u ≤ v := by
    apply Real.sqrt_le_sqrt
    show lam2 ^ 2 + c * at_ ≤ lam2 ^ 2 + c * alpha
    nlinarith [mul_le_mul_of_nonneg_left hat_le hc_pos.le]
  -- The key: (u - lam2)(v - lam2) >= 0
  have key : 0 ≤ (u - lam2) * (v - lam2) :=
    mul_nonneg (sub_nonneg.mpr hu_ge) (sub_nonneg.mpr hv_ge)
  -- We need (v - lam2) * at_ * (2*(s-lam2)) ≤ (u - lam2) * alpha * (2*(s-lam2))
  -- Since 2*(s-lam2) > 0, cancel it
  suffices h : (v - lam2) * at_ ≤ (u - lam2) * alpha by nlinarith
  have hvsq : v ^ 2 = lam2 ^ 2 + c * alpha := Real.sq_sqrt hD_nn
  have husq : u ^ 2 = lam2 ^ 2 + c * at_ := Real.sq_sqrt hDt_nn
  -- Decompose: (v-lam2)*at_ = (v-u)*at_ + (u-lam2)*at_
  -- Need: (v-u)*at_ ≤ (u-lam2)*(alpha-at_)
  -- Then: (v-lam2)*at_ = (v-u)*at_ + (u-lam2)*at_ ≤ (u-lam2)*(alpha-at_) + (u-lam2)*at_ = (u-lam2)*alpha
  suffices hvu : (v - u) * at_ ≤ (u - lam2) * (alpha - at_) by nlinarith
  -- Multiply both sides by (v+u) ≥ 0 (non-negative since u,v ≥ 0)
  have hvu_sum_nn : 0 ≤ v + u := by linarith
  -- (v-u)*(v+u) = v²-u² = c*(alpha-at_)
  have hvuvu : (v - u) * (v + u) = c * (alpha - at_) := by nlinarith
  -- (u-lam2)*(v+u) = u*v + u² - lam2*v - lam2*u
  -- c*at_ = u² - lam2²
  -- So need: at_*(v-u)*(v+u) ≤ (u-lam2)*(alpha-at_)*(v+u)
  -- i.e., at_*c*(alpha-at_) ≤ (u-lam2)*(v+u)*(alpha-at_)
  -- If alpha = at_, both sides are 0. Otherwise divide by (alpha-at_) > 0:
  -- at_*c ≤ (u-lam2)*(v+u)
  -- at_*c = u²-lam2² (from husq)
  -- (u-lam2)*(v+u) = u*v-lam2*v + u²-lam2*u = u*v-lam2*(v+u) + u²
  -- Need: u²-lam2² ≤ u*v-lam2*(v+u)+u²
  -- i.e., -lam2² ≤ u*v-lam2*(v+u) = u*v-lam2*u-lam2*v
  -- i.e., 0 ≤ u*v-lam2*u-lam2*v+lam2² = (u-lam2)*(v-lam2) = key ✓
  -- So the proof is: at_*c*(alpha-at_) ≤ (u-lam2)*(v+u)*(alpha-at_)
  -- which is (v-u)*at_*(v+u) ≤ (u-lam2)*(v+u)*(alpha-at_)
  -- and dividing by (v+u):  (v-u)*at_ ≤ (u-lam2)*(alpha-at_)
  -- For v+u > 0, this is clear. For v+u = 0, u=v=0 so v-u=0 and LHS=0.
  by_cases hvu_sum_pos : 0 < v + u
  · -- Show multiplied version and divide by v+u > 0
    suffices hmul : ((v - u) * at_) * (v + u) ≤ ((u - lam2) * (alpha - at_)) * (v + u) by
      exact le_of_mul_le_mul_right hmul hvu_sum_pos
    calc (v - u) * at_ * (v + u)
        = at_ * ((v - u) * (v + u)) := by ring
      _ = at_ * (c * (alpha - at_)) := by rw [hvuvu]
      _ = c * at_ * (alpha - at_) := by ring
      _ = (u ^ 2 - lam2 ^ 2) * (alpha - at_) := by nlinarith
      _ = (u - lam2) * (u + lam2) * (alpha - at_) := by ring
      _ ≤ (u - lam2) * (v + lam2) * (alpha - at_) := by
            -- u + lam2 ≤ v + lam2 since u ≤ v, mult by (u-lam2)≥0 and (alpha-at_)≥0
            have := sub_nonneg.mpr hu_ge  -- u - lam2 ≥ 0
            have := sub_nonneg.mpr hat_le -- alpha - at_ ≥ 0
            have := sub_nonneg.mpr huv    -- v - u ≥ 0
            nlinarith [mul_nonneg (sub_nonneg.mpr hu_ge) (sub_nonneg.mpr hat_le),
                       mul_nonneg (sub_nonneg.mpr huv) (mul_nonneg (sub_nonneg.mpr hu_ge) (sub_nonneg.mpr hat_le))]
      _ ≤ (u - lam2) * (alpha - at_) * (v + u) := by
            -- v + lam2 ≤ v + u since lam2 ≤ u (hu_ge), mult by (u-lam2)*(alpha-at_) ≥ 0
            nlinarith [mul_nonneg (sub_nonneg.mpr hu_ge) (sub_nonneg.mpr hat_le),
                       mul_nonneg (sub_nonneg.mpr hu_ge)
                         (mul_nonneg (sub_nonneg.mpr hat_le) (sub_nonneg.mpr hu_ge))]
  · -- v + u = 0, so v = u = 0 (both non-negative)
    have hvu0 : v + u = 0 := le_antisymm (by linarith) hvu_sum_nn
    have hu0 : u = 0 := by linarith
    have hv0 : v = 0 := by linarith
    have hlam_neg : lam2 ≤ 0 := by linarith [hu_ge]
    rw [hv0, hu0]; ring_nf
    nlinarith [mul_nonneg (neg_nonneg.mpr hlam_neg) (sub_nonneg.mpr hat_le)]

/-! ## Handshaking lemma -/

lemma edgeFinset_eq_half_sn (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hreg : G.IsRegularOfDegree s) :
    (G.edgeFinset.card : ℝ) = (s : ℝ) / 2 * (Fintype.card V : ℝ) := by
  have h := twice_card_edgeFinset_eq G s hreg
  linarith

/-! ## Step 2: Alon-Chung implies |Gamma(E)| >= gamma(at) * |V| -/

lemma incidentVertices_ge_gamma
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s) (hreg : G.IsRegularOfDegree s)
    (hcard : 2 ≤ Fintype.card V)
    (lam2 : ℝ) (hlam2 : lam2 = secondLargestEigenvalue G hcard)
    (hlam2_lt_s : lam2 < s)
    (E : Finset (Sym2 V)) (hE_sub : E ⊆ G.edgeFinset)
    (hE_ne : E.Nonempty) :
    (incidentVertices E).card ≥
      gammaOfAlpha s lam2 ((E.card : ℝ) / G.edgeFinset.card) * Fintype.card V := by
  -- Set S = Gamma(E), gamma' = |S|/|V|
  set S := incidentVertices E
  set n := (Fintype.card V : ℝ)
  have hn_pos : 0 < n := Nat.cast_pos.mpr (by omega)
  have hs_pos : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega)
  have hX1_pos : (0 : ℝ) < G.edgeFinset.card := by
    have : 0 < E.card := Finset.Nonempty.card_pos hE_ne
    have : E.card ≤ G.edgeFinset.card := Finset.card_le_card hE_sub
    exact Nat.cast_pos.mpr (by omega)
  -- S is nonempty since E is nonempty
  have hS_ne : S.Nonempty := by
    obtain ⟨e, he⟩ := hE_ne
    have he_edge := hE_sub he
    rw [SimpleGraph.mem_edgeFinset] at he_edge
    induction e using Sym2.ind with
    | h a b =>
    exact ⟨a, (mem_incidentVertices E a).mpr ⟨s(a, b), he, Sym2.mem_mk_left a b⟩⟩
  have hS_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.Nonempty.card_pos hS_ne)
  -- E subset inducedEdges G S
  have hE_ind : E ⊆ inducedEdges G S := subset_inducedEdges_incidentVertices G E hE_sub
  -- Case: S.card = Fintype.card V (gamma' = 1)
  by_cases hS_full : S.card = Fintype.card V
  · -- gamma(at) <= gamma(1) = 1, and |S| = n, so |S| >= gamma(at)*n
    -- Actually gammaOfAlpha <= 1 when at <= 1, and |S|/n = 1
    rw [ge_iff_le]
    calc gammaOfAlpha ↑s lam2 (↑E.card / ↑G.edgeFinset.card) * ↑(Fintype.card V)
        ≤ 1 * ↑(Fintype.card V) := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          -- gammaOfAlpha <= 1 when at <= 1
          unfold gammaOfAlpha
          rw [div_le_one (by linarith : 0 < 2 * (↑s - lam2))]
          -- sqrt(lam2^2 + 4s(s-lam2)*at) - lam2 <= 2(s - lam2)
          -- iff sqrt(...) <= 2s - lam2
          have hat_le_1 : (E.card : ℝ) / G.edgeFinset.card ≤ 1 :=
            div_le_one_of_le₀ (by exact_mod_cast Finset.card_le_card hE_sub) (le_of_lt hX1_pos)
          have hat_nn : 0 ≤ (E.card : ℝ) / G.edgeFinset.card :=
            div_nonneg (Nat.cast_nonneg _) (le_of_lt hX1_pos)
          -- sqrt(D_at) ≤ sqrt(D_1) ≤ 2s - lam2
          have hD_mono : lam2 ^ 2 + 4 * ↑s * (↑s - lam2) *
              ((E.card : ℝ) / ↑G.edgeFinset.card) ≤ lam2 ^ 2 + 4 * ↑s * (↑s - lam2) * 1 := by
            have := sub_pos.mpr hlam2_lt_s
            nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 4 * ↑s) this.le)
              (sub_nonneg.mpr hat_le_1)]
          have hD1_le : lam2 ^ 2 + 4 * ↑s * (↑s - lam2) * 1 ≤ (2 * ↑s - lam2) ^ 2 := by
            nlinarith
          have hrhs_nn : (0 : ℝ) ≤ 2 * ↑s - lam2 := by nlinarith
          have h1 := Real.sqrt_le_sqrt hD_mono
          have h2 := (Real.sqrt_le_left hrhs_nn).mpr hD1_le
          linarith
      _ = ↑(Fintype.card V) := one_mul _
      _ = ↑S.card := by rw [hS_full]
  · -- S.card < Fintype.card V
    have hS_lt : S.card < Fintype.card V := by
      have := Finset.card_le_card (Finset.subset_univ S)
      rw [Finset.card_univ] at this; omega
    -- Apply Alon-Chung to S
    have hAC := alonChung G s hs hreg hcard S hS_ne hS_lt
    -- |E| <= |inducedEdges G S| <= alpha(gamma')|X1|
    have hE_card : (E.card : ℝ) ≤ (inducedEdges G S).card :=
      by exact_mod_cast Finset.card_le_card hE_ind
    set gamma' := (S.card : ℝ) / n
    -- at = |E|/|X1| <= alpha(gamma')
    have hat_le_agamma : (E.card : ℝ) / G.edgeFinset.card ≤
        gamma' ^ 2 + (secondLargestEigenvalue G hcard / ↑s) * gamma' * (1 - gamma') := by
      rw [div_le_iff₀ hX1_pos]
      exact le_trans hE_card hAC
    -- The alpha function is monotone (from alpha_mono), so gamma(at) <= gamma'
    -- But we need to invert: gamma is the inverse of alpha
    -- Actually we need: gammaOfAlpha(at) <= gamma'
    -- This follows from: at <= alpha(gamma') and alpha is increasing
    -- and gammaOfAlpha is the inverse of alpha on [0,1]
    -- For now, use a direct approach: bound |S| from below
    -- |S| = gamma' * n, need gamma(at) * n <= |S| = gamma' * n
    -- i.e., gamma(at) <= gamma'
    -- gamma(at) = (sqrt(lam2^2 + 4s(s-lam2)*at) - lam2) / (2(s-lam2))
    -- at <= alpha(gamma') = gamma'^2 + (lam2/s)*gamma'*(1-gamma') = (1-lam2/s)*gamma'^2 + (lam2/s)*gamma'
    -- Need to show: at <= alpha(gamma') implies gamma(at) <= gamma'
    -- i.e., gamma is the inverse of alpha
    -- Sufficient: sqrt(lam2^2 + 4s(s-lam2)*at) <= lam2 + 2(s-lam2)*gamma'
    -- iff lam2^2 + 4s(s-lam2)*at <= (lam2 + 2(s-lam2)*gamma')^2
    -- = lam2^2 + 4(s-lam2)*lam2*gamma' + 4(s-lam2)^2*gamma'^2
    -- iff 4s(s-lam2)*at <= 4(s-lam2)*gamma'*(lam2 + (s-lam2)*gamma')
    -- iff s*at <= gamma'*(lam2 + (s-lam2)*gamma')
    -- = lam2*gamma' + (s-lam2)*gamma'^2
    -- = s*gamma'^2 + lam2*gamma'*(1-gamma') = s*alpha(gamma')
    -- So s*at <= s*alpha(gamma') iff at <= alpha(gamma'). True! ✓
    rw [ge_iff_le]
    suffices h : gammaOfAlpha ↑s lam2 ((E.card : ℝ) / ↑G.edgeFinset.card) ≤ gamma' by
      calc gammaOfAlpha ↑s lam2 (↑E.card / ↑G.edgeFinset.card) * ↑(Fintype.card V)
          = gammaOfAlpha ↑s lam2 (↑E.card / ↑G.edgeFinset.card) * n := rfl
        _ ≤ gamma' * n := by exact mul_le_mul_of_nonneg_right h (le_of_lt hn_pos)
        _ = ↑S.card := by
          show (↑S.card / n) * n = ↑S.card
          rw [div_mul_cancel₀ _ (ne_of_gt hn_pos)]
    -- Show gammaOfAlpha(at) <= gamma'
    unfold gammaOfAlpha
    rw [div_le_iff₀ (by linarith : 0 < 2 * (↑s - lam2))]
    -- sqrt(lam2^2 + 4s(s-lam2)*at) <= lam2 + 2(s-lam2)*gamma'
    have hgamma'_pos : 0 < gamma' := div_pos hS_pos hn_pos
    have hgamma'_lt_1 : gamma' < 1 := by
      rw [show gamma' = (↑S.card : ℝ) / n from rfl, div_lt_one hn_pos]
      exact Nat.cast_lt.mpr hS_lt
    -- From at > 0 and at ≤ alpha(gamma'), we get alpha(gamma') > 0
    -- which gives lam2 + (s-lam2)*gamma' > 0, hence lam2 + 2*(s-lam2)*gamma' > 0
    have hat_pos_here : (0 : ℝ) < E.card / G.edgeFinset.card := div_pos
      (Nat.cast_pos.mpr (Finset.Nonempty.card_pos hE_ne)) hX1_pos
    rw [← hlam2] at hat_le_agamma
    have halpha_pos : 0 < gamma' ^ 2 + lam2 / ↑s * gamma' * (1 - gamma') := by
      linarith
    have hsl_pos' : 0 < (↑s : ℝ) - lam2 := sub_pos.mpr hlam2_lt_s
    have hrhs_pos : 0 < lam2 + 2 * (↑s - lam2) * gamma' := by
      -- alpha(gamma') > 0 means gamma' + (lam2/s)*(1-gamma') > 0
      -- i.e., s*gamma' + lam2 - lam2*gamma' > 0 (mult by s > 0)
      -- i.e., lam2 + (s-lam2)*gamma' > 0
      -- plus (s-lam2)*gamma' > 0 gives result
      have h1 : 0 < lam2 + (↑s - lam2) * gamma' := by
        have h2 : 0 < gamma' ^ 2 + lam2 / ↑s * gamma' * (1 - gamma') := halpha_pos
        -- gamma'^2 + (lam2/s)*gamma'*(1-gamma') = gamma'*(gamma' + (lam2/s)*(1-gamma'))
        -- > 0, and gamma' > 0, so gamma' + (lam2/s)*(1-gamma') > 0
        have h3 : 0 < gamma' + lam2 / ↑s * (1 - gamma') := by
          by_contra h_neg
          push_neg at h_neg
          nlinarith [sq_nonneg gamma', mul_nonpos_of_nonneg_of_nonpos hgamma'_pos.le h_neg]
        have h4 : 0 < ↑s * (gamma' + lam2 / ↑s * (1 - gamma')) := mul_pos hs_pos h3
        have h5 : ↑s * (gamma' + lam2 / ↑s * (1 - gamma')) =
            lam2 + (↑s - lam2) * gamma' := by field_simp; ring
        linarith
      nlinarith [mul_pos hsl_pos' hgamma'_pos]
    rw [sub_le_iff_le_add, show gamma' * (2 * (↑s - lam2)) + lam2 =
        lam2 + 2 * (↑s - lam2) * gamma' by ring]
    rw [← Real.sqrt_sq (le_of_lt hrhs_pos)]
    apply Real.sqrt_le_sqrt
    -- lam2^2 + 4s(s-lam2)*at <= (lam2 + 2(s-lam2)*gamma')^2
    have h_expand : (lam2 + 2 * (↑s - lam2) * gamma') ^ 2 =
        lam2 ^ 2 + 4 * (↑s - lam2) * lam2 * gamma' + 4 * (↑s - lam2) ^ 2 * gamma' ^ 2 := by
      ring
    rw [h_expand]
    -- Need: 4*s*(s-lam2)*at <= 4*(s-lam2)*lam2*gamma' + 4*(s-lam2)^2*gamma'^2
    -- i.e., s*at <= lam2*gamma' + (s-lam2)*gamma'^2 = s*(gamma'^2 + (lam2/s)*gamma'*(1-gamma'))
    -- which follows from at <= alpha(gamma')
    -- Need: 4*s*(s-lam2)*at ≤ 4*(s-lam2)*lam2*gamma' + 4*(s-lam2)^2*gamma'^2
    -- = 4*(s-lam2)*(lam2*gamma' + (s-lam2)*gamma'^2)
    -- = 4*(s-lam2)*(s*gamma'^2 + lam2*gamma'*(1-gamma'))
    -- = 4*(s-lam2)*s*(gamma'^2 + (lam2/s)*gamma'*(1-gamma'))
    -- ≥ 4*(s-lam2)*s*at  by hat_le_agamma
    have key : ↑s * (↑(#E) / ↑(#G.edgeFinset)) ≤
        ↑s * (gamma' ^ 2 + lam2 / ↑s * gamma' * (1 - gamma')) :=
      mul_le_mul_of_nonneg_left hat_le_agamma (Nat.cast_nonneg _)
    -- s*(gamma'^2 + (lam2/s)*gamma'*(1-gamma'))
    -- = s*gamma'^2 + lam2*gamma'*(1-gamma')
    -- = lam2*gamma' + (s-lam2)*gamma'^2
    have expand : ↑s * (gamma' ^ 2 + lam2 / ↑s * gamma' * (1 - gamma')) =
        lam2 * gamma' + (↑s - lam2) * gamma' ^ 2 := by field_simp; ring
    nlinarith [mul_nonneg hsl_pos'.le (Nat.cast_nonneg (α := ℝ) s)]

/-! ## Main theorem -/

theorem edgeToVertexExpansion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s) (hreg : G.IsRegularOfDegree s)
    (hcard : 2 ≤ Fintype.card V)
    (lam2 : ℝ) (hlam2 : lam2 = secondLargestEigenvalue G hcard)
    (hlam2_lt_s : lam2 < s)
    (alpha : ℝ) (halpha_pos : 0 < alpha) (_halpha_le : alpha ≤ 1)
    (E : Finset (Sym2 V)) (hE_sub : E ⊆ G.edgeFinset)
    (hE_le : (E.card : ℝ) ≤ alpha * G.edgeFinset.card) :
    ((incidentVertices E).card : ℝ) ≥ betaParam s lam2 alpha * E.card := by
  -- Edge case: E = empty
  by_cases hE_empty : E = ∅
  · simp [hE_empty]
  have hE_ne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE_empty
  have hE_pos : (0 : ℝ) < E.card := Nat.cast_pos.mpr (Finset.Nonempty.card_pos hE_ne)
  have hX1_pos : (0 : ℝ) < G.edgeFinset.card := by
    have := Finset.Nonempty.card_pos hE_ne
    have := Finset.card_le_card hE_sub; exact Nat.cast_pos.mpr (by omega)
  have hs_pos : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega)
  set n := (Fintype.card V : ℝ)
  have hn_pos : 0 < n := Nat.cast_pos.mpr (by omega)
  set at_ := (E.card : ℝ) / G.edgeFinset.card
  have hat_pos : 0 < at_ := div_pos hE_pos hX1_pos
  have hat_le : at_ ≤ alpha := by
    show (E.card : ℝ) / G.edgeFinset.card ≤ alpha; rwa [div_le_iff₀ hX1_pos]
  -- Step 2: |Gamma(E)| >= gamma(at) * n
  have h_step2 : ((incidentVertices E).card : ℝ) ≥ gammaOfAlpha s lam2 at_ * n :=
    incidentVertices_ge_gamma G s hs hreg hcard lam2 hlam2 hlam2_lt_s E hE_sub hE_ne
  -- Step 3: concavity: gamma(at) >= (gamma(alpha)/alpha) * at
  have h_step3 : gammaOfAlpha s lam2 alpha * at_ ≤ gammaOfAlpha s lam2 at_ * alpha :=
    gammaOfAlpha_concavity s lam2 alpha at_ hs_pos hlam2_lt_s halpha_pos hat_pos.le hat_le
  -- Combined: |Gamma(E)| >= gamma(at)*n >= (gamma(alpha)/alpha)*at*n
  -- = (gamma(alpha)/alpha) * (|E|/|X1|) * n
  -- Step 5: at * n = |E| * (2/s) by handshaking
  have hX1_eq : (G.edgeFinset.card : ℝ) = ↑s / 2 * n := edgeFinset_eq_half_sn G s hreg
  -- at * n = (|E| / |X1|) * n = |E| * n / |X1| = |E| * n / (s/2 * n) = |E| * 2 / s
  have hat_n : at_ * n = (E.card : ℝ) * 2 / ↑s := by
    show (E.card : ℝ) / G.edgeFinset.card * ↑(Fintype.card V) = (E.card : ℝ) * 2 / ↑s
    rw [hX1_eq]; field_simp; ring
  -- So |Gamma(E)| >= (gamma(alpha)/alpha) * at * n = (2*gamma(alpha)/(s*alpha)) * |E| = beta * |E|
  rw [ge_iff_le]
  rw [betaParam_eq s lam2 alpha (ne_of_gt hs_pos) (ne_of_gt halpha_pos)]
  -- beta * |E| = 2 * gamma(alpha) / (s * alpha) * |E|
  -- = gamma(alpha) / alpha * (2/s) * |E|
  -- = gamma(alpha) / alpha * at * n  (since at*n = 2|E|/s)
  -- <= gamma(at) * n (by concavity)
  -- <= |Gamma(E)|
  have hsl_pos : 0 < (↑s : ℝ) - lam2 := sub_pos.mpr hlam2_lt_s
  calc 2 * gammaOfAlpha ↑s lam2 alpha / (↑s * alpha) * ↑E.card
      = gammaOfAlpha ↑s lam2 alpha / alpha * (↑E.card * 2 / ↑s) := by ring
    _ = gammaOfAlpha ↑s lam2 alpha / alpha * (at_ * n) := by rw [hat_n]
    _ = (gammaOfAlpha ↑s lam2 alpha * at_) / alpha * n := by ring
    _ ≤ (gammaOfAlpha ↑s lam2 at_ * alpha) / alpha * n := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hn_pos)
        exact div_le_div_of_nonneg_right h_step3 (le_of_lt halpha_pos)
    _ = gammaOfAlpha ↑s lam2 at_ * n := by field_simp
    _ ≤ ↑(incidentVertices E).card := h_step2

end EdgeToVertexExpansion
