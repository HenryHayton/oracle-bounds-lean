import OracleBounds.Attacks.Localise

/-!
# Localisation with one bisection per coordinate (Algorithm L2)

**Statements reviewed and signed off by the administrator (2026-09-20); note the known-margin hypothesis `t + c ≤ ⟨x0,g⟩`**

Noiseless oracle `x ↦ [⟨x, g⟩ > t]`, unit template `g`, launch point `x0` with a *known margin*
`⟨x0, g⟩ ≥ a₀ := t + c > t`, orthonormal completion `u₀ … u_m` of `x0` (`dim = m + 2`).

* Circle `0` (`θ ↦ cos θ·x0 + sin θ·u₀`) is treated as in `L0`: both arc ends are bisected
  (`k_a` steps each) and `â ≈ ⟨x0, g⟩`, `b̂₀ ≈ ⟨u₀, g⟩` are read off.
* On every other circle `j = 1 … m` a single query at `θ = w₀ := arccos(t/a₀)` selects the arc end
  at angular distance `≥ w₀` from `0` (it exists because the half-width `w_j ≥ w₀`); that end is
  bisected once (`k` steps) inside the bracket `[w₀, Θ₀]`, `Θ₀ := arccos a₀ + arccos t`, and
  `b̂_j := (t − â cos θ̂_j)/sin θ̂_j`.

Query count, visible from the definition: `Q_loc2 = 2 k_a + m (1 + k)` with
`k = ⌈log₂((Θ₀ − w₀)/η)⌉`, `k_a = ⌈log₂(2 arccos t / η_a)⌉`, where, with `d = m + 2`,
`s₀ = min(sin w₀, sin Θ₀)`, `e = ε/((1+ε)√d)`: `η = (d−1) s₀ e / d`, `δ = s₀ e / d`,
`η_a = t δ / 4`.  Guarantee (`L2_correct`): `‖ĝ − g‖ ≤ ε`.
-/

namespace OracleBounds.Attacks

open Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Algorithm L2.** `u 0` is the `a`-circle, `u (succ j)` the one-sided circles. -/
noncomputable def L2 (m : ℕ) (t ε c : ℝ) (x0 : E) (u : Fin (m + 1) → E) (orc : E → Bool) : E :=
  let a₀ := t + c
  let w₀ := Real.arccos (t / a₀)
  let Θ₀ := Real.arccos a₀ + Real.arccos t
  let s₀ := min (Real.sin w₀) (Real.sin Θ₀)
  let e := ε / ((1 + ε) * Real.sqrt (m + 2))
  let η := (m + 1) * s₀ * e / (m + 2)
  let δ := s₀ * e / (m + 2)
  let ηa := t * δ / 4
  let Θ := 2 * Real.arccos t
  let k := ⌈Real.logb 2 ((Θ₀ - w₀) / η)⌉₊
  let ka := ⌈Real.logb 2 (Θ / ηa)⌉₊
  let f : Fin (m + 1) → ℝ → Bool := fun j θ => orc (Real.cos θ • x0 + Real.sin θ • u j)
  -- circle 0: both ends, as in L0
  let θp := (bisect (f 0) ka 0 Θ).1
  let θm := (bisect (f 0) ka 0 (-Θ)).1
  let â := t / Real.cos ((θp - θm) / 2) * Real.cos ((θp + θm) / 2)
  let b₀ := t / Real.cos ((θp - θm) / 2) * Real.sin ((θp + θm) / 2)
  -- circles 1 … m: one side query, one bisection
  let θh : Fin m → ℝ := fun j =>
    if f j.succ w₀ then (bisect (f j.succ) k w₀ Θ₀).1 else (bisect (f j.succ) k (-w₀) (-Θ₀)).1
  let b : Fin (m + 1) → ℝ :=
    Fin.cases b₀ (fun j => (t - â * Real.cos (θh j)) / Real.sin (θh j))
  let g' : E := â • x0 + ∑ j, b j • u j
  ‖g'‖⁻¹ • g'

/-! ### Helper lemmas -/

lemma bisect_mem_uIcc (f : ℝ → Bool) : ∀ (k : ℕ) (a b : ℝ),
    (bisect f k a b).1 ∈ Set.uIcc a b := by
  intro k
  induction k with
  | zero => intro a b; simp [bisect]
  | succ k ih =>
    intro a b
    have hmid : (a + b) / 2 ∈ Set.uIcc a b := by
      rcases le_total a b with h | h
      · rw [Set.uIcc_of_le h]; constructor <;> linarith
      · rw [Set.uIcc_of_ge h]; constructor <;> linarith
    simp only [bisect]
    split_ifs
    · exact Set.uIcc_subset_uIcc hmid Set.right_mem_uIcc (ih _ _)
    · exact Set.uIcc_subset_uIcc Set.left_mem_uIcc hmid (ih _ _)

/-- Non-strict version of `bisect_down`: the crossing `c` may sit at the loud end `a`. -/
lemma bisect_down' (f : ℝ → Bool) (c : ℝ) : ∀ (k : ℕ) (a b : ℝ),
    (∀ θ, b ≤ θ → θ ≤ a → (f θ = true ↔ c < θ)) → c ≤ a → b ≤ c →
    c ≤ (bisect f k a b).1 ∧ (bisect f k a b).2 ≤ c ∧
      (bisect f k a b).1 - (bisect f k a b).2 = (a - b) / 2 ^ k := by
  intro k
  induction k with
  | zero => intro a b _ hac hcb; simp [bisect, hac, hcb]
  | succ k ih =>
    intro a b hf hac hcb
    have hab : b ≤ a := by linarith
    simp only [bisect]
    split_ifs with h
    · have hm : c < (a + b) / 2 := (hf _ (by linarith) (by linarith)).1 h
      obtain ⟨h1, h2, h3⟩ := ih ((a + b) / 2) b
        (fun θ h1 h2 => hf θ h1 (by linarith)) hm.le hcb
      refine ⟨h1, h2, ?_⟩
      rw [h3, pow_succ]; field_simp; ring
    · have hm : (a + b) / 2 ≤ c := by
        by_contra hc; push Not at hc
        exact h ((hf _ (by linarith) (by linarith)).2 hc)
      obtain ⟨h1, h2, h3⟩ := ih a ((a + b) / 2)
        (fun θ h1 h2 => hf θ (by linarith) h2) hac hm
      refine ⟨h1, h2, ?_⟩
      rw [h3, pow_succ]; field_simp; ring

/-- On `[w₀, Θ₀] ⊆ [0, π]`, `sin` is at least its value at the nearer endpoint. -/
lemma sin_ge_min {w₀ Θ₀ θ : ℝ} (hw : 0 ≤ w₀) (hΘ : Θ₀ ≤ Real.pi) (h1 : w₀ ≤ θ) (h2 : θ ≤ Θ₀) :
    min (Real.sin w₀) (Real.sin Θ₀) ≤ Real.sin θ := by
  rcases le_or_gt θ (Real.pi / 2) with h | h
  · refine (min_le_left _ _).trans ?_
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h h1
  · refine (min_le_right _ _).trans ?_
    rw [← Real.sin_pi_sub θ, ← Real.sin_pi_sub Θ₀]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

/-- Error propagation through the one-sided read-off `b̂ = (t − â cos θ̂)/sin θ̂`. -/
lemma crossing_err {t a â b θ θh η δ s₀ : ℝ}
    (hcross : a * Real.cos θ + b * Real.sin θ = t)
    (hlip : |(a * Real.cos θ + b * Real.sin θ) - (a * Real.cos θh + b * Real.sin θh)| ≤ η)
    (hâ : |â - a| ≤ δ) (hs : s₀ ≤ |Real.sin θh|) (hs0 : 0 < s₀) :
    |(t - â * Real.cos θh) / Real.sin θh - b| ≤ (δ + η) / s₀ := by
  have hsin : Real.sin θh ≠ 0 := by
    intro h; rw [h, abs_zero] at hs; linarith
  have key : (t - â * Real.cos θh) / Real.sin θh - b =
      ((a - â) * Real.cos θh +
        ((a * Real.cos θ + b * Real.sin θ) - (a * Real.cos θh + b * Real.sin θh))) /
        Real.sin θh := by
    rw [← hcross]; field_simp; ring
  rw [key, abs_div, div_le_div_iff₀ (abs_pos.mpr hsin) hs0]
  have h1 : |(a - â) * Real.cos θh| ≤ δ := by
    rw [abs_mul, abs_sub_comm]
    calc |â - a| * |Real.cos θh| ≤ δ * 1 :=
          mul_le_mul hâ (Real.abs_cos_le_one _) (abs_nonneg _) (by linarith [abs_nonneg (â - a)])
      _ = δ := mul_one δ
  have h2 := abs_add_le ((a - â) * Real.cos θh)
    ((a * Real.cos θ + b * Real.sin θ) - (a * Real.cos θh + b * Real.sin θh))
  have h3 : 0 ≤ |(a - â) * Real.cos θh +
      ((a * Real.cos θ + b * Real.sin θ) - (a * Real.cos θh + b * Real.sin θh))| := abs_nonneg _
  nlinarith

/-- Sharper normalisation bound: if `‖v − g‖ ≤ r < 1` and `‖g‖ = 1` then
`‖v/‖v‖ − g‖² ≤ r²/(1 − r)`. -/
lemma norm_normalise_sub_sharp (v g : E) (hg : ‖g‖ = 1) (r : ℝ) (hr : ‖v - g‖ ≤ r) (hr1 : r < 1) :
    ‖‖v‖⁻¹ • v - g‖ ^ 2 ≤ r ^ 2 / (1 - r) := by
  have hn : 1 - r ≤ ‖v‖ := by
    have := abs_norm_sub_norm_le g v
    rw [norm_sub_rev, hg] at this
    linarith [(abs_le.mp (this.trans hr)).2]
  have hn0 : 0 < ‖v‖ := by linarith
  have hvv : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
  have hgg : inner ℝ g g = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hg]; norm_num
  have hvg : ‖v - g‖ ^ 2 = ‖v‖ ^ 2 - 2 * inner ℝ v g + 1 := by
    rw [@norm_sub_sq_real, hg]; ring
  have hr2 : ‖v‖ ^ 2 - 2 * inner ℝ v g + 1 ≤ r ^ 2 := by
    rw [← hvg]; exact pow_le_pow_left₀ (norm_nonneg _) hr 2
  have hd : ‖‖v‖⁻¹ • v - g‖ ^ 2 = 2 - 2 * inner ℝ v g / ‖v‖ := by
    rw [@norm_sub_sq_real, norm_smul, inner_smul_left, hg, norm_inv, norm_norm]
    simp only [RCLike.conj_to_real]
    field_simp
    ring
  rw [hd, le_div_iff₀ (by linarith)]
  have h3 : 2 - 2 * inner ℝ v g / ‖v‖ ≤ r ^ 2 / ‖v‖ := by
    have e : 2 - 2 * inner ℝ v g / ‖v‖ = (2 * ‖v‖ - 2 * inner ℝ v g) / ‖v‖ := by
      field_simp
    rw [e, div_le_div_iff_of_pos_right hn0]
    nlinarith [sq_nonneg (‖v‖ - 1)]
  calc (2 - 2 * inner ℝ v g / ‖v‖) * (1 - r) ≤ r ^ 2 / ‖v‖ * ‖v‖ :=
        mul_le_mul h3 hn (by linarith) (by positivity)
    _ = r ^ 2 := by field_simp

/-- Arc structure with the bounds that depend on a known lower bound `a₀ ≤ a`. With
`R = t / cos w`: `a = R cos φ`, `b = R sin φ`, the loud arc is `(φ − w, φ + w)`,
`arccos(t/a₀) ≤ w ≤ arccos t`, `|φ| ≤ arccos a₀`, and `θ ↦ a cos θ + b sin θ` is `1`-Lipschitz. -/
lemma arc_structure2 {t a₀ a b : ℝ} (ht : 0 < t) (hta : t < a₀) (ha₀ : a₀ ≤ a)
    (hab : a ^ 2 + b ^ 2 ≤ 1) :
    ∃ φ w : ℝ, t ≤ Real.cos w ∧ t / Real.cos w * Real.cos φ = a ∧
      t / Real.cos w * Real.sin φ = b ∧
      0 < φ + w ∧ φ - w < 0 ∧
      Real.arccos (t / a₀) ≤ w ∧ w ≤ Real.arccos t ∧ |φ| ≤ Real.arccos a₀ ∧
      a * Real.cos (φ + w) + b * Real.sin (φ + w) = t ∧
      a * Real.cos (φ - w) + b * Real.sin (φ - w) = t ∧
      (∀ θ, 0 ≤ θ → θ ≤ 2 * Real.arccos t →
        (t < a * Real.cos θ + b * Real.sin θ ↔ θ < φ + w)) ∧
      (∀ θ, -(2 * Real.arccos t) ≤ θ → θ ≤ 0 →
        (t < a * Real.cos θ + b * Real.sin θ ↔ φ - w < θ)) ∧
      (∀ x y, |(a * Real.cos x + b * Real.sin x) - (a * Real.cos y + b * Real.sin y)| ≤ |x - y|) := by
  have hta' : t < a := hta.trans_le ha₀
  have ha : 0 < a := ht.trans hta'
  have ha₀0 : 0 < a₀ := ht.trans hta
  set R := Real.sqrt (a ^ 2 + b ^ 2) with hR
  have hRa : a ≤ R := by
    rw [hR]; exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hR0 : 0 < R := ha.trans_le hRa
  have hR1 : R ≤ 1 := by rw [hR]; exact Real.sqrt_le_one.mpr hab
  have hRsq : R ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  set φ := Real.arctan (b / a) with hφ
  have hsq : Real.sqrt (1 + (b / a) ^ 2) = R / a := by
    rw [← Real.sqrt_sq (div_nonneg hR0.le ha.le)]
    congr 1; rw [div_pow, div_pow, hRsq]; field_simp
  have hcφ : R * Real.cos φ = a := by
    rw [hφ, Real.cos_arctan, hsq]; field_simp
  have hsφ : R * Real.sin φ = b := by
    rw [hφ, Real.sin_arctan, hsq]; field_simp
  have htR : t / R < 1 := by rw [div_lt_one hR0]; linarith
  have htR0 : 0 < t / R := by positivity
  set w := Real.arccos (t / R) with hw
  have hcw : Real.cos w = t / R := Real.cos_arccos (by linarith) htR.le
  have hw0 : 0 < w := Real.arccos_pos.mpr htR
  have hwpi2 : w < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr htR0
  have hwt : w ≤ Real.arccos t := Real.arccos_le_arccos (by
    rw [le_div_iff₀ hR0]; nlinarith)
  have hat : Real.arccos t < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr ht
  have hφw : |φ| < w := by
    by_contra hc; push Not at hc
    have hφpi : |φ| ≤ Real.pi := by
      rw [abs_le]; constructor
      · linarith [Real.neg_pi_div_two_lt_arctan (b / a), Real.pi_pos]
      · linarith [Real.arctan_lt_pi_div_two (b / a), Real.pi_pos]
    have := Real.cos_le_cos_of_nonneg_of_le_pi hw0.le hφpi hc
    rw [Real.cos_abs, hcw] at this
    have : a ≤ t := by
      have h2 : R * Real.cos φ ≤ R * (t / R) := mul_le_mul_of_nonneg_left this hR0.le
      rw [hcφ, mul_div_cancel₀ _ hR0.ne'] at h2; exact h2
    linarith
  have hφ1 := (abs_lt.mp hφw).1
  have hφ2 := (abs_lt.mp hφw).2
  have hosc : ∀ θ, a * Real.cos θ + b * Real.sin θ = R * Real.cos (θ - φ) := by
    intro θ; rw [Real.cos_sub, ← hcφ, ← hsφ]; ring
  have hiff : ∀ θ, t < a * Real.cos θ + b * Real.sin θ ↔ Real.cos w < Real.cos (θ - φ) := by
    intro θ; rw [hosc, hcw, div_lt_iff₀ hR0, mul_comm]
  have htcw : t / Real.cos w = R := by rw [hcw]; field_simp
  -- the new exports
  have hw₀ : Real.arccos (t / a₀) ≤ w := by
    rw [hw]; apply Real.arccos_le_arccos
    exact div_le_div_of_nonneg_left ht.le ha₀0 (ha₀.trans hRa)
  have hφa₀ : |φ| ≤ Real.arccos a₀ := by
    have hcosφ : a₀ ≤ Real.cos φ := by
      have : Real.cos φ = a / R := by rw [← hcφ]; field_simp
      rw [this, le_div_iff₀ hR0]; nlinarith
    have hφpi : |φ| ≤ Real.pi := by linarith [abs_nonneg φ, Real.pi_pos]
    calc |φ| = Real.arccos (Real.cos |φ|) := (Real.arccos_cos (abs_nonneg _) hφpi).symm
      _ = Real.arccos (Real.cos φ) := by rw [Real.cos_abs]
      _ ≤ Real.arccos a₀ := Real.arccos_le_arccos hcosφ
  have hcross_up : a * Real.cos (φ + w) + b * Real.sin (φ + w) = t := by
    rw [hosc, add_sub_cancel_left, hcw]; field_simp
  have hcross_down : a * Real.cos (φ - w) + b * Real.sin (φ - w) = t := by
    rw [hosc, sub_sub_cancel_left, Real.cos_neg, hcw]; field_simp
  have hlip : ∀ x y, |(a * Real.cos x + b * Real.sin x) - (a * Real.cos y + b * Real.sin y)|
      ≤ |x - y| := by
    intro x y
    rw [hosc, hosc, ← mul_sub, abs_mul, abs_of_pos hR0]
    calc R * |Real.cos (x - φ) - Real.cos (y - φ)| ≤ 1 * |(x - φ) - (y - φ)| :=
          mul_le_mul hR1 (Real.abs_cos_sub_cos_le _ _) (abs_nonneg _) zero_le_one
      _ = |x - y| := by rw [one_mul]; congr 1; ring
  refine ⟨φ, w, ?_, ?_, ?_, by linarith, by linarith, hw₀, hwt, hφa₀, hcross_up, hcross_down,
    ?_, ?_, hlip⟩
  · rw [hcw, le_div_iff₀ hR0]; nlinarith
  · rw [htcw, hcφ]
  · rw [htcw, hsφ]
  · intro θ h0 hΘ
    rw [hiff]
    constructor
    · intro h
      by_contra hc; push Not at hc
      have := cos_le_of_mem hw0.le (x := θ - φ) (by linarith) (by linarith)
      linarith
    · intro h
      exact cos_lt_of_abs (by linarith [Real.pi_pos]) (abs_lt.mpr ⟨by linarith, by linarith⟩)
  · intro θ h0 hΘ
    rw [hiff]
    constructor
    · intro h
      by_contra hc; push Not at hc
      have := cos_le_of_mem hw0.le (x := -(θ - φ)) (by linarith) (by linarith)
      rw [Real.cos_neg] at this
      linarith
    · intro h
      exact cos_lt_of_abs (by linarith [Real.pi_pos]) (abs_lt.mpr ⟨by linarith, by linarith⟩)

/-- Circle `0`: both ends bisected, `â`, `b̂₀` read off as in `L0`. -/
lemma circle0_est {t a b Θ ηa : ℝ} (f : ℝ → Bool) (ka : ℕ) (φ w : ℝ)
    (ht : 0 < t) (ht1 : t < 1) (hηa0 : 0 < ηa) (hηat : ηa ≤ t / 2)
    (hka : ka = ⌈Real.logb 2 (Θ / ηa)⌉₊)
    (hcw : t ≤ Real.cos w) (ha : t / Real.cos w * Real.cos φ = a)
    (hb : t / Real.cos w * Real.sin φ = b)
    (h1 : 0 < φ + w) (h2 : φ + w ≤ Θ) (h3 : -Θ ≤ φ - w) (h4 : φ - w < 0)
    (hup : ∀ θ, 0 ≤ θ → θ ≤ Θ → (f θ = true ↔ θ < φ + w))
    (hdown : ∀ θ, -Θ ≤ θ → θ ≤ 0 → (f θ = true ↔ φ - w < θ)) :
    |t / Real.cos (((bisect f ka 0 Θ).1 - (bisect f ka 0 (-Θ)).1) / 2) *
        Real.cos (((bisect f ka 0 Θ).1 + (bisect f ka 0 (-Θ)).1) / 2) - a| ≤ 4 * ηa / t ∧
    |t / Real.cos (((bisect f ka 0 Θ).1 - (bisect f ka 0 (-Θ)).1) / 2) *
        Real.sin (((bisect f ka 0 Θ).1 + (bisect f ka 0 (-Θ)).1) / 2) - b| ≤ 4 * ηa / t := by
  have hΘ0 : 0 < Θ := by linarith
  have hkb : Θ / 2 ^ ka ≤ ηa := by rw [hka]; exact ceil_bound hΘ0 hηa0
  set θp := (bisect f ka 0 Θ).1 with hθp
  set θm := (bisect f ka 0 (-Θ)).1 with hθm
  have hp : |θp - (φ + w)| ≤ ηa := by
    obtain ⟨q1, q2, q3⟩ := bisect_up f (φ + w) ka 0 Θ hup h1 h2
    rw [sub_zero] at q3
    rw [abs_le]; constructor <;> linarith
  have hmn : |θm - (φ - w)| ≤ ηa := by
    obtain ⟨q1, q2, q3⟩ := bisect_down f (φ - w) ka 0 (-Θ) hdown h4 h3
    rw [sub_neg_eq_add, zero_add] at q3
    rw [abs_le]; constructor <;> linarith
  have hφ : |(θp + θm) / 2 - φ| ≤ ηa := by
    have e : (θp + θm) / 2 - φ = ((θp - (φ + w)) + (θm - (φ - w))) / 2 := by ring
    rw [e, abs_div, abs_two]
    linarith [abs_add_le (θp - (φ + w)) (θm - (φ - w))]
  have hw : |Real.cos ((θp - θm) / 2) - Real.cos w| ≤ ηa := by
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    have e : (θp - θm) / 2 - w = ((θp - (φ + w)) - (θm - (φ - w))) / 2 := by ring
    rw [e, abs_div, abs_two]
    linarith [abs_sub (θp - (φ + w)) (θm - (φ - w))]
  constructor
  · rw [← ha]
    exact ratio_err ht ht1 hηa0.le hηat hcw hw (Real.abs_cos_le_one _)
      ((Real.abs_cos_sub_cos_le _ _).trans hφ)
  · rw [← hb]
    exact ratio_err ht ht1 hηa0.le hηat hcw hw (Real.abs_sin_le_one _)
      ((Real.abs_sin_sub_sin_le _ _).trans hφ)

/-- One-sided circle: side query at `w₀`, one bisection, read-off through `â`. -/
lemma circle_est {t a b â δ η w₀ Θ₀ s₀ : ℝ} (f : ℝ → Bool) (k : ℕ) (φ w : ℝ)
    (hw₀0 : 0 ≤ w₀) (hw₀Θ : w₀ < Θ₀) (hΘ₀pi : Θ₀ ≤ Real.pi) (hΘ₀t : Θ₀ ≤ 2 * Real.arccos t)
    (hs₀ : s₀ = min (Real.sin w₀) (Real.sin Θ₀)) (hs₀0 : 0 < s₀)
    (hη0 : 0 < η) (hk : k = ⌈Real.logb 2 ((Θ₀ - w₀) / η)⌉₊)
    (hâ : |â - a| ≤ δ)
    (hw₀w : w₀ ≤ w) (hwt : w ≤ Real.arccos t) (A : ℝ) (hΘ₀A : Θ₀ = A + Real.arccos t)
    (hφ : |φ| ≤ A)
    (hcross_up : a * Real.cos (φ + w) + b * Real.sin (φ + w) = t)
    (hcross_down : a * Real.cos (φ - w) + b * Real.sin (φ - w) = t)
    (hup : ∀ θ, 0 ≤ θ → θ ≤ 2 * Real.arccos t → (f θ = true ↔ θ < φ + w))
    (hdown : ∀ θ, -(2 * Real.arccos t) ≤ θ → θ ≤ 0 → (f θ = true ↔ φ - w < θ))
    (hlip : ∀ x y, |(a * Real.cos x + b * Real.sin x) - (a * Real.cos y + b * Real.sin y)|
      ≤ |x - y|) :
    |(t - â * Real.cos (if f w₀ = true then (bisect f k w₀ Θ₀).1
        else (bisect f k (-w₀) (-Θ₀)).1)) /
      Real.sin (if f w₀ = true then (bisect f k w₀ Θ₀).1 else (bisect f k (-w₀) (-Θ₀)).1) - b|
      ≤ (δ + η) / s₀ := by
  have hkb : (Θ₀ - w₀) / 2 ^ k ≤ η := by rw [hk]; exact ceil_bound (by linarith) hη0
  have hφ1 : -(Θ₀ - Real.arccos t) ≤ φ := by rw [hΘ₀A]; linarith [(abs_le.mp hφ).1]
  have hφ2 : φ ≤ Θ₀ - Real.arccos t := by rw [hΘ₀A]; linarith [(abs_le.mp hφ).2]
  split_ifs with hside
  · have hlt : w₀ < φ + w := (hup w₀ hw₀0 (by linarith)).1 hside
    have hle : φ + w ≤ Θ₀ := by linarith
    obtain ⟨q1, q2, q3⟩ := bisect_up f (φ + w) k w₀ Θ₀
      (fun θ h1 h2 => hup θ (by linarith) (by linarith)) hlt hle
    have hmem := bisect_mem_uIcc f k w₀ Θ₀
    rw [Set.uIcc_of_le hw₀Θ.le] at hmem
    set lo := (bisect f k w₀ Θ₀).1 with hlo
    have hsin : s₀ ≤ |Real.sin lo| := by
      rw [hs₀]
      exact (sin_ge_min hw₀0 hΘ₀pi hmem.1 hmem.2).trans (le_abs_self _)
    have hdist : |(φ + w) - lo| ≤ η := by
      rw [abs_le]; constructor <;> linarith
    exact crossing_err hcross_up ((hlip _ _).trans hdist) hâ hsin hs₀0
  · have hnlt : ¬ (w₀ < φ + w) := fun h => hside ((hup w₀ hw₀0 (by linarith)).2 h)
    have hle : φ - w ≤ -w₀ := by push Not at hnlt; linarith
    have hge : -Θ₀ ≤ φ - w := by linarith
    obtain ⟨q1, q2, q3⟩ := bisect_down' f (φ - w) k (-w₀) (-Θ₀)
      (fun θ h1 h2 => hdown θ (by linarith) (by linarith)) hle hge
    have hmem := bisect_mem_uIcc f k (-w₀) (-Θ₀)
    rw [Set.uIcc_of_ge (by linarith)] at hmem
    set lo := (bisect f k (-w₀) (-Θ₀)).1 with hlo
    have hsin : s₀ ≤ |Real.sin lo| := by
      rw [hs₀, ← abs_neg, ← Real.sin_neg]
      exact (sin_ge_min hw₀0 hΘ₀pi (by linarith [hmem.2]) (by linarith [hmem.1])).trans
        (le_abs_self _)
    have e3 : (-w₀ - -Θ₀) = Θ₀ - w₀ := by ring
    rw [e3] at q3
    have hdist : |(φ - w) - lo| ≤ η := by
      rw [abs_le]; constructor <;> linarith
    exact crossing_err hcross_down ((hlip _ _).trans hdist) hâ hsin hs₀0

/-- Assembly and normalisation: per-coordinate errors `≤ e = ε/((1+ε)√d)` give `‖ĝ − g‖ ≤ ε`. -/
lemma assembly2 (m : ℕ) (hdim : Module.finrank ℝ E = m + 1 + 1)
    (x0 : E) (u : Fin (m + 1) → E) (hON : Orthonormal ℝ (Fin.cons x0 u : Fin (m + 1 + 1) → E))
    (g : E) (hg : ‖g‖ = 1) (ε : ℝ) (hε : 0 < ε) (â : ℝ) (b : Fin (m + 1) → ℝ) (e : ℝ)
    (he : e = ε / ((1 + ε) * Real.sqrt ((m : ℝ) + 2)))
    (hâ : |â - inner ℝ x0 g| ≤ e) (hb : ∀ j, |b j - inner ℝ (u j) g| ≤ e) :
    ‖‖â • x0 + ∑ j, b j • u j‖⁻¹ • (â • x0 + ∑ j, b j • u j) - g‖ ≤ ε := by
  set g' : E := â • x0 + ∑ j, b j • u j with hg'def
  have he0 : 0 ≤ e := by rw [he]; positivity
  -- orthonormality facts
  have hx0 : inner ℝ x0 x0 = (1 : ℝ) := by
    have := hON.1 0
    simp only [Fin.cons_zero] at this
    rw [real_inner_self_eq_norm_sq, this]; norm_num
  have hx0u : ∀ j, inner ℝ x0 (u j) = (0 : ℝ) := by
    intro j
    have := hON.2 (Fin.succ_ne_zero j).symm
    simpa using this
  have hu : Orthonormal ℝ u := by
    have h := hON.comp Fin.succ (Fin.succ_injective _)
    have e : (Fin.cons x0 u : Fin (m + 1 + 1) → E) ∘ Fin.succ = u := by
      funext j; simp
    rwa [e] at h
  have hux0 : ∀ j, inner ℝ (u j) x0 = (0 : ℝ) := by
    intro j; rw [real_inner_comm]; exact hx0u j
  have hg'x : inner ℝ x0 (g' - g) = â - inner ℝ x0 g := by
    simp only [hg'def, inner_sub_right, inner_add_right, inner_smul_right, hx0, inner_sum, hx0u,
      mul_zero, Finset.sum_const_zero, add_zero, mul_one]
  have hg'u : ∀ i, inner ℝ (u i) (g' - g) = b i - inner ℝ (u i) g := by
    intro i
    simp only [hg'def, inner_sub_right, inner_add_right, inner_smul_right, hux0, mul_zero, zero_add]
    rw [hu.inner_right_fintype]
  have hnorm : ‖g' - g‖ ^ 2 ≤ ((m : ℝ) + 2) * e ^ 2 := by
    rw [parseval_cons (m + 1) hdim x0 u hON, hg'x]
    simp only [hg'u]
    have h1 : (â - inner ℝ x0 g) ^ 2 ≤ e ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hâ 2
    have h2 : ∑ j, (b j - inner ℝ (u j) g) ^ 2 ≤ ∑ _j : Fin (m + 1), e ^ 2 :=
      Finset.sum_le_sum (fun j _ => by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb j) 2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    push_cast at h2
    linarith
  have hr : ‖g' - g‖ ≤ ε / (1 + ε) := by
    have hsq : Real.sqrt ((m : ℝ) + 2) * e = ε / (1 + ε) := by
      rw [he]; field_simp
    rw [← hsq, ← Real.sqrt_sq (norm_nonneg (g' - g)), ← Real.sqrt_sq (by positivity : 0 ≤ e),
      ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hnorm
  have hr1 : ε / (1 + ε) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have key := norm_normalise_sub_sharp g' g hg (ε / (1 + ε)) hr hr1
  have hrhs : (ε / (1 + ε)) ^ 2 / (1 - ε / (1 + ε)) ≤ ε ^ 2 := by
    have e2 : (ε / (1 + ε)) ^ 2 / (1 - ε / (1 + ε)) = ε ^ 2 / (1 + ε) := by
      field_simp; ring
    rw [e2, div_le_iff₀ (by positivity)]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).mp (key.trans hrhs)

/-- **L2 localisation.** From a launch point with known margin `⟨x0, g⟩ ≥ t + c`, `L2` returns
an `ε`-approximation of `g` using `2 k_a + m (1 + k)` oracle calls. -/
theorem L2_correct (m : ℕ) (hdim : Module.finrank ℝ E = m + 1 + 1)
    (x0 : E) (u : Fin (m + 1) → E) (hON : Orthonormal ℝ (Fin.cons x0 u : Fin (m + 1 + 1) → E))
    (g : E) (hg : ‖g‖ = 1) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (c : ℝ) (hc : 0 < c) (hc1 : t + c < 1) (hx0 : t + c ≤ inner ℝ x0 g)
    (ε : ℝ) (hε : 0 < ε) :
    ‖L2 m t ε c x0 u (fun x => decide (t < inner ℝ x g)) - g‖ ≤ ε := by
  -- geometry of the true coefficients
  have hpars := parseval_cons (m + 1) hdim x0 u hON g
  rw [hg] at hpars
  have hab : ∀ j, inner ℝ x0 g ^ 2 + inner ℝ (u j) g ^ 2 ≤ 1 := by
    intro j
    have := Finset.single_le_sum (f := fun j => inner ℝ (u j) g ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    nlinarith
  unfold L2
  dsimp only
  -- constants
  set a₀ := t + c with ha₀
  have hta₀ : t < a₀ := by rw [ha₀]; linarith
  have ha₀1 : a₀ < 1 := hc1
  have ha₀0 : 0 < a₀ := ht.trans hta₀
  have hat : Real.arccos t < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr ht
  have hat0 : 0 < Real.arccos t := Real.arccos_pos.mpr ht1
  have haa₀ : 0 < Real.arccos a₀ := Real.arccos_pos.mpr ha₀1
  have haa₀2 : Real.arccos a₀ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr ha₀0
  have haa₀t : Real.arccos a₀ ≤ Real.arccos t := Real.arccos_le_arccos hta₀.le
  have hta₀1 : t / a₀ < 1 := by rw [div_lt_one ha₀0]; exact hta₀
  have hta₀0 : 0 < t / a₀ := by positivity
  have htta₀ : t ≤ t / a₀ := by rw [le_div_iff₀ ha₀0]; nlinarith
  set w₀ := Real.arccos (t / a₀) with hw₀
  have hw₀0 : 0 < w₀ := Real.arccos_pos.mpr hta₀1
  have hw₀pi2 : w₀ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr hta₀0
  have hw₀t : w₀ ≤ Real.arccos t := Real.arccos_le_arccos htta₀
  set Θ₀ := Real.arccos a₀ + Real.arccos t with hΘ₀
  have hΘ₀pi : Θ₀ ≤ Real.pi := by linarith
  have hΘ₀0 : 0 < Θ₀ := by linarith
  have hw₀Θ : w₀ < Θ₀ := by linarith
  have hΘ₀t : Θ₀ ≤ 2 * Real.arccos t := by linarith
  set s₀ := min (Real.sin w₀) (Real.sin Θ₀) with hs₀
  have hs₀0 : 0 < s₀ := lt_min
    (Real.sin_pos_of_pos_of_lt_pi hw₀0 (by linarith [Real.pi_pos]))
    (Real.sin_pos_of_pos_of_lt_pi hΘ₀0 (by linarith))
  have hs₀1 : s₀ ≤ 1 := (min_le_left _ _).trans (Real.sin_le_one _)
  have hsqrt : 1 ≤ Real.sqrt ((m : ℝ) + 2) := by
    rw [Real.one_le_sqrt]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  set e := ε / ((1 + ε) * Real.sqrt ((m : ℝ) + 2)) with he
  have he0 : 0 < e := by positivity
  have he1 : e < 1 := by
    rw [he, div_lt_one (by positivity)]
    nlinarith
  have hm2 : (1 : ℝ) ≤ (m : ℝ) + 2 := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  set η := ((m : ℝ) + 1) * s₀ * e / ((m : ℝ) + 2) with hη
  set δ := s₀ * e / ((m : ℝ) + 2) with hδ
  set ηa := t * δ / 4 with hηa
  set Θ := 2 * Real.arccos t with hΘ
  have hη0 : 0 < η := by rw [hη]; positivity
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδe : δ ≤ e := by
    rw [hδ, div_le_iff₀ (by positivity)]; nlinarith
  have hδη : (δ + η) / s₀ = e := by
    rw [hδ, hη]; field_simp; ring
  have hηa0 : 0 < ηa := by rw [hηa]; positivity
  have hηat : ηa ≤ t / 2 := by
    rw [hηa]; nlinarith
  have h4ηa : 4 * ηa / t = δ := by rw [hηa]; field_simp
  -- arc structure on every circle
  choose φ w hcw ha hb h1 h2 hw₀w hwt hφ hcup hcdown hup hdown hlip using
    fun j => arc_structure2 ht hta₀ hx0 (hab j)
  have hf : ∀ (j : Fin (m + 1)) θ,
      decide (t < inner ℝ (Real.cos θ • x0 + Real.sin θ • u j) g) = true ↔
      t < inner ℝ x0 g * Real.cos θ + inner ℝ (u j) g * Real.sin θ := by
    intro j θ
    simp only [decide_eq_true_eq, inner_add_left, real_inner_smul_left]
    constructor <;> intro h <;> linarith
  -- circle 0
  have h0 := circle0_est (fun θ => decide (t < inner ℝ (Real.cos θ • x0 + Real.sin θ • u 0) g))
    ⌈Real.logb 2 (Θ / ηa)⌉₊ (φ 0) (w 0) ht ht1 hηa0 hηat rfl (hcw 0) (ha 0) (hb 0) (h1 0)
    (by have := (abs_le.mp (hφ 0)).2; linarith [hwt 0])
    (by have := (abs_le.mp (hφ 0)).1; linarith [hwt 0]) (h2 0)
    (fun θ a b => (hf 0 θ).trans (hup 0 θ a b))
    (fun θ a b => (hf 0 θ).trans (hdown 0 θ a b))
  rw [h4ηa] at h0
  refine assembly2 m hdim x0 u hON g hg ε hε _ _ e he ?_ ?_
  · exact h0.1.trans hδe
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [Fin.cases_zero]
      exact h0.2.trans hδe
    · rw [Fin.cases_succ]
      rw [← hδη]
      exact circle_est
        (fun θ => decide (t < inner ℝ (Real.cos θ • x0 + Real.sin θ • u j.succ) g))
        ⌈Real.logb 2 ((Θ₀ - w₀) / η)⌉₊ (φ j.succ) (w j.succ) hw₀0.le hw₀Θ hΘ₀pi hΘ₀t rfl hs₀0
        hη0 rfl h0.1 (hw₀w j.succ) (hwt j.succ) (Real.arccos a₀) rfl (hφ j.succ)
        (hcup j.succ) (hcdown j.succ)
        (fun θ a b => (hf j.succ θ).trans (hup j.succ θ a b))
        (fun θ a b => (hf j.succ θ).trans (hdown j.succ θ a b)) (hlip j.succ)

/-! ### Sub-unit targets (paper note `random-search-general-prior` §6.3, Lemma 1) -/

/-- The unnormalised vector `g' = â x0 + ∑ b_j u_j` computed inside `L2`. -/
noncomputable def L2raw (m : ℕ) (t ε c : ℝ) (x0 : E) (u : Fin (m + 1) → E) (orc : E → Bool) : E :=
  let a₀ := t + c
  let w₀ := Real.arccos (t / a₀)
  let Θ₀ := Real.arccos a₀ + Real.arccos t
  let s₀ := min (Real.sin w₀) (Real.sin Θ₀)
  let e := ε / ((1 + ε) * Real.sqrt (m + 2))
  let η := (m + 1) * s₀ * e / (m + 2)
  let δ := s₀ * e / (m + 2)
  let ηa := t * δ / 4
  let Θ := 2 * Real.arccos t
  let k := ⌈Real.logb 2 ((Θ₀ - w₀) / η)⌉₊
  let ka := ⌈Real.logb 2 (Θ / ηa)⌉₊
  let f : Fin (m + 1) → ℝ → Bool := fun j θ => orc (Real.cos θ • x0 + Real.sin θ • u j)
  -- circle 0: both ends, as in L0
  let θp := (bisect (f 0) ka 0 Θ).1
  let θm := (bisect (f 0) ka 0 (-Θ)).1
  let â := t / Real.cos ((θp - θm) / 2) * Real.cos ((θp + θm) / 2)
  let b₀ := t / Real.cos ((θp - θm) / 2) * Real.sin ((θp + θm) / 2)
  -- circles 1 … m: one side query, one bisection
  let θh : Fin m → ℝ := fun j =>
    if f j.succ w₀ then (bisect (f j.succ) k w₀ Θ₀).1 else (bisect (f j.succ) k (-w₀) (-Θ₀)).1
  let b : Fin (m + 1) → ℝ :=
    Fin.cases b₀ (fun j => (t - â * Real.cos (θh j)) / Real.sin (θh j))
  â • x0 + ∑ j, b j • u j

lemma L2_eq_normalize_L2raw (m : ℕ) (t ε c : ℝ) (x0 : E) (u : Fin (m + 1) → E) (orc : E → Bool) :
    L2 m t ε c x0 u orc = ‖L2raw m t ε c x0 u orc‖⁻¹ • L2raw m t ε c x0 u orc := rfl

/-- `assembly2` without the normalisation step: no norm hypothesis on `g`. -/
lemma assembly2_sub (m : ℕ) (hdim : Module.finrank ℝ E = m + 1 + 1)
    (x0 : E) (u : Fin (m + 1) → E) (hON : Orthonormal ℝ (Fin.cons x0 u : Fin (m + 1 + 1) → E))
    (g : E) (ε : ℝ) (hε : 0 < ε) (â : ℝ) (b : Fin (m + 1) → ℝ) (e : ℝ)
    (he : e = ε / ((1 + ε) * Real.sqrt ((m : ℝ) + 2)))
    (hâ : |â - inner ℝ x0 g| ≤ e) (hb : ∀ j, |b j - inner ℝ (u j) g| ≤ e) :
    ‖(â • x0 + ∑ j, b j • u j) - g‖ ≤ ε / (1 + ε) := by
  set g' : E := â • x0 + ∑ j, b j • u j with hg'def
  have he0 : 0 ≤ e := by rw [he]; positivity
  -- orthonormality facts
  have hx0 : inner ℝ x0 x0 = (1 : ℝ) := by
    have := hON.1 0
    simp only [Fin.cons_zero] at this
    rw [real_inner_self_eq_norm_sq, this]; norm_num
  have hx0u : ∀ j, inner ℝ x0 (u j) = (0 : ℝ) := by
    intro j
    have := hON.2 (Fin.succ_ne_zero j).symm
    simpa using this
  have hu : Orthonormal ℝ u := by
    have h := hON.comp Fin.succ (Fin.succ_injective _)
    have e : (Fin.cons x0 u : Fin (m + 1 + 1) → E) ∘ Fin.succ = u := by
      funext j; simp
    rwa [e] at h
  have hux0 : ∀ j, inner ℝ (u j) x0 = (0 : ℝ) := by
    intro j; rw [real_inner_comm]; exact hx0u j
  have hg'x : inner ℝ x0 (g' - g) = â - inner ℝ x0 g := by
    simp only [hg'def, inner_sub_right, inner_add_right, inner_smul_right, hx0, inner_sum, hx0u,
      mul_zero, Finset.sum_const_zero, add_zero, mul_one]
  have hg'u : ∀ i, inner ℝ (u i) (g' - g) = b i - inner ℝ (u i) g := by
    intro i
    simp only [hg'def, inner_sub_right, inner_add_right, inner_smul_right, hux0, mul_zero, zero_add]
    rw [hu.inner_right_fintype]
  have hnorm : ‖g' - g‖ ^ 2 ≤ ((m : ℝ) + 2) * e ^ 2 := by
    rw [parseval_cons (m + 1) hdim x0 u hON, hg'x]
    simp only [hg'u]
    have h1 : (â - inner ℝ x0 g) ^ 2 ≤ e ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hâ 2
    have h2 : ∑ j, (b j - inner ℝ (u j) g) ^ 2 ≤ ∑ _j : Fin (m + 1), e ^ 2 :=
      Finset.sum_le_sum (fun j _ => by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb j) 2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    push_cast at h2
    linarith
  have hr : ‖g' - g‖ ≤ ε / (1 + ε) := by
    have hsq : Real.sqrt ((m : ℝ) + 2) * e = ε / (1 + ε) := by
      rw [he]; field_simp
    rw [← hsq, ← Real.sqrt_sq (norm_nonneg (g' - g)), ← Real.sqrt_sq (by positivity : 0 ≤ e),
      ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hnorm
  exact hr

/-- **L2 against a target of norm `≤ 1`.** The unnormalised L2 vector is within `ε/(1+ε)` of `g`. -/
theorem L2_correct_sub (m : ℕ) (hdim : Module.finrank ℝ E = m + 1 + 1)
    (x0 : E) (u : Fin (m + 1) → E) (hON : Orthonormal ℝ (Fin.cons x0 u : Fin (m + 1 + 1) → E))
    (g : E) (hg : ‖g‖ ≤ 1) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (c : ℝ) (hc : 0 < c) (hc1 : t + c < 1) (hx0 : t + c ≤ inner ℝ x0 g)
    (ε : ℝ) (hε : 0 < ε) :
    ‖L2raw m t ε c x0 u (fun x => decide (t < inner ℝ x g)) - g‖ ≤ ε / (1 + ε) := by
  -- geometry of the true coefficients
  have hpars := parseval_cons (m + 1) hdim x0 u hON g
  have hg2 : ‖g‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg g]
  have hab : ∀ j, inner ℝ x0 g ^ 2 + inner ℝ (u j) g ^ 2 ≤ 1 := by
    intro j
    have := Finset.single_le_sum (f := fun j => inner ℝ (u j) g ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    nlinarith
  unfold L2raw
  dsimp only
  -- constants
  set a₀ := t + c with ha₀
  have hta₀ : t < a₀ := by rw [ha₀]; linarith
  have ha₀1 : a₀ < 1 := hc1
  have ha₀0 : 0 < a₀ := ht.trans hta₀
  have hat : Real.arccos t < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr ht
  have hat0 : 0 < Real.arccos t := Real.arccos_pos.mpr ht1
  have haa₀ : 0 < Real.arccos a₀ := Real.arccos_pos.mpr ha₀1
  have haa₀2 : Real.arccos a₀ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr ha₀0
  have haa₀t : Real.arccos a₀ ≤ Real.arccos t := Real.arccos_le_arccos hta₀.le
  have hta₀1 : t / a₀ < 1 := by rw [div_lt_one ha₀0]; exact hta₀
  have hta₀0 : 0 < t / a₀ := by positivity
  have htta₀ : t ≤ t / a₀ := by rw [le_div_iff₀ ha₀0]; nlinarith
  set w₀ := Real.arccos (t / a₀) with hw₀
  have hw₀0 : 0 < w₀ := Real.arccos_pos.mpr hta₀1
  have hw₀pi2 : w₀ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr hta₀0
  have hw₀t : w₀ ≤ Real.arccos t := Real.arccos_le_arccos htta₀
  set Θ₀ := Real.arccos a₀ + Real.arccos t with hΘ₀
  have hΘ₀pi : Θ₀ ≤ Real.pi := by linarith
  have hΘ₀0 : 0 < Θ₀ := by linarith
  have hw₀Θ : w₀ < Θ₀ := by linarith
  have hΘ₀t : Θ₀ ≤ 2 * Real.arccos t := by linarith
  set s₀ := min (Real.sin w₀) (Real.sin Θ₀) with hs₀
  have hs₀0 : 0 < s₀ := lt_min
    (Real.sin_pos_of_pos_of_lt_pi hw₀0 (by linarith [Real.pi_pos]))
    (Real.sin_pos_of_pos_of_lt_pi hΘ₀0 (by linarith))
  have hs₀1 : s₀ ≤ 1 := (min_le_left _ _).trans (Real.sin_le_one _)
  have hsqrt : 1 ≤ Real.sqrt ((m : ℝ) + 2) := by
    rw [Real.one_le_sqrt]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  set e := ε / ((1 + ε) * Real.sqrt ((m : ℝ) + 2)) with he
  have he0 : 0 < e := by positivity
  have he1 : e < 1 := by
    rw [he, div_lt_one (by positivity)]
    nlinarith
  have hm2 : (1 : ℝ) ≤ (m : ℝ) + 2 := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  set η := ((m : ℝ) + 1) * s₀ * e / ((m : ℝ) + 2) with hη
  set δ := s₀ * e / ((m : ℝ) + 2) with hδ
  set ηa := t * δ / 4 with hηa
  set Θ := 2 * Real.arccos t with hΘ
  have hη0 : 0 < η := by rw [hη]; positivity
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδe : δ ≤ e := by
    rw [hδ, div_le_iff₀ (by positivity)]; nlinarith
  have hδη : (δ + η) / s₀ = e := by
    rw [hδ, hη]; field_simp; ring
  have hηa0 : 0 < ηa := by rw [hηa]; positivity
  have hηat : ηa ≤ t / 2 := by
    rw [hηa]; nlinarith
  have h4ηa : 4 * ηa / t = δ := by rw [hηa]; field_simp
  -- arc structure on every circle
  choose φ w hcw ha hb h1 h2 hw₀w hwt hφ hcup hcdown hup hdown hlip using
    fun j => arc_structure2 ht hta₀ hx0 (hab j)
  have hf : ∀ (j : Fin (m + 1)) θ,
      decide (t < inner ℝ (Real.cos θ • x0 + Real.sin θ • u j) g) = true ↔
      t < inner ℝ x0 g * Real.cos θ + inner ℝ (u j) g * Real.sin θ := by
    intro j θ
    simp only [decide_eq_true_eq, inner_add_left, real_inner_smul_left]
    constructor <;> intro h <;> linarith
  -- circle 0
  have h0 := circle0_est (fun θ => decide (t < inner ℝ (Real.cos θ • x0 + Real.sin θ • u 0) g))
    ⌈Real.logb 2 (Θ / ηa)⌉₊ (φ 0) (w 0) ht ht1 hηa0 hηat rfl (hcw 0) (ha 0) (hb 0) (h1 0)
    (by have := (abs_le.mp (hφ 0)).2; linarith [hwt 0])
    (by have := (abs_le.mp (hφ 0)).1; linarith [hwt 0]) (h2 0)
    (fun θ a b => (hf 0 θ).trans (hup 0 θ a b))
    (fun θ a b => (hf 0 θ).trans (hdown 0 θ a b))
  rw [h4ηa] at h0
  refine assembly2_sub m hdim x0 u hON g ε hε _ _ e he ?_ ?_
  · exact h0.1.trans hδe
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [Fin.cases_zero]
      exact h0.2.trans hδe
    · rw [Fin.cases_succ]
      rw [← hδη]
      exact circle_est
        (fun θ => decide (t < inner ℝ (Real.cos θ • x0 + Real.sin θ • u j.succ) g))
        ⌈Real.logb 2 ((Θ₀ - w₀) / η)⌉₊ (φ j.succ) (w j.succ) hw₀0.le hw₀Θ hΘ₀pi hΘ₀t rfl hs₀0
        hη0 rfl h0.1 (hw₀w j.succ) (hwt j.succ) (Real.arccos a₀) rfl (hφ j.succ)
        (hcup j.succ) (hcdown j.succ)
        (fun θ a b => (hf j.succ θ).trans (hup j.succ θ a b))
        (fun θ a b => (hf j.succ θ).trans (hdown j.succ θ a b)) (hlip j.succ)

/-- **Photo-in-hand / two-tier launch.** If `‖x0 − g‖ ≤ r₀` then `⟨x0, g⟩ ≥ 1 − r₀²/2`, so `L2`
with margin `c = 1 − r₀²/2 − t` applies (bracket `[arccos(t/a₀), arccos a₀ + arccos t]`,
`a₀ = 1 − r₀²/2`). -/
theorem L2_photo (m : ℕ) (hdim : Module.finrank ℝ E = m + 1 + 1)
    (x0 : E) (u : Fin (m + 1) → E) (hON : Orthonormal ℝ (Fin.cons x0 u : Fin (m + 1 + 1) → E))
    (g : E) (hg : ‖g‖ = 1) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (hr₀t : t < 1 - r₀ ^ 2 / 2) (hx0 : ‖x0 - g‖ ≤ r₀)
    (ε : ℝ) (hε : 0 < ε) :
    ‖L2 m t ε (1 - r₀ ^ 2 / 2 - t) x0 u (fun x => decide (t < inner ℝ x g)) - g‖ ≤ ε := by
  have hx0n : ‖x0‖ = 1 := by
    have := hON.1 0
    simpa using this
  have hinner : 1 - r₀ ^ 2 / 2 ≤ inner ℝ x0 g := by
    have h1 : ‖x0 - g‖ ^ 2 = ‖x0‖ ^ 2 - 2 * inner ℝ x0 g + ‖g‖ ^ 2 := by
      rw [@norm_sub_sq_real]
    have h2 : ‖x0 - g‖ ^ 2 ≤ r₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx0 2
    rw [hx0n, hg] at h1
    linarith
  refine L2_correct m hdim x0 u hON g hg t ht ht1 (1 - r₀ ^ 2 / 2 - t) (by linarith)
    (by nlinarith) (by linarith) ε hε

end OracleBounds.Attacks
