import Mathlib

/-!
# Localisation by bisection (upper-bounds note, Algorithm L0 / Theorem 4.1)

Noiseless oracle `x ↦ [⟨x, g⟩ > t]` for a single unit template `g`, a launch point `x0` inside
its cap (`⟨x0, g⟩ > t`), and an orthonormal completion `u₁ … u_m` of `x0` (`dim = m + 1`).
Along each great circle `θ ↦ cos θ·x0 + sin θ·uⱼ` the loud set is an arc containing `θ = 0`;
two bisections (towards `+Θ` and `−Θ`) locate its ends to within `η`, from which
`aⱼ ≈ ⟨x0, g⟩`, `bⱼ ≈ ⟨uⱼ, g⟩` are read off; the normalised reassembly is `ε`-close to `g`.

Query count: `2m` bisections of `k = ⌈log₂(Θ/η)⌉` oracle calls each, i.e.
`Q_loc = 2(d−1)⌈log₂(12√d·min(π, 2 arccos t)/(tε))⌉`, visible from the definition.

**Definitions and the statement of `L0_correct` are locked by the administrator. Do not edit.**
-/

namespace OracleBounds.Attacks

/-- Bisection: `k` halvings of the bracket `[a, b]` (either orientation), keeping as `a` the
endpoint where `f` is `true`. Uses exactly `k` evaluations of `f`. -/
noncomputable def bisect (f : ℝ → Bool) : ℕ → ℝ → ℝ → ℝ × ℝ
  | 0, a, b => (a, b)
  | k + 1, a, b =>
      if f ((a + b) / 2) then bisect f k ((a + b) / 2) b
      else bisect f k a ((a + b) / 2)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Algorithm L0.** -/
noncomputable def L0 (m : ℕ) (t ε : ℝ) (x0 : E) (u : Fin m → E) (orc : E → Bool) : E :=
  let η := t * ε / (12 * Real.sqrt (m + 1))
  let Θ := min Real.pi (2 * Real.arccos t)
  let k := ⌈Real.logb 2 (Θ / η)⌉₊
  let γ : Fin m → ℝ → E := fun j θ => Real.cos θ • x0 + Real.sin θ • u j
  let θp : Fin m → ℝ := fun j => (bisect (fun θ => orc (γ j θ)) k 0 Θ).1
  let θm : Fin m → ℝ := fun j => (bisect (fun θ => orc (γ j θ)) k 0 (-Θ)).1
  let φ : Fin m → ℝ := fun j => (θp j + θm j) / 2
  let w : Fin m → ℝ := fun j => (θp j - θm j) / 2
  let a : Fin m → ℝ := fun j => t / Real.cos (w j) * Real.cos (φ j)
  let b : Fin m → ℝ := fun j => t / Real.cos (w j) * Real.sin (φ j)
  let g' : E := ((∑ j, a j) / m) • x0 + ∑ j, b j • u j
  ‖g'‖⁻¹ • g'

/-! ### Helper lemmas for `L0_correct` -/

lemma bisect_up (f : ℝ → Bool) (c : ℝ) : ∀ (k : ℕ) (a b : ℝ),
    (∀ θ, a ≤ θ → θ ≤ b → (f θ = true ↔ θ < c)) → a < c → c ≤ b →
    (bisect f k a b).1 < c ∧ c ≤ (bisect f k a b).2 ∧
      (bisect f k a b).2 - (bisect f k a b).1 = (b - a) / 2 ^ k := by
  intro k
  induction k with
  | zero => intro a b _ hac hcb; simp [bisect, hac, hcb]
  | succ k ih =>
    intro a b hf hac hcb
    have hab : a ≤ b := by linarith
    simp only [bisect]
    split_ifs with h
    · have hm : (a + b) / 2 < c := (hf _ (by linarith) (by linarith)).1 h
      obtain ⟨h1, h2, h3⟩ := ih ((a + b) / 2) b
        (fun θ h1 h2 => hf θ (by linarith) h2) hm hcb
      refine ⟨h1, h2, ?_⟩
      rw [h3, pow_succ]; field_simp; ring
    · have hm : c ≤ (a + b) / 2 := by
        by_contra hc; push Not at hc
        exact h ((hf _ (by linarith) (by linarith)).2 hc)
      obtain ⟨h1, h2, h3⟩ := ih a ((a + b) / 2)
        (fun θ h1 h2 => hf θ h1 (by linarith)) hac hm
      refine ⟨h1, h2, ?_⟩
      rw [h3, pow_succ]; field_simp; ring

lemma bisect_down (f : ℝ → Bool) (c : ℝ) : ∀ (k : ℕ) (a b : ℝ),
    (∀ θ, b ≤ θ → θ ≤ a → (f θ = true ↔ c < θ)) → c < a → b ≤ c →
    c < (bisect f k a b).1 ∧ (bisect f k a b).2 ≤ c ∧
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
        (fun θ h1 h2 => hf θ h1 (by linarith)) hm hcb
      refine ⟨h1, h2, ?_⟩
      rw [h3, pow_succ]; field_simp; ring
    · have hm : (a + b) / 2 ≤ c := by
        by_contra hc; push Not at hc
        exact h ((hf _ (by linarith) (by linarith)).2 hc)
      obtain ⟨h1, h2, h3⟩ := ih a ((a + b) / 2)
        (fun θ h1 h2 => hf θ (by linarith) h2) hac hm
      refine ⟨h1, h2, ?_⟩
      rw [h3, pow_succ]; field_simp; ring

lemma ceil_bound {Θ η : ℝ} (hΘ : 0 < Θ) (hη : 0 < η) :
    Θ / 2 ^ ⌈Real.logb 2 (Θ / η)⌉₊ ≤ η := by
  have h1 : Θ / η ≤ (2:ℝ) ^ ⌈Real.logb 2 (Θ / η)⌉₊ := by
    calc Θ / η = (2:ℝ) ^ Real.logb 2 (Θ / η) := (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      _ ≤ (2:ℝ) ^ (⌈Real.logb 2 (Θ / η)⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = _ := by rw [Real.rpow_natCast]
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hη] at h1
  linarith

lemma cos_le_of_mem {w x : ℝ} (hw : 0 ≤ w) (h1 : w ≤ x) (h2 : x ≤ 2 * Real.pi - w) :
    Real.cos x ≤ Real.cos w := by
  have e := Real.cos_sub_cos x w
  have s1 : 0 ≤ Real.sin ((x + w) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have s2 : 0 ≤ Real.sin ((x - w) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  nlinarith [mul_nonneg s1 s2]

lemma cos_lt_of_abs {w x : ℝ} (hw : w ≤ Real.pi) (h : |x| < w) :
    Real.cos w < Real.cos x := by
  rw [← Real.cos_abs x]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hw h

lemma arc_structure {t a b : ℝ} (ht : 0 < t) (hta : t < a) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    ∃ φ w : ℝ, t ≤ Real.cos w ∧ t / Real.cos w * Real.cos φ = a ∧
      t / Real.cos w * Real.sin φ = b ∧
      0 < φ + w ∧ φ + w ≤ 2 * Real.arccos t ∧ -(2 * Real.arccos t) ≤ φ - w ∧ φ - w < 0 ∧
      (∀ θ, 0 ≤ θ → θ ≤ 2 * Real.arccos t →
        (t < a * Real.cos θ + b * Real.sin θ ↔ θ < φ + w)) ∧
      (∀ θ, -(2 * Real.arccos t) ≤ θ → θ ≤ 0 →
        (t < a * Real.cos θ + b * Real.sin θ ↔ φ - w < θ)) := by
  have ha : 0 < a := ht.trans hta
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
  refine ⟨φ, w, ?_, ?_, ?_, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
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

lemma ratio_err {t η c ch X Xh : ℝ} (ht : 0 < t) (ht1 : t < 1) (hη0 : 0 ≤ η) (hηt : η ≤ t / 2)
    (hc : t ≤ c) (hcc : |ch - c| ≤ η) (hX : |X| ≤ 1) (hXX : |Xh - X| ≤ η) :
    |t / ch * Xh - t / c * X| ≤ 4 * η / t := by
  have hch : t / 2 ≤ ch := by linarith [(abs_le.mp hcc).1]
  have hc0 : 0 < c := by linarith
  have hch0 : 0 < ch := by linarith
  have key : t / ch * Xh - t / c * X = t * (Xh - X) / ch + t * X * (c - ch) / (ch * c) := by
    field_simp; ring
  have h1 : |t * (Xh - X) / ch| ≤ 2 * η := by
    rw [abs_div, abs_mul, abs_of_pos ht, abs_of_pos hch0, div_le_iff₀ hch0]
    nlinarith [abs_nonneg (Xh - X)]
  have h2 : |t * X * (c - ch) / (ch * c)| ≤ 2 * η / t := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos ht, abs_of_pos (mul_pos hch0 hc0),
      div_le_div_iff₀ (mul_pos hch0 hc0) ht, abs_sub_comm]
    have hcc' : ch * c ≥ t / 2 * t := mul_le_mul hch hc ht.le hch0.le
    have := mul_le_mul hX hcc (abs_nonneg _) zero_le_one
    nlinarith [abs_nonneg X, abs_nonneg (ch - c)]
  have h3 : 2 * η ≤ 2 * η / t := by
    rw [le_div_iff₀ ht]; nlinarith
  rw [key]
  calc _ ≤ |t * (Xh - X) / ch| + |t * X * (c - ch) / (ch * c)| := abs_add_le _ _
    _ ≤ 2 * η / t + 2 * η / t := by linarith
    _ = 4 * η / t := by ring

lemma norm_normalise_sub (v g : E) (hg : ‖g‖ = 1) : ‖‖v‖⁻¹ • v - g‖ ≤ 2 * ‖v - g‖ := by
  have h1 : ‖‖v‖⁻¹ • v - v‖ ≤ ‖v - g‖ := by
    by_cases hv : v = 0
    · subst hv; simp
    · have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have : ‖v‖⁻¹ • v - v = (‖v‖⁻¹ - 1) • v := by rw [sub_smul, one_smul]
      rw [this, norm_smul, Real.norm_eq_abs]
      have e : |‖v‖⁻¹ - 1| * ‖v‖ = |1 - ‖v‖| := by
        rw [← abs_of_pos hv0, ← abs_mul, abs_of_pos hv0, sub_mul, inv_mul_cancel₀ hv0.ne',
          one_mul]
      rw [e, ← hg]
      exact abs_norm_sub_norm_le g v |>.trans (by rw [norm_sub_rev])
  calc ‖‖v‖⁻¹ • v - g‖ = ‖(‖v‖⁻¹ • v - v) + (v - g)‖ := by congr 1; abel
    _ ≤ ‖‖v‖⁻¹ • v - v‖ + ‖v - g‖ := norm_add_le _ _
    _ ≤ 2 * ‖v - g‖ := by linarith

lemma parseval_cons (m : ℕ) (hdim : Module.finrank ℝ E = m + 1)
    (x0 : E) (u : Fin m → E) (hON : Orthonormal ℝ (Fin.cons x0 u : Fin (m + 1) → E)) (v : E) :
    ‖v‖ ^ 2 = inner ℝ x0 v ^ 2 + ∑ j, inner ℝ (u j) v ^ 2 := by
  have hcard : Fintype.card (Fin (m + 1)) = Module.finrank ℝ E := by simp [hdim]
  set B := basisOfOrthonormalOfCardEqFinrank hON hcard
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range (Fin.cons x0 u : Fin (m + 1) → E)) := by
    have := B.span_eq
    rw [coe_basisOfOrthonormalOfCardEqFinrank] at this
    rw [this]
  set OB := OrthonormalBasis.mk hON hsp
  have h := OB.sum_sq_norm_inner_right v
  rw [Fin.sum_univ_succ] at h
  simp only [OB, OrthonormalBasis.coe_mk, Fin.cons_zero, Fin.cons_succ, Real.norm_eq_abs,
    sq_abs] at h
  exact h.symm

lemma assembly (m : ℕ) (hm : 1 ≤ m) (hdim : Module.finrank ℝ E = m + 1)
    (x0 : E) (u : Fin m → E) (hON : Orthonormal ℝ (Fin.cons x0 u : Fin (m + 1) → E))
    (g : E) (hg : ‖g‖ = 1) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (η : ℝ) (hη0 : 0 ≤ η) (hηt : η ≤ t / 2) (ε : ℝ)
    (hηε : Real.sqrt (m + 1) * (4 * η / t) ≤ ε / 2)
    (θp θm φ w : Fin m → ℝ) (hp : ∀ j, |θp j - (φ j + w j)| ≤ η)
    (hmn : ∀ j, |θm j - (φ j - w j)| ≤ η) (hcw : ∀ j, t ≤ Real.cos (w j))
    (ha : ∀ j, t / Real.cos (w j) * Real.cos (φ j) = inner ℝ x0 g)
    (hb : ∀ j, t / Real.cos (w j) * Real.sin (φ j) = inner ℝ (u j) g) :
    ‖(let g' : E := ((∑ j, t / Real.cos ((θp j - θm j) / 2) * Real.cos ((θp j + θm j) / 2)) / m)
        • x0 + ∑ j, (t / Real.cos ((θp j - θm j) / 2) * Real.sin ((θp j + θm j) / 2)) • u j
      ‖g'‖⁻¹ • g') - g‖ ≤ ε := by
  dsimp only
  set g' : E := ((∑ j, t / Real.cos ((θp j - θm j) / 2) * Real.cos ((θp j + θm j) / 2)) / m)
        • x0 + ∑ j, (t / Real.cos ((θp j - θm j) / 2) * Real.sin ((θp j + θm j) / 2)) • u j
    with hg'def
  set A := (∑ j, t / Real.cos ((θp j - θm j) / 2) * Real.cos ((θp j + θm j) / 2)) / (m : ℝ)
    with hA
  set B : Fin m → ℝ := fun j => t / Real.cos ((θp j - θm j) / 2) * Real.sin ((θp j + θm j) / 2)
    with hB
  have hφ : ∀ j, |(θp j + θm j) / 2 - φ j| ≤ η := by
    intro j
    have e : (θp j + θm j) / 2 - φ j = ((θp j - (φ j + w j)) + (θm j - (φ j - w j))) / 2 := by
      ring
    rw [e, abs_div, abs_two]
    linarith [abs_add_le (θp j - (φ j + w j)) (θm j - (φ j - w j)), hp j, hmn j]
  have hw : ∀ j, |Real.cos ((θp j - θm j) / 2) - Real.cos (w j)| ≤ η := by
    intro j
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    have e : (θp j - θm j) / 2 - w j = ((θp j - (φ j + w j)) - (θm j - (φ j - w j))) / 2 := by
      ring
    rw [e, abs_div, abs_two]
    linarith [abs_sub (θp j - (φ j + w j)) (θm j - (φ j - w j)), hp j, hmn j]
  have hAj : ∀ j, |t / Real.cos ((θp j - θm j) / 2) * Real.cos ((θp j + θm j) / 2)
      - inner ℝ x0 g| ≤ 4 * η / t := by
    intro j
    rw [← ha j]
    exact ratio_err ht ht1 hη0 hηt (hcw j) (hw j) (Real.abs_cos_le_one _)
      ((Real.abs_cos_sub_cos_le _ _).trans (hφ j))
  have hBj : ∀ j, |B j - inner ℝ (u j) g| ≤ 4 * η / t := by
    intro j
    rw [← hb j]
    exact ratio_err ht ht1 hη0 hηt (hcw j) (hw j) (Real.abs_sin_le_one _)
      ((Real.abs_sin_sub_sin_le _ _).trans (hφ j))
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hAe : |A - inner ℝ x0 g| ≤ 4 * η / t := by
    have e : A - inner ℝ x0 g = (∑ j, (t / Real.cos ((θp j - θm j) / 2) *
        Real.cos ((θp j + θm j) / 2) - inner ℝ x0 g)) / m := by
      rw [hA, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    rw [e, abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
    calc _ ≤ ∑ j, |t / Real.cos ((θp j - θm j) / 2) * Real.cos ((θp j + θm j) / 2)
          - inner ℝ x0 g| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin m, 4 * η / t := Finset.sum_le_sum (fun j _ => hAj j)
      _ = _ := by simp [mul_comm]
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
    have e : (Fin.cons x0 u : Fin (m + 1) → E) ∘ Fin.succ = u := by
      funext j; simp
    rwa [e] at h
  have hux0 : ∀ j, inner ℝ (u j) x0 = (0 : ℝ) := by
    intro j; rw [real_inner_comm]; exact hx0u j
  have hg'x : inner ℝ x0 (g' - g) = A - inner ℝ x0 g := by
    simp only [hg'def, inner_sub_right, inner_add_right, inner_smul_right, hx0, inner_sum, hx0u,
      mul_zero, Finset.sum_const_zero, add_zero, mul_one]
  have hg'u : ∀ i, inner ℝ (u i) (g' - g) = B i - inner ℝ (u i) g := by
    intro i
    simp only [hg'def, inner_sub_right, inner_add_right, inner_smul_right, hux0, mul_zero, zero_add]
    rw [hu.inner_right_fintype]
  have hnorm : ‖g' - g‖ ^ 2 ≤ (m + 1) * (4 * η / t) ^ 2 := by
    rw [parseval_cons m hdim x0 u hON, hg'x]
    simp only [hg'u]
    have h1 : (A - inner ℝ x0 g) ^ 2 ≤ (4 * η / t) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hAe 2
    have h2 : ∑ j, (B j - inner ℝ (u j) g) ^ 2 ≤ ∑ _j : Fin m, (4 * η / t) ^ 2 :=
      Finset.sum_le_sum (fun j _ => by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hBj j) 2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    linarith
  have hnorm' : ‖g' - g‖ ≤ Real.sqrt (m + 1) * (4 * η / t) := by
    have hq : 0 ≤ 4 * η / t := by positivity
    rw [← Real.sqrt_sq (norm_nonneg (g' - g)), ← Real.sqrt_sq hq, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hnorm
  calc _ ≤ 2 * ‖g' - g‖ := norm_normalise_sub g' g hg
    _ ≤ ε := by linarith

/-- **Theorem 4.1 (K0 localisation).** -/
theorem L0_correct (m : ℕ) (hm : 1 ≤ m) (hdim : Module.finrank ℝ E = m + 1)
    (x0 : E) (u : Fin m → E) (hON : Orthonormal ℝ (Fin.cons x0 u : Fin (m + 1) → E))
    (g : E) (hg : ‖g‖ = 1) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (hx0 : t < inner ℝ x0 g)
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 2) :
    ‖L0 m t ε x0 u (fun x => decide (t < inner ℝ x g)) - g‖ ≤ ε := by
  have hpars := parseval_cons m hdim x0 u hON g
  rw [hg] at hpars
  have hab : ∀ j, inner ℝ x0 g ^ 2 + inner ℝ (u j) g ^ 2 ≤ 1 := by
    intro j
    have := Finset.single_le_sum (f := fun j => inner ℝ (u j) g ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    nlinarith
  have hat : Real.arccos t < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr ht
  have hΘ : min Real.pi (2 * Real.arccos t) = 2 * Real.arccos t := min_eq_right (by linarith)
  have hΘ0 : 0 < 2 * Real.arccos t := by have := Real.arccos_pos.mpr ht1; linarith
  have hs : 1 ≤ Real.sqrt ((m : ℝ) + 1) := by
    rw [Real.one_le_sqrt]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  set η := t * ε / (12 * Real.sqrt ((m : ℝ) + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hηt : η ≤ t / 2 := by
    rw [hη, div_le_iff₀ (by positivity)]; nlinarith
  have hηε : Real.sqrt ((m : ℝ) + 1) * (4 * η / t) ≤ ε / 2 := by
    have : Real.sqrt ((m : ℝ) + 1) * (4 * η / t) = ε / 3 := by
      rw [hη]; field_simp; ring
    linarith
  set k := ⌈Real.logb 2 (2 * Real.arccos t / η)⌉₊ with hk
  have hkb : 2 * Real.arccos t / 2 ^ k ≤ η := ceil_bound hΘ0 hη0
  choose φ w hcw ha hb h1 h2 h3 h4 hup hdown using
    fun j => arc_structure ht hx0 (hab j)
  set f : Fin m → ℝ → Bool :=
    fun j θ => decide (t < inner ℝ (Real.cos θ • x0 + Real.sin θ • u j) g) with hfdef
  have hf : ∀ j θ, f j θ = true ↔
      t < inner ℝ x0 g * Real.cos θ + inner ℝ (u j) g * Real.sin θ := by
    intro j θ
    simp only [hfdef, decide_eq_true_eq, inner_add_left, real_inner_smul_left]
    constructor <;> intro h <;> linarith
  have hp : ∀ j, |(bisect (f j) k 0 (2 * Real.arccos t)).1 - (φ j + w j)| ≤ η := by
    intro j
    obtain ⟨q1, q2, q3⟩ := bisect_up (f j) (φ j + w j) k 0 (2 * Real.arccos t)
      (fun θ a b => (hf j θ).trans (hup j θ a b)) (h1 j) (h2 j)
    rw [sub_zero] at q3
    rw [abs_le]; constructor <;> linarith
  have hmn : ∀ j, |(bisect (f j) k 0 (-(2 * Real.arccos t))).1 - (φ j - w j)| ≤ η := by
    intro j
    obtain ⟨q1, q2, q3⟩ := bisect_down (f j) (φ j - w j) k 0 (-(2 * Real.arccos t))
      (fun θ a b => (hf j θ).trans (hdown j θ a b)) (h4 j) (h3 j)
    rw [sub_neg_eq_add, zero_add] at q3
    rw [abs_le]; constructor <;> linarith
  have key := assembly m hm hdim x0 u hON g hg t ht ht1 η hη0.le hηt ε hηε
    (fun j => (bisect (f j) k 0 (2 * Real.arccos t)).1)
    (fun j => (bisect (f j) k 0 (-(2 * Real.arccos t))).1) φ w hp hmn hcw ha hb
  unfold L0
  dsimp only
  rw [hΘ]
  exact key

end OracleBounds.Attacks
