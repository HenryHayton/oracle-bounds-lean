import OracleBounds.GeneralPrior.Gallery
import OracleBounds.V6.InfoProcess

/-!
# Membership inference as two-gallery testing (`n-face-general-prior-v2` §18, G17)

"Is the known candidate `c` on the list?" is the test `H₀ : gallery = G₀` against
`H₁ : gallery = G₀ ∪ {c}`. Conditioned on `G₀`, both hypotheses are adaptive one-bit processes with
the *same* probe rule and kernels `p₀`, `p₁` that differ only on probes reaching `c`. Theorem 18.1
bounds the attacker's total error `δI + δII` from below in terms of
`E₀[S_c]`, the expected number of `c`-reaching probes under `H₀`:

* (i) coupling/TV: `δI + δII ≥ 1 − Δ·E₀[S_c] − 2ζQ`;
* (ii) KL: `KL(P₀‖P₁) ≤ KL_ρ·E₀[S_c] + β₀ᶜᵃᵖ·Q`, hence by Bretagnolle–Huber
  `δI + δII ≥ ½·exp(−KL_ρ·E₀[S_c] − β₀ᶜᵃᵖ·Q)`.

The file is in three layers:

1. **Two kernels, one probe rule** (any `X`): `val_tv_cost` and `klRounds_le_cost`, the
   round-by-round comparison with a per-round cost `Δ·[reach] + const`.
2. **Finite-pmf facts:** `bretagnolle_huber` (proved here from weighted AM–GM and Cauchy–Schwarz;
   not in Mathlib), `bkl_le_chi2` (`KL ≤ χ²`), `bkl_le_corner` (`KL_ρ` closed form: the sup of
   Bernoulli KL over `[ρ,1−ρ]²` is `(1−2ρ)·log((1−ρ)/ρ)`).
3. **The gallery instance** (`membership_tv`, `membership_kl`, `membership_bh`,
   `membership_reach_needed`), with the note's three-case split done once in `cand_cases`.

Remark 18.2(b) (noiseless kernels make both bounds vacuous, correctly) is `one_probe_decides`.

No `sorry`s.
-/

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

/-! ### 1. Two kernels, one probe rule -/

section TwoKernels

variable {X : Type*}

/-- **Round-by-round TV comparison.** If the two kernels differ at probe `x` by at most
`Δ·[reach x] + 2ζ`, then for any leaf function in `[0,1]` the two expectations differ by at most
`Δ · E₀[#reaching probes] + 2ζ·r`, the count taken under the `p₀`-process. -/
theorem val_tv_cost (probe : List Bool → X) (p₀ p₁ : X → ℝ)
    (hp₀ : ∀ x, 0 ≤ p₀ x ∧ p₀ x ≤ 1) (hp₁ : ∀ x, 0 ≤ p₁ x ∧ p₁ x ≤ 1)
    (reach : X → Prop) [DecidablePred reach] (Δ ζ : ℝ)
    (hloc : ∀ x, |p₀ x - p₁ x| ≤ Δ * (if reach x then 1 else 0) + 2 * ζ)
    (F : List Bool → ℝ) (hF : ∀ h', 0 ≤ F h' ∧ F h' ≤ 1) :
    ∀ (r : ℕ) h, |val p₀ probe F r h - val p₁ probe F r h| ≤
      Δ * accCount p₀ probe reach r h + 2 * r * ζ := by
  intro r
  induction r with
  | zero => intro h; simp [accCount]
  | succ r ih =>
    intro h
    set a₀ := val p₀ probe F r (h ++ [true])
    set b₀ := val p₀ probe F r (h ++ [false])
    set a₁ := val p₁ probe F r (h ++ [true])
    set b₁ := val p₁ probe F r (h ++ [false])
    set t := p₀ (probe h)
    set g := p₁ (probe h)
    have e : val p₀ probe F (r + 1) h - val p₁ probe F (r + 1) h =
        t * (a₀ - a₁) + (1 - t) * (b₀ - b₁) + (t - g) * (a₁ - b₁) := by
      simp only [val_succ, a₀, b₀, a₁, b₁, t, g]; ring
    rw [e]
    have ht0 : 0 ≤ t := (hp₀ _).1
    have ht1 : 0 ≤ 1 - t := by linarith [(hp₀ (probe h)).2]
    have ha := val_mem_Icc probe hp₁ hF r (h ++ [true])
    have hb := val_mem_Icc probe hp₁ hF r (h ++ [false])
    have hab : |a₁ - b₁| ≤ 1 := abs_le.2 ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩
    have hc := hloc (probe h)
    have hc0 : 0 ≤ Δ * (if reach (probe h) then 1 else 0) + 2 * ζ := (abs_nonneg _).trans hc
    have t1 : |t * (a₀ - a₁)| ≤ t * (Δ * accCount p₀ probe reach r (h ++ [true]) + 2 * r * ζ) := by
      rw [abs_mul, abs_of_nonneg ht0]; exact mul_le_mul_of_nonneg_left (ih _) ht0
    have t2 : |(1 - t) * (b₀ - b₁)| ≤
        (1 - t) * (Δ * accCount p₀ probe reach r (h ++ [false]) + 2 * r * ζ) := by
      rw [abs_mul, abs_of_nonneg ht1]; exact mul_le_mul_of_nonneg_left (ih _) ht1
    have t3 : |(t - g) * (a₁ - b₁)| ≤ Δ * (if reach (probe h) then 1 else 0) + 2 * ζ := by
      rw [abs_mul]
      calc |t - g| * |a₁ - b₁| ≤ (Δ * (if reach (probe h) then 1 else 0) + 2 * ζ) * 1 :=
            mul_le_mul hc hab (abs_nonneg _) hc0
        _ = _ := mul_one _
    have htri : |t * (a₀ - a₁) + (1 - t) * (b₀ - b₁) + (t - g) * (a₁ - b₁)| ≤
        |t * (a₀ - a₁)| + |(1 - t) * (b₀ - b₁)| + |(t - g) * (a₁ - b₁)| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    have hacc : accCount p₀ probe reach (r + 1) h = (if reach (probe h) then 1 else 0) +
        t * accCount p₀ probe reach r (h ++ [true]) +
        (1 - t) * accCount p₀ probe reach r (h ++ [false]) := rfl
    rw [hacc]
    push_cast
    nlinarith

/-- **Round-by-round KL comparison.** If `KL(Bern p₀(x) ‖ Bern p₁(x)) ≤ a·[reach x] + b` at every
probe, then `KL(P₀‖P₁) ≤ a · E₀[#reaching probes] + b·r`. -/
lemma klRounds_le_cost {p q : X → ℝ} {probe : List Bool → X} (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (act : X → Prop) [DecidablePred act] (a b : ℝ)
    (hcost : ∀ x, bkl (p x) (q x) ≤ a * (if act x then 1 else 0) + b) :
    ∀ r h, klRounds p q probe r h ≤ a * accCount p probe act r h + b * r := by
  intro r
  induction r with
  | zero => intro h; simp [klRounds, accCount]
  | succ r ih =>
    intro h
    simp only [klRounds, accCount]
    have h1 := ih (h ++ [true])
    have h2 := ih (h ++ [false])
    have hc := hcost (probe h)
    have hp0 := (hp (probe h)).1
    have hp1 : 0 ≤ 1 - p (probe h) := by linarith [(hp (probe h)).2]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h1 hp0, mul_le_mul_of_nonneg_left h2 hp1]

end TwoKernels

/-! ### 2. Finite-pmf facts -/

section Pmf

variable {ι : Type*} [Fintype ι]

/-- Any (randomised) decision's total error dominates the overlap `Σ min(P, R)`. -/
lemma sum_min_le_errors (P R D : ι → ℝ) (hD : ∀ i, 0 ≤ D i ∧ D i ≤ 1) :
    ∑ i, min (P i) (R i) ≤ ∑ i, P i * D i + ∑ i, R i * (1 - D i) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := min_le_left (P i) (R i)
  have h2 := min_le_right (P i) (R i)
  have hD0 := (hD i).1
  have hD1 : 0 ≤ 1 - D i := by linarith [(hD i).2]
  nlinarith [mul_le_mul_of_nonneg_left h1 hD0, mul_le_mul_of_nonneg_left h2 hD1]

/-- `exp(−KL/2) ≤ Σ √(P R)` (Bhattacharyya), from weighted AM–GM. -/
lemma exp_neg_half_kl_le (P R : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hR : ∀ i, 0 ≤ R i)
    (hP1 : ∑ i, P i = 1) (hac : ∀ i, R i = 0 → P i = 0) :
    Real.exp (-(klPmf P R / 2)) ≤ ∑ i, Real.sqrt (P i * R i) := by
  set z : ι → ℝ := fun i => Real.sqrt (R i / P i) with hz
  have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ P z (fun i _ => hP i) hP1
    (fun i _ => Real.sqrt_nonneg _)
  have hterm : ∀ i, z i ^ P i = Real.exp (-(P i * Real.log (P i / R i)) / 2) := by
    intro i
    rcases eq_or_lt_of_le (hP i) with h0 | h0
    · rw [← h0]; simp
    have hRi : 0 < R i := lt_of_le_of_ne (hR i) fun h => h0.ne' (hac i h.symm)
    have hzpos : 0 < z i := Real.sqrt_pos.2 (div_pos hRi h0)
    rw [Real.rpow_def_of_pos hzpos]
    congr 1
    rw [hz]
    dsimp only
    rw [Real.log_sqrt (div_nonneg hRi.le h0.le), Real.log_div hRi.ne' h0.ne',
      Real.log_div h0.ne' hRi.ne']
    ring
  have hlhs : ∏ i, z i ^ P i = Real.exp (-(klPmf P R / 2)) := by
    rw [Finset.prod_congr rfl fun i _ => hterm i, ← Real.exp_sum, klPmf]
    congr 1
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
    ring
  have hrhs : ∑ i, P i * z i = ∑ i, Real.sqrt (P i * R i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_lt_of_le (hP i) with h0 | h0
    · rw [← h0]; simp
    rw [hz]
    simp only
    rw [show P i * R i = P i ^ 2 * (R i / P i) by field_simp, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (hP i)]
  rw [← hlhs, ← hrhs]
  exact hamgm

/-- **Bretagnolle–Huber** for finite pmfs: `½·exp(−KL(P‖R)) ≤ Σ min(P, R)`, hence (by
`sum_min_le_errors`) any test's `δI + δII ≥ ½·exp(−KL)`. -/
theorem bretagnolle_huber (P R : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hR : ∀ i, 0 ≤ R i)
    (hP1 : ∑ i, P i = 1) (hR1 : ∑ i, R i = 1) (hac : ∀ i, R i = 0 → P i = 0) :
    Real.exp (-klPmf P R) / 2 ≤ ∑ i, min (P i) (R i) := by
  have hB := exp_neg_half_kl_le P R hP hR hP1 hac
  -- Cauchy–Schwarz: (Σ √(PR))² = (Σ √min·√max)² ≤ Σ min · Σ max
  have hsq : ∀ i, Real.sqrt (P i * R i) =
      Real.sqrt (min (P i) (R i)) * Real.sqrt (max (P i) (R i)) := by
    intro i
    rw [← Real.sqrt_mul (le_min (hP i) (hR i)), min_mul_max]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (min (P i) (R i)))
    (fun i => Real.sqrt (max (P i) (R i)))
  simp only [Real.sq_sqrt (le_min (hP _) (hR _)), Real.sq_sqrt (le_max_of_le_left (hP _))] at hCS
  rw [← Finset.sum_congr rfl fun i _ => hsq i] at hCS
  have hmax : ∑ i, max (P i) (R i) = 2 - ∑ i, min (P i) (R i) := by
    have : ∀ i, max (P i) (R i) = P i + R i - min (P i) (R i) := fun i => by
      rw [← min_add_max (P i) (R i)]; ring
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      hP1, hR1]; norm_num
  have hmin0 : 0 ≤ ∑ i, min (P i) (R i) := Finset.sum_nonneg fun i _ => le_min (hP i) (hR i)
  have hmin1 : ∑ i, min (P i) (R i) ≤ 1 := hP1 ▸ Finset.sum_le_sum fun i _ => min_le_left _ _
  have hexp : Real.exp (-klPmf P R) = Real.exp (-(klPmf P R / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hsq_le : Real.exp (-(klPmf P R / 2)) ^ 2 ≤ (∑ i, Real.sqrt (P i * R i)) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hB 2
  rw [hmax] at hCS
  rw [hexp]
  nlinarith

end Pmf

/-! ### Bernoulli KL constants -/

section BernKL

/-- Bernoulli KL in closed form on the open square. -/
lemma bkl_eq {a c : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hc0 : 0 < c) (hc1 : c < 1) :
    bkl a c = a * Real.log a + (1 - a) * Real.log (1 - a) - a * Real.log c -
      (1 - a) * Real.log (1 - c) := by
  simp only [bkl, Fintype.sum_bool, bern, if_true, Bool.false_eq_true, if_false]
  rw [Real.log_div ha0.ne' hc0.ne', Real.log_div (by linarith) (by linarith)]
  ring

/-- **`KL ≤ χ²`** for Bernoulli: `KL(Bern a ‖ Bern c) ≤ (a − c)²/(c(1−c))`. -/
lemma bkl_le_chi2 {a c : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hc0 : 0 < c) (hc1 : c < 1) :
    bkl a c ≤ (a - c) ^ 2 / (c * (1 - c)) := by
  simp only [bkl, Fintype.sum_bool, bern, if_true, Bool.false_eq_true, if_false]
  have hc1' : 0 < 1 - c := by linarith
  have k1 : a * Real.log (a / c) ≤ a * (a / c - 1) := by
    rcases eq_or_lt_of_le ha0 with h | h
    · rw [← h]; simp
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos h hc0)) ha0
  have k2 : (1 - a) * Real.log ((1 - a) / (1 - c)) ≤ (1 - a) * ((1 - a) / (1 - c) - 1) := by
    rcases eq_or_lt_of_le (show 0 ≤ 1 - a by linarith) with h | h
    · rw [← h]; simp
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos h hc1')) h.le
  have hid : a * (a / c - 1) + (1 - a) * ((1 - a) / (1 - c) - 1) = (a - c) ^ 2 / (c * (1 - c)) := by
    field_simp; ring
  linarith

/-- For fixed `a ∈ [0,1]`, `c ↦ −a log c − (1−a) log(1−c)` is convex on `(0,1)`. -/
lemma convexOn_crossEnt (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ConvexOn ℝ (Set.Ioo 0 1) (fun c => -(a * Real.log c) - (1 - a) * Real.log (1 - c)) := by
  refine ⟨convex_Ioo 0 1, fun x hx y hy s t hs ht hst => ?_⟩
  simp only [smul_eq_mul]
  have h1 := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hx.1) (Set.mem_Ioi.2 hy.1) hs ht hst
  have h2 := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 (sub_pos.2 hx.2))
    (Set.mem_Ioi.2 (sub_pos.2 hy.2)) hs ht hst
  simp only [smul_eq_mul] at h1 h2
  rw [show s * (1 - x) + t * (1 - y) = 1 - (s * x + t * y) by linear_combination hst] at h2
  have ha1' : 0 ≤ 1 - a := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 ha0, mul_le_mul_of_nonneg_left h2 ha1']

/-- For fixed `u, v`, `a ↦ a log a + (1−a) log(1−a) − a u − (1−a) v` is convex on `[0,1]`. -/
lemma convexOn_negEnt (u v : ℝ) :
    ConvexOn ℝ (Set.Icc 0 1) (fun a => a * Real.log a + (1 - a) * Real.log (1 - a) - a * u -
      (1 - a) * v) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy s t hs ht hst => ?_⟩
  simp only [smul_eq_mul]
  have h1 := Real.convexOn_mul_log.2 (Set.mem_Ici.2 hx.1) (Set.mem_Ici.2 hy.1) hs ht hst
  have h2 := Real.convexOn_mul_log.2 (Set.mem_Ici.2 (sub_nonneg.2 hx.2))
    (Set.mem_Ici.2 (sub_nonneg.2 hy.2)) hs ht hst
  simp only [smul_eq_mul] at h1 h2
  rw [show s * (1 - x) + t * (1 - y) = 1 - (s * x + t * y) by linear_combination hst] at h2
  have l1 : (s * x + t * y) * u = s * (x * u) + t * (y * u) := by ring
  have l2 : (1 - (s * x + t * y)) * v = s * ((1 - x) * v) + t * ((1 - y) * v) := by
    linear_combination (-v) * hst
  have l3 : s * (x * Real.log x + (1 - x) * Real.log (1 - x) - x * u - (1 - x) * v) +
      t * (y * Real.log y + (1 - y) * Real.log (1 - y) - y * u - (1 - y) * v) =
      s * (x * Real.log x) + t * (y * Real.log y) +
        (s * ((1 - x) * Real.log (1 - x)) + t * ((1 - y) * Real.log (1 - y))) -
        (s * (x * u) + t * (y * u)) - (s * ((1 - x) * v) + t * ((1 - y) * v)) := by ring
  rw [l3, l1, l2]
  linarith

/-- **`KL_ρ` closed form.** Over `a, c ∈ [ρ, 1−ρ]`, `KL(Bern a ‖ Bern c) ≤ (1−2ρ)·log((1−ρ)/ρ)`
(attained at the corners `(1−ρ, ρ)`, `(ρ, 1−ρ)`). -/
lemma bkl_le_corner {ρ a c : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (ha : ρ ≤ a ∧ a ≤ 1 - ρ)
    (hc : ρ ≤ c ∧ c ≤ 1 - ρ) :
    bkl a c ≤ (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) := by
  have hρ1 : 0 < 1 - ρ := by linarith
  have hρρ : ρ ≤ 1 - ρ := by linarith
  have hmem : ∀ b, ρ ≤ b ∧ b ≤ 1 - ρ → 0 < b ∧ b < 1 := fun b hb => ⟨by linarith, by linarith⟩
  set K := (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) with hK
  have hK0 : 0 ≤ K := mul_nonneg (by linarith)
    (Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith))
  have hcorner : bkl (1 - ρ) ρ = K ∧ bkl ρ (1 - ρ) = K := by
    have hL : Real.log (ρ / (1 - ρ)) = -Real.log ((1 - ρ) / ρ) := by
      rw [← Real.log_inv, inv_div]
    simp only [bkl, Fintype.sum_bool, bern, if_true, Bool.false_eq_true, if_false,
      show 1 - (1 - ρ) = ρ by ring]
    rw [hL, hK]; constructor <;> ring
  -- step 1: in `c`, bounded by the endpoint values
  have step1 : ∀ a', ρ ≤ a' ∧ a' ≤ 1 - ρ → ∀ c', ρ ≤ c' ∧ c' ≤ 1 - ρ →
      bkl a' c' ≤ max (bkl a' ρ) (bkl a' (1 - ρ)) := by
    intro a' ha' c' hc'
    obtain ⟨ha0, ha1⟩ := hmem a' ha'
    have hf := (convexOn_crossEnt a' ha0.le ha1.le).add_const
      (a' * Real.log a' + (1 - a') * Real.log (1 - a'))
    have hseg := hf.le_on_segment (hmem ρ ⟨le_rfl, hρρ⟩) (hmem (1 - ρ) ⟨hρρ, le_rfl⟩)
      (z := c') (by rw [segment_eq_Icc hρρ]; exact hc')
    have e : ∀ b, ρ ≤ b ∧ b ≤ 1 - ρ → bkl a' b =
        -(a' * Real.log b) - (1 - a') * Real.log (1 - b) +
          (a' * Real.log a' + (1 - a') * Real.log (1 - a')) := by
      intro b hb
      obtain ⟨hb0, hb1⟩ := hmem b hb
      rw [bkl_eq ha0 ha1 hb0 hb1]; ring
    rw [e c' hc', e ρ ⟨le_rfl, hρρ⟩, e (1 - ρ) ⟨hρρ, le_rfl⟩]
    exact hseg
  -- step 2: in `a`, with `c` at an endpoint
  have step2 : ∀ c', c' = ρ ∨ c' = 1 - ρ → bkl a c' ≤ K := by
    intro c' hc'
    have hc'm : ρ ≤ c' ∧ c' ≤ 1 - ρ := by rcases hc' with h | h <;> rw [h] <;> constructor <;> linarith
    obtain ⟨hc0, hc1⟩ := hmem c' hc'm
    have hf := convexOn_negEnt (Real.log c') (Real.log (1 - c'))
    have hseg := hf.le_on_segment (x := ρ) (y := 1 - ρ) ⟨hρ.le, by linarith⟩ ⟨hρ1.le, by linarith⟩
      (z := a) (by rw [segment_eq_Icc hρρ]; exact ha)
    have e : ∀ b, ρ ≤ b ∧ b ≤ 1 - ρ → bkl b c' = b * Real.log b + (1 - b) * Real.log (1 - b) -
        b * Real.log c' - (1 - b) * Real.log (1 - c') := by
      intro b hb
      obtain ⟨hb0, hb1⟩ := hmem b hb
      exact bkl_eq hb0 hb1 hc0 hc1
    rw [← e a ha, ← e ρ ⟨le_rfl, hρρ⟩, ← e (1 - ρ) ⟨hρρ, le_rfl⟩] at hseg
    refine hseg.trans (max_le ?_ ?_)
    · rcases hc' with h | h <;> rw [h]
      · rw [bkl_self]; exact hK0
      · exact hcorner.2.le
    · rcases hc' with h | h <;> rw [h]
      · exact hcorner.1.le
      · rw [bkl_self]; exact hK0
  exact (step1 a ha c hc).trans (max_le (step2 ρ (Or.inl rfl)) (step2 (1 - ρ) (Or.inr rfl)))

end BernKL

/-! ### 3. The gallery instance -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [Fintype Fine]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι]

lemma score_mem (V : ι → Fine) (x : Sph E) : -1 ≤ G.score V x ∧ G.score V x ≤ 1 := by
  have hb : ∀ j, |inner ℝ x.1 (G.g (V j))| ≤ 1 := fun j => by
    have := abs_real_inner_le_norm x.1 (G.g (V j))
    rwa [x.2, G.hg, one_mul] at this
  obtain ⟨j₀⟩ := (inferInstance : Nonempty ι)
  constructor
  · exact (abs_le.1 (hb j₀)).1.trans
      (Finset.le_sup' (f := fun j => inner ℝ x.1 (G.g (V j))) (Finset.mem_univ j₀))
  · exact Finset.sup'_le _ _ fun j _ => (abs_le.1 (hb j)).2

omit [Nonempty ι] in
lemma zeta_nonneg : 0 ≤ G.ζ := (abs_nonneg _).trans (G.hband G.thr le_rfl)

/-- Response under `H₁ : gallery = G₀ ∪ {c}`, where `G₀` is the fixed list `V`. -/
noncomputable def respWith (V : ι → Fine) (c : E) (x : Sph E) : ℝ :=
  G.κ (max (G.score V x) (inner ℝ x.1 c))

/-- Probe `x` reaches the candidate `c`: `⟨x, c⟩ > thr`. -/
def reachC (c : E) (x : Sph E) : Prop := G.thr < inner ℝ x.1 c

/-- **The note's three-case split.** Reaching rounds cost at most `Δ`; non-reaching rounds either
see identical laws (another face already above threshold) or two laws in the `ζ`-band. -/
lemma cand_cases (V : ι → Fine) (c : E) (hc : ‖c‖ = 1) (Δ : ℝ)
    (hΔ : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ∀ s' ∈ Set.Ioc G.thr 1, |G.κ (max s s') - G.κ s| ≤ Δ)
    (x : Sph E) :
    (G.reachC c x → |G.resp V x - G.respWith V c x| ≤ Δ) ∧
    (¬ G.reachC c x → |G.resp V x - G.respWith V c x| ≤ 2 * G.ζ) := by
  have hs := G.score_mem V x
  have hxc : inner ℝ x.1 c ≤ 1 := by
    have := abs_real_inner_le_norm x.1 c
    rw [x.2, hc, one_mul] at this
    exact (abs_le.1 this).2
  unfold resp respWith reachC
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · rw [abs_sub_comm]; exact hΔ _ hs _ ⟨hr, hxc⟩
  · push Not at hr
    by_cases h0 : G.thr < G.score V x
    · rw [max_eq_left (by linarith), sub_self, abs_zero]
      linarith [G.zeta_nonneg]
    · push Not at h0
      have e1 := G.hband _ h0
      have e2 := G.hband _ (max_le h0 hr)
      calc |G.κ (G.score V x) - G.κ (max (G.score V x) (inner ℝ x.1 c))|
          = |(G.κ (G.score V x) - G.ν₀) - (G.κ (max (G.score V x) (inner ℝ x.1 c)) - G.ν₀)| := by
            ring_nf
        _ ≤ |G.κ (G.score V x) - G.ν₀| + |G.κ (max (G.score V x) (inner ℝ x.1 c)) - G.ν₀| :=
            abs_sub _ _
        _ ≤ 2 * G.ζ := by linarith

open Classical in
/-- **Theorem 18.1(i), membership (coupling/TV form).** For the known candidate `c`, common faces
`V`, any adaptive attacker `probe` and any randomised decision `D` (the probability of answering
"member" after transcript `h`), with `δI := P₀[D = 1]`, `δII := P₁[D = 0]` and
`E₀[S_c]` the expected number of `c`-reaching probes under `H₀`:

  `δI + δII ≥ 1 − Δ·E₀[S_c] − 2ζQ`.

`Δ` is the note's `sup_{s∈[−1,1], s'>thr} |κ(max(s,s')) − κ(s)|` (here with `s' ≤ 1` too, which is
all that inner products of unit vectors can produce). -/
theorem membership_tv (V : ι → Fine) (c : E) (hc : ‖c‖ = 1) (Δ : ℝ)
    (hΔ : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ∀ s' ∈ Set.Ioc G.thr 1, |G.κ (max s s') - G.κ s| ≤ Δ)
    (probe : List Bool → Sph E) (Q : ℕ) (D : List Bool → ℝ) (hD : ∀ h, 0 ≤ D h ∧ D h ≤ 1) :
    1 - Δ * accCount (G.resp V) probe (G.reachC c) Q [] - 2 * Q * G.ζ ≤
      val (G.resp V) probe D Q [] + val (G.respWith V c) probe (fun h => 1 - D h) Q [] := by
  have hp₀ : ∀ x, 0 ≤ G.resp V x ∧ G.resp V x ≤ 1 := fun x => G.hκ _
  have hp₁ : ∀ x, 0 ≤ G.respWith V c x ∧ G.respWith V c x ≤ 1 := fun x => G.hκ _
  have hloc : ∀ x, |G.resp V x - G.respWith V c x| ≤
      Δ * (if G.reachC c x then 1 else 0) + 2 * G.ζ := by
    intro x
    have hcc := G.cand_cases V c hc Δ hΔ x
    have hζ := G.zeta_nonneg
    split_ifs with hr
    · linarith [hcc.1 hr]
    · linarith [hcc.2 hr]
  have htv := val_tv_cost probe _ _ hp₀ hp₁ (G.reachC c) Δ G.ζ hloc D hD Q []
  have haff := val_affine (G.respWith V c) probe 1 (-1) D Q []
  simp only [neg_one_mul, ← sub_eq_add_neg] at haff
  rw [haff]
  linarith [(abs_le.1 htv).1]

open Classical in
/-- **Theorem 18.1(ii), first half (KL form).** Under the range condition `κ ∈ [ρ, 1−ρ]` and
`ζ = 0 ∨ ζ < min(ν₀, 1−ν₀)`:

  `KL(P₀ ‖ P₁) ≤ KL_ρ · E₀[S_c] + β₀ᶜᵃᵖ · Q`,

with `KL_ρ = (1−2ρ)·log((1−ρ)/ρ)` and `β₀ᶜᵃᵖ = 4ζ²/((ν₀−ζ)(1−ν₀−ζ))`, both in the note's closed
form (`bkl_le_corner`, `bkl_le_chi2`). -/
theorem membership_kl (V : ι → Fine) (c : E) (hc : ‖c‖ = 1) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ2 : ρ ≤ 1 / 2) (hrange : ∀ s, ρ ≤ G.κ s ∧ G.κ s ≤ 1 - ρ)
    (hζ : G.ζ = 0 ∨ (G.ζ < G.ν₀ ∧ G.ζ < 1 - G.ν₀))
    (probe : List Bool → Sph E) (Q : ℕ) :
    klPmf (pathProb (G.resp V) probe Q []) (pathProb (G.respWith V c) probe Q []) ≤
      (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * accCount (G.resp V) probe (G.reachC c) Q [] +
        4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) * Q := by
  set KL := (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) with hKL
  set β₀ := 4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) with hβ₀
  have hp₀ : ∀ x, 0 ≤ G.resp V x ∧ G.resp V x ≤ 1 := fun x => G.hκ _
  have hp₁ : ∀ x, 0 ≤ G.respWith V c x ∧ G.respWith V c x ≤ 1 := fun x => G.hκ _
  have hac : ∀ x b, bern (G.respWith V c x) b = 0 → bern (G.resp V x) b = 0 := by
    intro x b hb
    exfalso
    have := hrange (max (G.score V x) (inner ℝ x.1 c))
    cases b <;> simp only [bern, Bool.false_eq_true, if_false, if_true] at hb <;>
      unfold respWith at hb <;> linarith [this.1, this.2]
  have hβ0 : 0 ≤ β₀ := by
    rcases hζ with h | ⟨h1, h2⟩
    · rw [hβ₀, h]; simp
    · exact div_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))
  have hKL0 : 0 ≤ KL := mul_nonneg (by linarith)
    (Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith))
  have hcost : ∀ x, bkl (G.resp V x) (G.respWith V c x) ≤
      KL * (if G.reachC c x then 1 else 0) + β₀ := by
    intro x
    have hcc := G.cand_cases V c hc 1 (fun s _ s' _ => by
      have h1 := G.hκ (max s s'); have h2 := G.hκ s
      exact abs_le.2 ⟨by linarith, by linarith⟩) x
    split_ifs with hr
    · have := bkl_le_corner hρ hρ2 (hrange _) (hrange _) (a := G.resp V x)
        (c := G.respWith V c x)
      linarith
    · -- quiet round: either identical laws, or both in the ζ-band
      simp only [mul_zero, zero_add]
      unfold reachC at hr
      push Not at hr
      by_cases h0 : G.thr < G.score V x
      · have : G.respWith V c x = G.resp V x := by
          unfold respWith resp; rw [max_eq_left (by linarith)]
        rw [this, bkl_self]; exact hβ0
      · push Not at h0
        have e1 := abs_le.1 (G.hband _ h0)
        have e2 := abs_le.1 (G.hband _ (max_le h0 hr))
        rcases hζ with hz | ⟨hz1, hz2⟩
        · have ha : G.resp V x = G.ν₀ := by unfold resp; rw [hz] at e1; linarith [e1.1, e1.2]
          have hb : G.respWith V c x = G.ν₀ := by
            unfold respWith; rw [hz] at e2; linarith [e2.1, e2.2]
          rw [ha, hb, bkl_self]; exact hβ0
        · set a := G.resp V x
          set b := G.respWith V c x
          have ha1 : a - G.ν₀ = G.κ (G.score V x) - G.ν₀ := rfl
          have hb1 : b - G.ν₀ = G.κ (max (G.score V x) (inner ℝ x.1 c)) - G.ν₀ := rfl
          have hbl : G.ν₀ - G.ζ ≤ b := by linarith [e2.1]
          have hbu : b ≤ G.ν₀ + G.ζ := by linarith [e2.2]
          have hb0 : 0 < b := by linarith
          have hb1' : b < 1 := by linarith
          have hchi := bkl_le_chi2 (hp₀ x).1 (hp₀ x).2 hb0 hb1'
          have hden : 0 < (G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ) := mul_pos (by linarith) (by linarith)
          have hden_le : (G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ) ≤ b * (1 - b) := by
            nlinarith [mul_nonneg (sub_nonneg.2 hbl) (show 0 ≤ 1 - G.ν₀ - G.ζ by linarith),
              mul_nonneg hb0.le (sub_nonneg.2 hbu)]
          have hnum : (a - b) ^ 2 ≤ 4 * G.ζ ^ 2 := by
            have : |a - b| ≤ 2 * G.ζ := by
              rw [abs_le]; constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
            nlinarith [abs_nonneg (a - b), sq_abs (a - b), G.zeta_nonneg]
          refine hchi.trans ?_
          rw [hβ₀]
          calc (a - b) ^ 2 / (b * (1 - b)) ≤ 4 * G.ζ ^ 2 / (b * (1 - b)) :=
                div_le_div_of_nonneg_right hnum (hden.trans_le hden_le).le
            _ ≤ 4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) :=
                div_le_div_of_nonneg_left (by positivity) hden hden_le
  rw [kl_chain hp₀ hp₁ hac Q []]
  exact klRounds_le_cost hp₀ (G.reachC c) KL β₀ hcost Q []

open Classical in
/-- **Theorem 18.1(ii), second half (Bretagnolle–Huber).**

  `δI + δII ≥ ½ · exp(−KL_ρ·E₀[S_c] − β₀ᶜᵃᵖ·Q)`. -/
theorem membership_bh (V : ι → Fine) (c : E) (hc : ‖c‖ = 1) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ2 : ρ ≤ 1 / 2) (hrange : ∀ s, ρ ≤ G.κ s ∧ G.κ s ≤ 1 - ρ)
    (hζ : G.ζ = 0 ∨ (G.ζ < G.ν₀ ∧ G.ζ < 1 - G.ν₀))
    (probe : List Bool → Sph E) (Q : ℕ) (D : List Bool → ℝ) (hD : ∀ h, 0 ≤ D h ∧ D h ≤ 1) :
    Real.exp (-((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) *
        accCount (G.resp V) probe (G.reachC c) Q [] +
        4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) * Q)) / 2 ≤
      val (G.resp V) probe D Q [] + val (G.respWith V c) probe (fun h => 1 - D h) Q [] := by
  have hp₀ : ∀ x, 0 ≤ G.resp V x ∧ G.resp V x ≤ 1 := fun x => G.hκ _
  have hp₁ : ∀ x, 0 ≤ G.respWith V c x ∧ G.respWith V c x ≤ 1 := fun x => G.hκ _
  have hac : ∀ x b, bern (G.respWith V c x) b = 0 → bern (G.resp V x) b = 0 := by
    intro x b hb
    exfalso
    have := hrange (max (G.score V x) (inner ℝ x.1 c))
    cases b <;> simp only [bern, Bool.false_eq_true, if_false, if_true] at hb <;>
      unfold respWith at hb <;> linarith [this.1, this.2]
  set P₀ := pathProb (G.resp V) probe Q []
  set P₁ := pathProb (G.respWith V c) probe Q []
  have hkl := G.membership_kl V c hc ρ hρ hρ2 hrange hζ probe Q
  have hBH := bretagnolle_huber P₀ P₁ (pathProb_nonneg probe hp₀ Q []) (pathProb_nonneg probe hp₁ Q [])
    (pathProb_sum probe hp₀ Q []) (pathProb_sum probe hp₁ Q [])
    (fun e he => pathProb_ac hac Q [] e he)
  have herr := sum_min_le_errors P₀ P₁ (fun e => D ([] ++ List.ofFn e)) (fun e => hD _)
  rw [val_eq_sum, val_eq_sum]
  refine le_trans ?_ (hBH.trans herr)
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (neg_le_neg hkl)) (by norm_num)

open Classical in
/-- **Theorem 18.1(ii), rearranged.** Any test with `δI + δII ≤ δ` needs

  `E₀[S_c] ≥ (log(1/(2δ)) − β₀ᶜᵃᵖ·Q) / KL_ρ`

candidate-reaching probes (in expectation under `H₀`), for `ρ < ½`. (`δ > 0` is automatic:
Bretagnolle–Huber makes the total error positive.) -/
theorem membership_reach_needed (V : ι → Fine) (c : E) (hc : ‖c‖ = 1) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ2 : ρ < 1 / 2) (hrange : ∀ s, ρ ≤ G.κ s ∧ G.κ s ≤ 1 - ρ)
    (hζ : G.ζ = 0 ∨ (G.ζ < G.ν₀ ∧ G.ζ < 1 - G.ν₀))
    (probe : List Bool → Sph E) (Q : ℕ) (D : List Bool → ℝ) (hD : ∀ h, 0 ≤ D h ∧ D h ≤ 1)
    (δ : ℝ)
    (herr : val (G.resp V) probe D Q [] + val (G.respWith V c) probe (fun h => 1 - D h) Q [] ≤ δ) :
    (Real.log (1 / (2 * δ)) - 4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) * Q) /
        ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ)) ≤
      accCount (G.resp V) probe (G.reachC c) Q [] := by
  have hbh := (G.membership_bh V c hc ρ hρ hρ2.le hrange hζ probe Q D hD).trans herr
  set S := accCount (G.resp V) probe (G.reachC c) Q []
  set KL := (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ)
  set β := 4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) * Q
  have hKL : 0 < KL := mul_pos (by linarith)
    (Real.log_pos (by rw [lt_div_iff₀ hρ]; linarith))
  have h2 : Real.exp (-(KL * S + β)) ≤ 2 * δ := by linarith
  have h3 := Real.log_le_log (Real.exp_pos _) h2
  rw [Real.log_exp] at h3
  have h4 : Real.log (1 / (2 * δ)) = -Real.log (2 * δ) := by
    rw [one_div, Real.log_inv]
  rw [div_le_iff₀ hKL, h4]
  linarith

/-- **Remark 18.2(b): noiseless kernels make both bounds vacuous, correctly.** If the kernel is
deterministic (`κ = 0` at or below threshold, `κ(1) = 1`) and no listed face is within threshold
of the candidate (`score(c) ≤ thr`), one probe at `x = c` decides membership with zero error of
both kinds. -/
theorem one_probe_decides (V : ι → Fine) (c : E) (hc : ‖c‖ = 1)
    (hκ0 : ∀ s ≤ G.thr, G.κ s = 0) (hκ1 : G.κ 1 = 1) (hfar : G.score V ⟨c, hc⟩ ≤ G.thr) :
    let probe : List Bool → Sph E := fun _ => ⟨c, hc⟩
    let D : List Bool → ℝ := fun h => if h = [true] then 1 else 0
    val (G.resp V) probe D 1 [] = 0 ∧ val (G.respWith V c) probe (fun h => 1 - D h) 1 [] = 0 := by
  intro probe D
  have hcc : inner ℝ c c = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hc]; norm_num
  have hs1 := (G.score_mem V ⟨c, hc⟩).2
  constructor
  · simp only [val_succ, val_zero, probe, D, resp, hκ0 _ hfar]
    simp
  · simp only [val_succ, val_zero, probe, D, respWith]
    rw [show inner ℝ (⟨c, hc⟩ : Sph E).1 c = (1 : ℝ) from hcc, max_eq_right hs1, hκ1]
    simp

end Gallery

end OracleBounds.GeneralPrior
