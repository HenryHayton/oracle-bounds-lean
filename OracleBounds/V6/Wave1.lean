import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Wave 1 — constants, inequalities and proof steps of v6 (tasks a01–a23)

Each declaration carries the task id; the statement is the locked statement from
`tasks/v6/wave1/<id>.toml` verbatim (for refuted claims: its negation). No `sorry`s.
a15 (Cap(0.3) numeric) is not done here; it stands on the Python computation (F5).
-/

namespace OracleBounds.V6.Wave1

open Real Finset

/-- a01 (Thm 10.1 constant): proved. -/
theorem a01 : (3/8 : ℝ) * (1 - 1/14) * (7/8) > 3/10 ∧ (3/10 : ℝ) > 1/5 ∧
    ((1:ℝ) - 1/16 - 1/16 = 7/8) ∧ ((1:ℝ)/16) / (7/8) = 1/14 := by
  norm_num

/-- a02 (Prop 8.3, correct reverse Markov): proved. -/
theorem a02 : ∀ (n : ℕ) (w r : Fin n → ℝ) (a b D : ℝ),
    (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 → (∀ i, 0 ≤ r i ∧ r i ≤ D) →
    b < D → a ≤ (∑ i, w i * r i) →
    (a - b) / (D - b) ≤ ∑ i ∈ Finset.univ.filter (fun i => b ≤ r i), w i := by
  intro n w r a b D hw hsum hr hbD ha
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => b ≤ r i) (fun i => w i * r i)
  have hsplitw := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => b ≤ r i) w
  have h1 : ∑ i ∈ Finset.univ.filter (fun i => b ≤ r i), w i * r i ≤
      D * ∑ i ∈ Finset.univ.filter (fun i => b ≤ r i), w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by nlinarith [hw i, (hr i).2]
  have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ b ≤ r i), w i * r i ≤
      b * ∑ i ∈ Finset.univ.filter (fun i => ¬ b ≤ r i), w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      simp only [Finset.mem_filter] at hi; nlinarith [hw i]
  set P := ∑ i ∈ Finset.univ.filter (fun i => b ≤ r i), w i
  set P' := ∑ i ∈ Finset.univ.filter (fun i => ¬ b ≤ r i), w i
  have e1 : P' = 1 - P := by linarith
  rw [e1] at h2
  rw [div_le_iff₀ (by linarith)]
  have e2 : b * (1 - P) = b - b * P := by ring
  have e3 : P * (D - b) = D * P - b * P := by ring
  linarith

/-- a03 (Prop 8.3 caveat "fraction ≥ 1/8", chordal diameter 2): REFUTED. -/
theorem a03_refuted : ¬ (∀ (n : ℕ) (w r : Fin n → ℝ),
    (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 → (∀ i, 0 ≤ r i ∧ r i ≤ 2) →
    (5/16 : ℝ) ≤ (∑ i, w i * r i) →
    (1/8 : ℝ) ≤ ∑ i ∈ Finset.univ.filter (fun i => (3/16 : ℝ) ≤ r i), w i) := by
  intro h
  have := h 2 ![9/10, 1/10] ![1/8, 2] (fun i => by fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) (fun i => by fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num)
  rw [Finset.sum_filter, Fin.sum_univ_two] at this
  norm_num at this

/-- a04 (same, with the note's diameter √2): REFUTED. -/
theorem a04_refuted : ¬ (∀ (n : ℕ) (w r : Fin n → ℝ),
    (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 → (∀ i, 0 ≤ r i ∧ r i ≤ Real.sqrt 2) →
    (5/16 : ℝ) ≤ (∑ i, w i * r i) →
    (1/8 : ℝ) ≤ ∑ i ∈ Finset.univ.filter (fun i => (3/16 : ℝ) ≤ r i), w i) := by
  intro h
  have hs : (7/5 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have := h 2 ![435/488, 53/488] ![9/50, 7/5] (fun i => by fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num)
    (fun i => by fin_cases i <;> simp <;> norm_num <;> linarith)
    (by simp [Fin.sum_univ_two]; norm_num)
  rw [Finset.sum_filter, Fin.sum_univ_two] at this
  norm_num at this

/-- a05 (Cor 6.2 absorption ⟺ Λ′ ≥ 2L): proved. -/
theorem a05 : ∀ (m Λ L : ℝ), 0 < m →
    ((3*m/8)*Λ - (m/2)*L ≥ (m/4)*(Λ - L) ↔ Λ ≥ 2*L) := by
  intro m Λ L hm
  constructor <;> intro h <;> nlinarith

/-- a06 (Cor 6.2 as stated, Λ′ > L with L ≥ log 4e): REFUTED. -/
theorem a06_refuted : ¬ (∀ (m Λ L : ℝ), 0 < m → Real.log (4 * Real.exp 1) ≤ L → Λ > L →
    (3*m/8)*Λ - (m/2)*L ≥ (m/4)*(Λ - L)) := by
  intro h
  have hL : Real.log (4 * Real.exp 1) ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h1 := Real.exp_one_lt_d9
    have h2 := Real.add_one_le_exp (10:ℝ)
    norm_num at h1 h2 ⊢
    linarith
  have := h 1 11 10 (by norm_num) hL (by norm_num)
  norm_num at this

/-- a07 (Thm 6.1 (3) proof: unhit caps ≥ M/2 under n ≤ M/2): REFUTED. -/
theorem a07_refuted : ¬ (∀ (M n : ℕ) (μ Q : ℝ), 2 ≤ n → 2 * n ≤ M → 0 ≤ μ → 0 ≤ Q → 2 * μ * Q < 1 →
    (M : ℝ) - n + 1 - Q * μ * M ≥ (M : ℝ) / 2) := by
  intro h
  have := h 4 2 (49/100) 1 le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

/-- a08 (repair: n ≤ M/4, μ₁Q ≤ 1/4): proved. -/
theorem a08 : ∀ (M n : ℕ) (μ Q : ℝ), 4 * n ≤ M → 0 ≤ μ → 0 ≤ Q → μ * Q ≤ 1/4 →
    (M : ℝ) - n + 1 - Q * μ * M ≥ (M : ℝ) / 2 := by
  intro M n μ Q hn hμ hQ hμQ
  have hn' : (4 * n : ℝ) ≤ M := by exact_mod_cast hn
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  nlinarith

/-- a09 (Prop 7.3 proof: unhit ≥ M/2 under n ≤ M/8): REFUTED. -/
theorem a09_refuted : ¬ (∀ (M n : ℕ) (μ Q : ℝ), 2 ≤ n → 8 * n ≤ M → 0 ≤ μ → 0 ≤ Q → 2 * μ * Q < 1 →
    (M : ℝ) - n + 1 - Q * μ * M ≥ (M : ℝ) / 2) := by
  intro h
  have := h 16 2 (49/100) 1 le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

/-- a10 (Prop 7.3 proof: r₀ + 3/8 < 1/2): REFUTED (equality at τ − δ ≥ 1/4). Harmless:
`OracleBounds.V6.not_near_two` works with `≤ 1/2`. -/
theorem a10_refuted : ¬ (∀ (τ δ : ℝ), δ < τ → min (1/8 : ℝ) ((τ - δ)/2) + 3/8 < 1/2) := by
  intro h
  have := h 1 0 (by norm_num)
  norm_num at this

/-- a11 (Thm 7.1 proof constants): proved. -/
theorem a11 : ∀ (M n : ℕ) (μ Q k : ℝ), 0 < M → 8 * n ≤ M → 0 ≤ μ → 0 ≤ Q → μ * Q ≤ 1/4 → 0 ≤ k →
    ((M : ℝ) - n + 1 - Q * μ * M ≥ 5 * (M : ℝ) / 8) ∧ (k * μ * M / (5 * (M : ℝ) / 8) ≤ 2 * μ * k) := by
  intro M n μ Q k hM hn hμ hQ hμQ hk
  have hn' : (8 * n : ℝ) ≤ M := by exact_mod_cast hn
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨by nlinarith, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hk hμ]

/-- a12 (Cor 4.2: M/(M−n+1) ≤ 2): proved. -/
theorem a12 : ∀ (M n : ℕ), 2 ≤ n → 2 * n ≤ M → (M : ℝ) / ((M : ℝ) - n + 1) ≤ 2 := by
  intro M n _ hn
  have hn' : (2 * n : ℝ) ≤ M := by exact_mod_cast hn
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- a13 (Cor 4.3 ratio perturbation, p ≥ 1/2 for the true process only): proved. -/
theorem a13 : ∀ (a a' p p' e : ℝ), 0 ≤ a' → a' ≤ p' → 1/2 ≤ p →
    |a - a'| ≤ e → |p - p'| ≤ e → |a / p - a' / p'| ≤ 4 * e := by
  intro a a' p p' e ha' hap hp hae hpe
  have hp0 : 0 < p := by linarith
  have he : 0 ≤ e := (abs_nonneg _).trans hae
  have hq : 0 ≤ a' / p' ∧ a' / p' ≤ 1 := by
    rcases eq_or_lt_of_le (ha'.trans hap) with h0 | h0
    · simp [← h0]
    · exact ⟨div_nonneg ha' h0.le, (div_le_one h0).2 hap⟩
  have key : a / p - a' / p' = (a - a') / p + (a' / p') * ((p' - p) / p) := by
    rcases eq_or_lt_of_le (ha'.trans hap) with h0 | h0
    · have : a' = 0 := le_antisymm (h0 ▸ hap) ha'
      subst this; rw [← h0]; simp
    · field_simp; ring
  have t1 : |(a - a') / p| ≤ 2 * e := by
    rw [abs_div, abs_of_pos hp0, div_le_iff₀ hp0]; nlinarith
  have t2 : |(p' - p) / p| ≤ 2 * e := by
    rw [abs_div, abs_of_pos hp0, div_le_iff₀ hp0, abs_sub_comm]; nlinarith
  have t3 : |(a' / p') * ((p' - p) / p)| ≤ 2 * e := by
    rw [abs_mul, abs_of_nonneg hq.1]
    nlinarith [abs_nonneg ((p' - p) / p)]
  rw [key]
  calc _ ≤ |(a - a') / p| + |(a' / p') * ((p' - p) / p)| := abs_add_le _ _
    _ ≤ 4 * e := by linarith

/-- a14 (Cor 8.1 constants 6 > 16/3, 4 > (16/3) log 2): proved. -/
theorem a14 : (6 : ℝ) > 16/3 ∧ (4 : ℝ) > 16/3 * Real.log 2 := by
  have := Real.log_two_lt_d9
  exact ⟨by norm_num, by norm_num at *; linarith⟩

/-- a16 (Lemma 11.1 trig facts): proved. -/
theorem a16 : (∀ x y : ℝ, Real.sin x ^ 2 - Real.sin y ^ 2 = Real.sin (x - y) * Real.sin (2*y + (x - y))) ∧
    (∀ a b : ℝ, |Real.sin (a + b)| ≤ |Real.sin a| + |b|) := by
  constructor
  · intro x y
    rw [show 2*y + (x - y) = x + y by ring, Real.sin_sub, Real.sin_add]
    linear_combination (Real.sin y)^2 * Real.sin_sq_add_cos_sq x - (Real.sin x)^2 * Real.sin_sq_add_cos_sq y
  · intro a b
    rw [Real.sin_add]
    calc |Real.sin a * Real.cos b + Real.cos a * Real.sin b|
        ≤ |Real.sin a * Real.cos b| + |Real.cos a * Real.sin b| := abs_add_le _ _
      _ ≤ |Real.sin a| * 1 + 1 * |b| := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one b) (abs_nonneg _))
            (mul_le_mul (Real.abs_cos_le_one a) Real.abs_sin_le_abs (abs_nonneg _) zero_le_one)
      _ = |Real.sin a| + |b| := by ring

/-- a17 (Thm 6.1 (4) Jensen step, literal reading): REFUTED. -/
theorem a17_refuted : ¬ (∀ (n x y : ℝ), 0 < n → 0 ≤ x → x ≤ y → y ≤ n →
    Real.binEntropy (min (y/n) (1/2)) ≤ Real.binEntropy (min (x/n) (1/2))) := by
  intro h
  have := h 1 0 (1/4) (by norm_num) le_rfl (by norm_num) (by norm_num)
  have hpos : 0 < Real.binEntropy (1/4) := Real.binEntropy_pos (by norm_num) (by norm_num)
  norm_num at this
  linarith

/-- `t ↦ h(min t ½)` is concave on `[0,1]`. -/
lemma concaveOn_binEntropy_min :
    ConcaveOn ℝ (Set.Icc 0 1) (fun t : ℝ => Real.binEntropy (min t (1/2))) := by
  have hmin : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) (fun t : ℝ => min t (1/2)) :=
    (concaveOn_id (convex_Icc 0 1)).inf (concaveOn_const _ (convex_Icc 0 1))
  have himg : (fun t : ℝ => min t (1/2)) '' Set.Icc 0 1 = Set.Icc 0 (1/2) := by
    ext y
    simp only [Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨t, ⟨h0, _⟩, rfl⟩; exact ⟨le_min h0 (by norm_num), min_le_right _ _⟩
    · rintro ⟨h0, h1⟩; exact ⟨y, ⟨h0, by linarith⟩, min_eq_left h1⟩
  have hg : ConcaveOn ℝ ((fun t : ℝ => min t (1/2)) '' Set.Icc 0 1) Real.binEntropy := by
    rw [himg]
    exact Real.strictConcave_binEntropy.concaveOn.subset
      (Set.Icc_subset_Icc le_rfl (by norm_num)) (convex_Icc _ _)
  have hmono : MonotoneOn Real.binEntropy ((fun t : ℝ => min t (1/2)) '' Set.Icc 0 1) := by
    rw [himg, one_div]; exact Real.binEntropy_strictMonoOn.monotoneOn
  exact hg.comp hmin hmono

/-- The function `f(t) = tΛ − n·h(min{t/n, ½})` is convex on `[0, n]`. -/
lemma convexOn_fano_bound (n Λ : ℝ) (hn : 0 < n) :
    ConvexOn ℝ (Set.Icc 0 n) (fun t => t * Λ - n * Real.binEntropy (min (t/n) (1/2))) := by
  refine ⟨convex_Icc 0 n, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : x / n ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg hx.1 hn.le, (div_le_one hn).2 hx.2⟩
  have hy' : y / n ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg hy.1 hn.le, (div_le_one hn).2 hy.2⟩
  have hc := concaveOn_binEntropy_min.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  have e : (a * x + b * y) / n = a * (x / n) + b * (y / n) := by field_simp
  rw [e]
  nlinarith

/-- a18 (repair of Thm 6.1 (4): convexity gives f(x) ≤ max(0, f(y))): proved. -/
theorem a18 : ∀ (n Λ x y : ℝ), 0 < n → 0 ≤ Λ → 0 ≤ x → x ≤ y → y ≤ n →
    x * Λ - n * Real.binEntropy (min (x/n) (1/2)) ≤
      max 0 (y * Λ - n * Real.binEntropy (min (y/n) (1/2))) := by
  intro n Λ x y hn _ hx hxy hyn
  have := (convexOn_fano_bound n Λ hn).le_max_of_mem_Icc (x := 0) (y := y) (z := x)
    ⟨le_rfl, hn.le⟩ ⟨hx.trans hxy, hyn⟩ ⟨hx, hxy⟩
  simpa using this

/-- a19 (reach containment): proved. -/
theorem a19 : ∀ (d : ℕ) (x g z : EuclideanSpace ℝ (Fin d)) (τ δ r₀ : ℝ),
    ‖x‖ = 1 → ‖g - z‖ ≤ r₀ → inner ℝ x z ≤ τ - δ - r₀ → inner ℝ x g ≤ τ - δ := by
  intro d x g z τ δ r₀ hx hg hz
  have h1 : inner ℝ x g = inner ℝ x z + inner ℝ x (g - z) := by rw [inner_sub_right]; ring
  have h2 : inner ℝ x (g - z) ≤ ‖x‖ * ‖g - z‖ := real_inner_le_norm _ _
  rw [hx, one_mul] at h2
  linarith

/-- a20 (Cor 6.2 staircase display Q ≥ m/(4nμ₁)): REFUTED. -/
theorem a20_refuted : ¬ (∀ (n m μ Q E t : ℝ), 1 ≤ m → m ≤ n → 0 < μ → 1 ≤ Q →
    m/2 ≤ E → E ≤ n → E ≤ n * min 1 (2*μ*Q) + t → 0 ≤ t → t ≤ m/8 →
    Q ≥ m / (4*n*μ)) := by
  intro h
  have hmin : min (1:ℝ) (2 * (1/100) * (75/4)) = 3/8 := by norm_num
  have := h 8 8 (1/100) (75/4) 4 1 (by norm_num) le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [hmin]; norm_num) (by norm_num) (by norm_num)
  norm_num at this

/-- a21 (repair Q ≥ 3m/(16nμ₁)): proved. -/
theorem a21 : ∀ (n m μ Q E t : ℝ), 1 ≤ m → m ≤ n → 0 < μ → 1 ≤ Q →
    m/2 ≤ E → E ≤ n → E ≤ n * min 1 (2*μ*Q) + t → 0 ≤ t → t ≤ m/8 →
    Q ≥ 3*m / (16*n*μ) := by
  intro n m μ Q E t hm hmn hμ hQ hE1 _ hE2 _ ht
  have hn : 0 < n := by linarith
  rw [ge_iff_le, div_le_iff₀ (by positivity)]
  rcases le_total 1 (2*μ*Q) with h | h
  · nlinarith
  · rw [min_eq_right h] at hE2; nlinarith

/-- a22 (Thm 6.1 (4), charitable reading: g nondecreasing, Λ ≥ 100): REFUTED. -/
theorem a22_refuted : ¬ (∀ (n Λ x y : ℝ), 0 < n → 100 ≤ Λ → 0 ≤ x → x ≤ y → y ≤ n →
    x * Λ - n * Real.binEntropy (min (x/n) (1/2)) ≤
      y * Λ - n * Real.binEntropy (min (y/n) (1/2))) := by
  intro h
  set y := Real.exp (-200) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hy1 : y < 1/2 := by
    have := Real.exp_lt_one_iff.2 (by norm_num : (-200:ℝ) < 0)
    have h2 := Real.add_one_le_exp (-200 : ℝ)
    -- exp(−200) ≤ exp(−1) < 1/2
    have h3 : Real.exp (-200) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by norm_num)
    have h4 : Real.exp (-1) < 1/2 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.exp_one_gt_d9; norm_num at this ⊢; linarith
    linarith
  have := h 1 100 0 y (by norm_num) le_rfl le_rfl hy0.le (by linarith)
  simp only [div_one, zero_mul, Real.binEntropy_zero, min_eq_left (by norm_num : (0:ℝ) ≤ 1/2),
    min_eq_left hy1.le, mul_zero, sub_zero, one_mul] at this
  -- h(y) ≥ y·log(1/y) = 200·y
  have hent : 200 * y ≤ Real.binEntropy y := by
    unfold Real.binEntropy
    have hlog : Real.log y⁻¹ = 200 := by rw [Real.log_inv, hy, Real.log_exp]; norm_num
    have h2 : 0 ≤ (1 - y) * Real.log (1 - y)⁻¹ := by
      apply mul_nonneg (by linarith)
      apply Real.log_nonneg
      rw [one_le_inv₀ (by linarith)]; linarith
    rw [hlog]; linarith
  linarith

/-- a23 (Cor 6.2 absorption with the correct entropy term): proved. -/
theorem a23 : ∀ (m Λ L : ℝ), 0 < m →
    ((3*m/8)*Λ - (m/2)*(L - Real.log 2) ≥ (m/4)*(Λ - L) ↔ Λ ≥ 2*L - 4 * Real.log 2) := by
  intro m Λ L hm
  constructor <;> intro h <;> nlinarith

end OracleBounds.V6.Wave1
