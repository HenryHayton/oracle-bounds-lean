import OracleBounds.GeneralPrior.BudgetBest
import OracleBounds.GeneralPrior.RecoveryCount

/-!
# Corollaries 6.2, 6.3, 8.1 as stated in `n-face-general-prior-v2`

The attacker makes `Q` adaptive probes (`probe`), then outputs `k_out` points `out e` as a
function of the transcript `e`. Face `i` is *recovered at `ε`* if some output is within `ε` of it;
`N_ε` counts recovered faces; the risk is `R = (1/n) Σᵢ minⱼ ‖ĝⱼ − gᵢ‖`. All expectations are over
the gallery `V ∼ ∏πᵢ` and the transcript.

* `thm61_3` — Thm 6.1(3): `E[N_ε] ≤ n(Q(μ₁+2ζ) + k_out·p(ε))`;
* `thm61_4` — Thm 6.1(4) with the canonical budget: `x·Λ(ε) ≤ B_best(Q) + n·h(min{x/n, ½})`;
* `markov` — `P[N_ε ≥ m] ≥ ½ ⇒ E[N_ε] ≥ m/2`;
* `cor62_i`, `cor62_ii` — Cor 6.2 (staircase and information branches);
* `cor63` — Cor 6.3, all five branches `Q₁, Q₂, Q₂′, Q₃, Q₄` (division-free), and `cor63_min`
  — the note's `min{·,·}` forms where the denominators are positive;
* `lemma80`, `cor81_plateau`, `cor81_decay`, `cor81_decay_sup`, `cor81_prior_free` — Lemma 8.0
  and Cor 8.1.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

/-! ### Algebra for the inversions -/

lemma log_le_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← Real.log_rpow hs, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt hx.le]
  have h2 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt x / 2 by positivity)
  rw [Real.log_div hs.ne' (by norm_num)] at h2
  have h3 := Real.log_two_lt_d9
  norm_num at h3
  linarith

lemma two_term {a b R : ℝ} (h : R ≤ a + b) : R ≤ 2 * a ∨ R ≤ 2 * b := by
  by_contra hc
  push Not at hc
  linarith [hc.1, hc.2]

lemma sqrt_div_le {c R Q : ℝ} (hc : 0 < c) (hQ : 0 ≤ Q) (h : R ≤ c * Q ^ 2) :
    Real.sqrt (R / c) ≤ Q :=
  calc Real.sqrt (R / c) ≤ Real.sqrt (Q ^ 2) :=
        Real.sqrt_le_sqrt (by rw [div_le_iff₀ hc]; linarith)
    _ = Q := Real.sqrt_sq hQ

lemma cbrt_le {y Q : ℝ} (hy : 0 ≤ y) (hQ : 0 ≤ Q) (h : y ≤ Q ^ 3) : y ^ ((1 : ℝ) / 3) ≤ Q := by
  have := Real.rpow_le_rpow hy h (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [← Real.rpow_natCast, ← Real.rpow_mul hQ, show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num,
    Real.rpow_one] at this

/-- The `Q₄` inversion (Cor 6.3 proof): from `R ≤ S·log(2eQ/S)` with `S ≤ Q`, `S ≤ aQ²`, either
`aQ ≥ 1` or `R² ≤ 2e·a·Q³`. -/
lemma q4_branch {a R S : ℝ} {Q : ℕ} (ha : 0 ≤ a) (hR : 0 < R) (hS0 : 0 ≤ S)
    (hSa : S ≤ a * (Q : ℝ) ^ 2) (h : R ≤ S * Real.log (2 * Real.exp 1 * Q / S)) :
    1 ≤ a * Q ∨ R ^ 2 ≤ 2 * Real.exp 1 * a * (Q : ℝ) ^ 3 := by
  by_cases h1 : 1 ≤ a * Q
  · exact Or.inl h1
  right
  push Not at h1
  have hSpos : 0 < S := by
    rcases eq_or_lt_of_le hS0 with h0 | h0
    · exfalso
      have : S * Real.log (2 * Real.exp 1 * Q / S) = 0 := by rw [← h0, zero_mul]
      linarith
    · exact h0
  have ha0 : 0 < a * (Q : ℝ) ^ 2 := hSpos.trans_le hSa
  have hapos : 0 < a := lt_of_le_of_ne ha (by rintro rfl; simp at ha0)
  have hQ : (0 : ℝ) < Q := lt_of_le_of_ne (Nat.cast_nonneg _) (by
    intro h0; rw [← h0] at ha0; simp at ha0)
  have hle2 : a * (Q : ℝ) ^ 2 ≤ 2 * Q := by nlinarith
  have hmono := tlog_mono hSpos hSa (A := 2 * Real.exp 1 * Q)
    (by nlinarith [Real.exp_pos 1, mul_le_mul_of_nonneg_left hle2 (Real.exp_pos 1).le])
  have hX : 0 < 2 * Real.exp 1 * Q / (a * (Q : ℝ) ^ 2) := by positivity
  have hls := log_le_sqrt hX
  have hR1 : R ≤ a * (Q : ℝ) ^ 2 * Real.sqrt (2 * Real.exp 1 * Q / (a * (Q : ℝ) ^ 2)) :=
    h.trans (hmono.trans (mul_le_mul_of_nonneg_left hls ha0.le))
  have hR2 := pow_le_pow_left₀ hR.le hR1 2
  rw [mul_pow, Real.sq_sqrt hX.le] at hR2
  have e : (a * (Q : ℝ) ^ 2) ^ 2 * (2 * Real.exp 1 * Q / (a * (Q : ℝ) ^ 2)) =
      2 * Real.exp 1 * a * (Q : ℝ) ^ 3 := by
    field_simp
  linarith

lemma log_two_e {n m : ℝ} (hn : 0 < n) (hm : 0 < m) :
    Real.log (2 * Real.exp 1 * n / m) = 1 + Real.log (2 * n / m) := by
  rw [show 2 * Real.exp 1 * n / m = Real.exp 1 * (2 * n / m) by ring,
    Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]

/-! ### The attack on the gallery -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι] [Nonempty Fine]
variable (probe : List Bool → Sph E) {Q : ℕ} {kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)

/-- Joint weight of gallery `v` and transcript `e`. -/
noncomputable def wt (v : ι → Fine) (e : Fin Q → Bool) : ℝ :=
  G.prior v * pathProb (G.resp v) probe Q [] e

lemma wt_nonneg (v : ι → Fine) (e : Fin Q → Bool) : 0 ≤ G.wt probe v e :=
  mul_nonneg (G.prior_nonneg v) (pathProb_nonneg probe (G.resp_mem v) Q [] e)

lemma wt_sum : ∑ v, ∑ e, G.wt probe (Q := Q) v e = 1 := by
  unfold wt
  simp only [← Finset.mul_sum, pathProb_sum probe (G.resp_mem _), mul_one]
  exact G.prior_sum

/-- Face `i` is recovered at `ε` (Def 1.5, closed balls). -/
def recovered (ε : ℝ) (i : ι) (v : ι → Fine) (e : Fin Q → Bool) : Prop :=
  ∃ j, ‖(out e j).1 - G.g (v i)‖ ≤ ε

open Classical in
/-- `N_ε`, the number of recovered faces. -/
noncomputable def Ncount (ε : ℝ) (v : ι → Fine) (e : Fin Q → Bool) : ℝ :=
  ((Finset.univ.filter fun i => G.recovered out ε i v e).card : ℝ)

open Classical in
/-- `E[N_ε]`. -/
noncomputable def EN (ε : ℝ) : ℝ := ∑ v, ∑ e, G.wt probe v e * G.Ncount out ε v e

open Classical in
/-- `P[N_ε ≥ m]`. -/
noncomputable def PN (ε m : ℝ) : ℝ :=
  ∑ v, ∑ e, G.wt probe v e * (if m ≤ G.Ncount out ε v e then 1 else 0)

lemma Ncount_mem (ε : ℝ) (v : ι → Fine) (e : Fin Q → Bool) :
    0 ≤ G.Ncount out ε v e ∧ G.Ncount out ε v e ≤ Fintype.card ι := by
  classical
  unfold Ncount
  refine ⟨Nat.cast_nonneg _, ?_⟩
  exact_mod_cast Finset.card_filter_le _ _

lemma EN_le_n (ε : ℝ) : G.EN probe out ε ≤ Fintype.card ι := by
  classical
  unfold EN
  calc ∑ v, ∑ e, G.wt probe v e * G.Ncount out ε v e
      ≤ ∑ v, ∑ e, G.wt probe v e * Fintype.card ι :=
        Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun e _ =>
          mul_le_mul_of_nonneg_left (G.Ncount_mem out ε v e).2 (G.wt_nonneg probe v e)
    _ = Fintype.card ι := by
        simp only [← Finset.sum_mul]; rw [G.wt_sum probe, one_mul]

/-- Outputs read off a `List Bool` history (for the `val` formulation). -/
def outL (h : List Bool) : Fin kout → Sph E := out (fun t => h.getD t.1 false)

lemma outL_ofFn (e : Fin Q → Bool) : outL out ([] ++ List.ofFn e) = out e := by
  unfold outL; simp

open Classical in
/-- `E[N_ε] = Σᵢ P[face i recovered]` (linearity). -/
lemma EN_eq_faces (ε : ℝ) : G.EN probe out ε =
    ∑ i, ∑ v, ∑ e, G.wt probe v e * (if G.recovered out ε i v e then (1 : ℝ) else 0) := by
  have h1 : ∀ v, ∑ e, G.wt probe v e * G.Ncount out ε v e =
      ∑ i, ∑ e, G.wt probe v e * (if G.recovered out ε i v e then (1 : ℝ) else 0) := by
    intro v
    unfold Ncount
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  unfold EN
  rw [Finset.sum_congr rfl fun v _ => h1 v]
  exact Finset.sum_comm

open Classical in
/-- `E[N_ε]` in the `val` form used by the coupling bounds. -/
lemma EN_eq_val (ε : ℝ) : G.EN probe out ε = ∑ i, ∑ v, G.prior v * val (G.resp v) probe
    (fun h => if ∃ j, ‖(outL out h j).1 - G.g (v i)‖ ≤ ε then (1 : ℝ) else 0) Q [] := by
  rw [G.EN_eq_faces]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => ?_
  rw [val_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [outL_ofFn]
  unfold wt recovered
  ring_nf

open Classical in
/-- **Theorem 6.1(3).** `E[N_ε] ≤ n(Q(μ₁+2ζ) + k_out·p(ε))`. -/
theorem thm61_3 (μ₁ ε pε : ℝ) (hμ : 0 ≤ μ₁) (hp : 0 ≤ pε)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ pε) :
    G.EN probe out ε ≤ Fintype.card ι * (Q * (μ₁ + 2 * G.ζ) + kout * pε) := by
  rw [G.EN_eq_val]
  calc _ ≤ ∑ _i : ι, (Q * (μ₁ + 2 * G.ζ) + kout * pε) := Finset.sum_le_sum fun i _ =>
        G.gallery_recovery i probe kout (outL out) Q μ₁ ε pε hμ hp (hcov i) (hballcov i)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

open Classical in
/-- `E[N_ε] = Σᵢ Pᵢ` with `Pᵢ` in `recovery_count_budget`'s form. -/
lemma EN_eq_P (ε : ℝ) :
    G.EN probe out ε = ∑ i, ∑ le : Fine × (Fin Q → Bool),
      (if le.1 ∈ Finset.univ.filter (fun a => ∃ j, ‖(out le.2 j).1 - G.g a‖ ≤ ε) then
        ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = le.1),
          (∏ j, G.π j (v j)) * pathProb (G.resp v) probe Q [] le.2 else 0) := by
  rw [G.EN_eq_faces]
  refine Finset.sum_congr rfl fun i _ => ?_
  set H : (ι → Fine) → (Fin Q → Bool) → ℝ :=
    fun v e => G.wt probe v e * (if G.recovered out ε i v e then (1 : ℝ) else 0) with hH
  have hpt : ∀ l e, (if l ∈ Finset.univ.filter (fun a => ∃ j, ‖(out e j).1 - G.g a‖ ≤ ε) then
        ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = l),
          (∏ j, G.π j (v j)) * pathProb (G.resp v) probe Q [] e else 0) =
      ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = l), H v e := by
    intro l e
    split_ifs with hl
    · refine Finset.sum_congr rfl fun v hv => ?_
      have hvi := (Finset.mem_filter.1 hv).2
      rw [Finset.mem_filter] at hl
      simp only [hH, wt, prior, recovered, hvi, if_pos hl.2, mul_one]
    · refine (Finset.sum_eq_zero fun v hv => ?_).symm
      have hvi := (Finset.mem_filter.1 hv).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp only [hH, recovered, hvi, if_neg hl, mul_zero]
  have hfib : ∀ e, ∑ l, ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = l), H v e =
      ∑ v, H v e := fun e => by
    convert Finset.sum_fiberwise Finset.univ (fun v : ι → Fine => v i) (fun v => H v e)
  rw [Fintype.sum_prod_type]
  simp only [hpt]
  symm
  calc ∑ l, ∑ e, ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = l), H v e
      = ∑ e, ∑ l, ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = l), H v e :=
        Finset.sum_comm
    _ = ∑ e, ∑ v, H v e := Finset.sum_congr rfl fun e _ => hfib e
    _ = ∑ v, ∑ e, H v e := Finset.sum_comm

lemma jointInfo_nonneg : 0 ≤ G.jointInfo probe Q := by
  unfold jointInfo
  refine Info.mutualInfo_nonneg _ (fun te => G.wt_nonneg probe te.1 te.2) ?_
  rw [Fintype.sum_prod_type]
  exact G.wt_sum probe

lemma Lambda_nonneg {kout : ℕ} {pε : ℝ} (hp : 0 ≤ pε) (hkp : (kout : ℝ) * pε < 1) :
    0 ≤ Real.log (1 / ((kout : ℝ) * pε)) := by
  rcases eq_or_lt_of_le (mul_nonneg (Nat.cast_nonneg kout) hp) with h | h
  · rw [← h]; simp
  · exact Real.log_nonneg (by rw [le_div_iff₀ h]; linarith)

open Classical in
/-- **Theorem 6.1(4) with `B = B_best(Q)`.** With `x = E[N_ε]` and `Λ(ε) = log(1/(k_out·p(ε)))`
(`k_out·p(ε) < 1`): `x·Λ(ε) ≤ B_best(Q) + n·h(min{x/n, ½})`. -/
theorem thm61_4 (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (ε pε : ℝ) (hp : 0 ≤ pε) (hkp : (kout : ℝ) * pε < 1)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ pε) :
    G.EN probe out ε * Real.log (1 / ((kout : ℝ) * pε)) ≤
      Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q + (Fintype.card ι : ℝ) *
        Real.binEntropy (min (G.EN probe out ε / Fintype.card ι) (1 / 2)) := by
  have hB := G.info_le_Bbest hν βstar hβ μ₁ hμ hcov probe Q
  unfold jointInfo prior at hB
  have h := recovery_count_budget G.π G.hπ0 G.hπ1 G.resp (fun v x => G.resp_mem v x) probe Q _ hB
    (fun l (y : Sph E) => ‖y.1 - G.g l‖ ≤ ε) kout out pε hp hkp (fun i c => hballcov i c)
  simp only at h
  rw [G.EN_eq_P probe out ε]
  exact h

open Classical in
/-- **Markov**: `P[N_ε ≥ m] ≥ ½ ⇒ E[N_ε] ≥ m/2`. -/
theorem markov (ε m : ℝ) (hm : 0 ≤ m) (h : 1 / 2 ≤ G.PN probe out ε m) :
    m / 2 ≤ G.EN probe out ε := by
  have hle : m * G.PN probe out ε m ≤ G.EN probe out ε := by
    unfold PN EN
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    have hw := G.wt_nonneg probe v e
    have hN := (G.Ncount_mem out ε v e).1
    split_ifs with hmN
    · nlinarith
    · nlinarith
  nlinarith

open Classical in
/-- **Corollary 6.2(i) (staircase branch).** If `P[N_ε ≥ m] ≥ ½` then
`nQ(μ₁+2ζ) ≥ m/2 − n·k_out·p(ε)`; if moreover `n·k_out·p(ε) ≤ m/8`, then `nQ(μ₁+2ζ) ≥ 3m/8`,
i.e. `Q ≥ 3m/(8n(μ₁+2ζ))` (and if `μ₁ + 2ζ = 0` no `Q` works, since `m ≥ 1`). -/
theorem cor62_i (μ₁ ε pε : ℝ) (hμ : 0 ≤ μ₁) (hp : 0 ≤ pε)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ pε)
    (m : ℝ) (hm : 1 ≤ m) (hPN : 1 / 2 ≤ G.PN probe out ε m) :
    m / 2 - Fintype.card ι * kout * pε ≤ Fintype.card ι * Q * (μ₁ + 2 * G.ζ) ∧
    (Fintype.card ι * kout * pε ≤ m / 8 → 3 * m / 8 ≤ Fintype.card ι * Q * (μ₁ + 2 * G.ζ)) ∧
    (Fintype.card ι * kout * pε ≤ m / 8 → 0 < μ₁ + 2 * G.ζ →
      3 * m / (8 * Fintype.card ι * (μ₁ + 2 * G.ζ)) ≤ Q) := by
  have hx := G.markov probe out ε m (by linarith) hPN
  have h3 := G.thm61_3 probe out μ₁ ε pε hμ hp hcov hballcov
  have h1 : m / 2 - Fintype.card ι * kout * pε ≤ Fintype.card ι * Q * (μ₁ + 2 * G.ζ) := by
    nlinarith
  refine ⟨h1, fun hs => by linarith, fun hs hμ' => ?_⟩
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ (by positivity)]
  nlinarith

open Classical in
/-- **Corollary 6.2(ii) (information branch).** If `P[N_ε ≥ m] ≥ ½`, `1 ≤ m ≤ n`,
`k_out·p(ε) < 1`, `L := log(2en/m)`: unconditionally `B_best(Q) ≥ (m/8)(3Λ(ε) − 4L)`, and if
`Λ(ε) ≥ L`, `B_best(Q) ≥ R := (m/2)(Λ(ε) − L)`. -/
theorem cor62_ii (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (ε pε : ℝ) (hp : 0 ≤ pε) (hkp : (kout : ℝ) * pε < 1)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ pε)
    (m : ℝ) (hm : 1 ≤ m) (hmn : m ≤ Fintype.card ι) (hPN : 1 / 2 ≤ G.PN probe out ε m) :
    m / 8 * (3 * Real.log (1 / ((kout : ℝ) * pε)) -
        4 * Real.log (2 * Real.exp 1 * Fintype.card ι / m)) ≤
      Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q ∧
    (Real.log (2 * Real.exp 1 * Fintype.card ι / m) ≤ Real.log (1 / ((kout : ℝ) * pε)) →
      m / 2 * (Real.log (1 / ((kout : ℝ) * pε)) -
        Real.log (2 * Real.exp 1 * Fintype.card ι / m)) ≤
      Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q) := by
  set n : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hn
  set Λ := Real.log (1 / ((kout : ℝ) * pε)) with hΛ
  set B := Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q with hBdef
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hxm := G.markov probe out ε m (by linarith) hPN
  have hxn := G.EN_le_n probe out ε
  have h4 := G.thm61_4 probe out hν βstar hβ μ₁ hμ hcov ε pε hp hkp hballcov
  have cv := Info.cor62_v7 n m Λ 1 B B (G.EN probe out ε) hm one_pos le_rfl hxm hxn
    (by rw [one_mul]; exact h4)
  have hL : Real.log (2 * Real.exp 1 * n / m) = 1 + Real.log (2 * n / m) :=
    log_two_e hn0 (by linarith)
  have hB0 : 0 ≤ B := (G.jointInfo_nonneg probe).trans (G.info_le_Bbest hν βstar hβ μ₁ hμ hcov probe Q)
  have hΛ0 : 0 ≤ Λ := Lambda_nonneg hp hkp
  have hL0 : 0 ≤ Real.log (2 * Real.exp 1 * n / m) :=
    Real.log_nonneg (by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [Real.add_one_le_exp (1 : ℝ)])
  have hii : Real.log (2 * Real.exp 1 * n / m) ≤ Λ →
      m / 2 * (Λ - Real.log (2 * Real.exp 1 * n / m)) ≤ B := by
    intro hLΛ
    have := cv.2 (by rw [← hL]; exact hLΛ)
    rw [hL]
    simpa using this
  refine ⟨?_, hii⟩
  rcases le_or_gt (Real.log (2 * Real.exp 1 * n / m)) Λ with h | h
  · have := hii h
    nlinarith
  · nlinarith

open Classical in
/-- **Corollary 6.3 (explicit inversion), all branches.** Under Cor 6.2(ii)'s hypotheses with
`Λ(ε) ≥ L`, `R := (m/2)(Λ(ε) − L)`, `μ′ := μ₁ + 2ζ`, `β̃ := log(1/(ν₀ ∧ (1−ν₀)))`,
`β₀ := ζ²/(ν₀(1−ν₀))`:

* `Q₁`: `Q ≥ R/β*`;
* `Q₂` (`ν₀ ∈ (0,1)`): `Q ≥ R/(β̃ + β₀)`;
* `Q₂′` (`ν₀ ∈ (0,1)`): `R ≤ 2β̃·nμ′Q²` or `R ≤ 2β₀Q`;
* `Q₃` (`0 < ζ < ½`): `R ≤ 2·log(1/ζ)·nμ′Q²` or `R ≤ 16ζQ`;
* `Q₄` (`ζ = 0`, `Λ > L`): `nμ₁Q ≥ 1` or `R² ≤ 2e·nμ₁·Q³`.

The disjunctions are the note's `Q ≥ min{·,·}` without the `c/0 := +∞` convention; `cor63_min`
gives the `min` forms. -/
theorem cor63 (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (ε pε : ℝ) (hp : 0 ≤ pε) (hkp : (kout : ℝ) * pε < 1)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ pε)
    (m : ℝ) (hm : 1 ≤ m) (hmn : m ≤ Fintype.card ι) (hPN : 1 / 2 ≤ G.PN probe out ε m)
    (hLΛ : Real.log (2 * Real.exp 1 * Fintype.card ι / m) ≤ Real.log (1 / ((kout : ℝ) * pε))) :
    let n : ℝ := Fintype.card ι
    let R := m / 2 * (Real.log (1 / ((kout : ℝ) * pε)) - Real.log (2 * Real.exp 1 * n / m))
    let μ' := μ₁ + 2 * G.ζ
    let βt := Real.log (1 / min G.ν₀ (1 - G.ν₀))
    let β₀ := G.ζ ^ 2 / (G.ν₀ * (1 - G.ν₀))
    (0 < βstar → R / βstar ≤ Q) ∧
    (0 < G.ν₀ → G.ν₀ < 1 → R / (βt + β₀) ≤ Q) ∧
    (0 < G.ν₀ → G.ν₀ < 1 → R ≤ 2 * (βt * (n * μ' * (Q : ℝ) ^ 2)) ∨ R ≤ 2 * (β₀ * Q)) ∧
    (0 < G.ζ → G.ζ < 1 / 2 →
      R ≤ 2 * (Real.log (1 / G.ζ) * (n * μ' * (Q : ℝ) ^ 2)) ∨ R ≤ 2 * (8 * G.ζ * Q)) ∧
    (G.ζ = 0 → Real.log (2 * Real.exp 1 * n / m) < Real.log (1 / ((kout : ℝ) * pε)) →
      1 ≤ n * μ₁ * Q ∨ R ^ 2 ≤ 2 * Real.exp 1 * (n * μ₁) * (Q : ℝ) ^ 3) := by
  intro n R μ' βt β₀
  have hRB : R ≤ Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q :=
    (G.cor62_ii probe out hν βstar hβ μ₁ hμ hcov ε pε hp hkp hballcov m hm hmn hPN).2 hLΛ
  have hn0 : 0 < n := by show (0 : ℝ) < (Fintype.card ι : ℝ); exact_mod_cast Fintype.card_pos
  have hζ := G.zeta_nonneg
  set S := Sn (Fintype.card ι) (μ₁ + 2 * G.ζ) Q with hS
  have hnμ : 0 ≤ n * μ' := mul_nonneg hn0.le (by linarith)
  have hS0 : 0 ≤ S := Sn_nonneg hnμ Q
  have hSQ : S ≤ Q := Sn_le_Q _ _ Q
  have hSsq : S ≤ n * μ' * (Q : ℝ) ^ 2 := Sn_le_sq hnμ Q
  unfold Bbest at hRB
  rw [← hS] at hRB
  obtain ⟨h1, h2, h3, h4⟩ : R ≤ Q * βstar ∧ R ≤ Bform2 S G.ζ G.ν₀ βstar Q ∧
      R ≤ Bform3 S G.ζ Q ∧ R ≤ Bform4 S G.ζ βstar Q := by
    simp only [le_min_iff] at hRB; exact ⟨hRB.1, hRB.2.1, hRB.2.2.1, hRB.2.2.2⟩
  have hβt : ∀ (_ : 0 < G.ν₀) (_ : G.ν₀ < 1), 0 < βt := fun h0 h1' => by
    have hmin : 0 < min G.ν₀ (1 - G.ν₀) := lt_min h0 (by linarith)
    exact Real.log_pos (by rw [lt_div_iff₀ hmin]; linarith [min_le_left G.ν₀ (1 - G.ν₀)])
  have hform2 : ∀ (h0 : 0 < G.ν₀) (h1' : G.ν₀ < 1), R ≤ βt * S + β₀ * Q := fun h0 h1' => by
    have := h2; unfold Bform2 at this; rwa [if_pos ⟨h0, h1'⟩] at this
  refine ⟨fun hb => by rw [div_le_iff₀ hb]; linarith, fun h0 h1' => ?_, fun h0 h1' => ?_,
    fun hz0 hz1 => ?_, fun hz hΛ => ?_⟩
  · -- Q₂
    have hb0 : 0 ≤ β₀ := div_nonneg (sq_nonneg _) (mul_nonneg h0.le (by linarith))
    rw [div_le_iff₀ (by linarith [hβt h0 h1'])]
    nlinarith [mul_le_mul_of_nonneg_left hSQ (hβt h0 h1').le, hform2 h0 h1']
  · -- Q₂′
    exact two_term ((hform2 h0 h1').trans (by
      nlinarith [mul_le_mul_of_nonneg_left hSsq (hβt h0 h1').le]))
  · -- Q₃: the θ-form at θ = 2ζ
    have hθ := Bform3_le hS0 hζ Q (2 * G.ζ) ⟨by linarith, by linarith⟩
    have e1 : Real.log (2 / (2 * G.ζ)) = Real.log (1 / G.ζ) := by
      congr 1; field_simp
    have e2 : 2 * G.ζ + 4 * G.ζ + 4 * G.ζ ^ 2 / (2 * G.ζ) = 8 * G.ζ := by
      field_simp; ring
    rw [e1, e2] at hθ
    have hl : 0 ≤ Real.log (1 / G.ζ) :=
      Real.log_nonneg (by rw [le_div_iff₀ hz0]; linarith)
    exact two_term (h3.trans (hθ.trans (by nlinarith [mul_le_mul_of_nonneg_left hSsq hl])))
  · -- Q₄
    have h4' : R ≤ S * Real.log (2 * Real.exp 1 * Q / S) := by
      have := h4; unfold Bform4 at this; rwa [if_pos hz] at this
    have hR : 0 < R := by
      have : 0 < m / 2 := by linarith
      exact mul_pos this (by linarith)
    have hSa : S ≤ n * μ₁ * (Q : ℝ) ^ 2 := by
      have := hSsq; simp only [μ', hz, mul_zero, add_zero] at this; exact this
    exact q4_branch (mul_nonneg hn0.le hμ) hR hS0 hSa h4'

open Classical in
/-- **Corollary 6.3, the note's `min` forms** (where the denominators are positive):
`Q ≥ min{√(R/(2β̃nμ′)), R/(2β₀)}`, `Q ≥ min{√(R/(2nμ′·log(1/ζ))), R/(16ζ)}`,
`Q ≥ min{1/(nμ₁), (R²/(2enμ₁))^{1/3}}`; and `Q₄`'s degenerate case: if `ζ = 0`, `μ₁ = 0` and
`Λ > L`, no `Q` achieves the premise. -/
theorem cor63_min (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (ε pε : ℝ) (hp : 0 ≤ pε) (hkp : (kout : ℝ) * pε < 1)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ pε)
    (m : ℝ) (hm : 1 ≤ m) (hmn : m ≤ Fintype.card ι) (hPN : 1 / 2 ≤ G.PN probe out ε m)
    (hLΛ : Real.log (2 * Real.exp 1 * Fintype.card ι / m) ≤ Real.log (1 / ((kout : ℝ) * pε))) :
    let n : ℝ := Fintype.card ι
    let R := m / 2 * (Real.log (1 / ((kout : ℝ) * pε)) - Real.log (2 * Real.exp 1 * n / m))
    let μ' := μ₁ + 2 * G.ζ
    let βt := Real.log (1 / min G.ν₀ (1 - G.ν₀))
    let β₀ := G.ζ ^ 2 / (G.ν₀ * (1 - G.ν₀))
    (0 < G.ν₀ → G.ν₀ < 1 → 0 < G.ζ →
      min (Real.sqrt (R / (2 * βt * n * μ'))) (R / (2 * β₀)) ≤ Q) ∧
    (0 < G.ζ → G.ζ < 1 / 2 →
      min (Real.sqrt (R / (2 * n * μ' * Real.log (1 / G.ζ)))) (R / (16 * G.ζ)) ≤ Q) ∧
    (G.ζ = 0 → Real.log (2 * Real.exp 1 * n / m) < Real.log (1 / ((kout : ℝ) * pε)) → 0 < μ₁ →
      min (1 / (n * μ₁)) ((R ^ 2 / (2 * Real.exp 1 * n * μ₁)) ^ ((1 : ℝ) / 3)) ≤ Q) ∧
    (G.ζ = 0 → μ₁ = 0 →
      Real.log (2 * Real.exp 1 * n / m) < Real.log (1 / ((kout : ℝ) * pε)) → False) := by
  intro n R μ' βt β₀
  have hc := G.cor63 probe out hν βstar hβ μ₁ hμ hcov ε pε hp hkp hballcov m hm hmn hPN hLΛ
  have hQ2' : 0 < G.ν₀ → G.ν₀ < 1 →
      R ≤ 2 * (βt * (n * μ' * (Q : ℝ) ^ 2)) ∨ R ≤ 2 * (β₀ * Q) := hc.2.2.1
  have hQ3 : 0 < G.ζ → G.ζ < 1 / 2 →
      R ≤ 2 * (Real.log (1 / G.ζ) * (n * μ' * (Q : ℝ) ^ 2)) ∨ R ≤ 2 * (8 * G.ζ * Q) := hc.2.2.2.1
  have hQ4 : G.ζ = 0 → Real.log (2 * Real.exp 1 * n / m) < Real.log (1 / ((kout : ℝ) * pε)) →
      1 ≤ n * μ₁ * Q ∨ R ^ 2 ≤ 2 * Real.exp 1 * (n * μ₁) * (Q : ℝ) ^ 3 := hc.2.2.2.2
  have hn0 : 0 < n := by show (0 : ℝ) < (Fintype.card ι : ℝ); exact_mod_cast Fintype.card_pos
  have hζ := G.zeta_nonneg
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  refine ⟨fun h0 h1 hz => ?_, fun hz0 hz1 => ?_, fun hz hΛ hμ0 => ?_, fun hz hμ0 hΛ => ?_⟩
  · have hmin : 0 < min G.ν₀ (1 - G.ν₀) := lt_min h0 (by linarith)
    have hβt : 0 < βt :=
      Real.log_pos (by rw [lt_div_iff₀ hmin]; linarith [min_le_left G.ν₀ (1 - G.ν₀)])
    have hβ₀ : 0 < β₀ := div_pos (by positivity) (mul_pos h0 (by linarith))
    have hμ' : 0 < μ' := by simp only [μ']; linarith
    rcases hQ2' h0 h1 with h | h
    · exact min_le_of_left_le (sqrt_div_le (by positivity) hQ (by linarith))
    · exact min_le_of_right_le (by rw [div_le_iff₀ (by positivity)]; linarith)
  · have hl : 0 < Real.log (1 / G.ζ) := Real.log_pos (by rw [lt_div_iff₀ hz0]; linarith)
    have hμ' : 0 < μ' := by simp only [μ']; linarith
    rcases hQ3 hz0 hz1 with h | h
    · exact min_le_of_left_le (sqrt_div_le (by positivity) hQ (by linarith))
    · exact min_le_of_right_le (by rw [div_le_iff₀ (by positivity)]; linarith)
  · rcases hQ4 hz hΛ with h | h
    · exact min_le_of_left_le (by rw [div_le_iff₀ (by positivity)]; linarith)
    · refine min_le_of_right_le (cbrt_le (by positivity) hQ ?_)
      rw [div_le_iff₀ (by positivity)]; linarith
  · have hR : 0 < R := mul_pos (by linarith) (by linarith)
    rcases hQ4 hz hΛ with h | h
    · rw [hμ0] at h; simp at h; linarith
    · rw [hμ0] at h; simp at h; nlinarith

/-! ### Risk (Lemma 8.0, Corollary 8.1) -/

section Risk

variable [NeZero kout]

/-- `minⱼ ‖ĝⱼ − gᵢ‖`. -/
noncomputable def dist (i : ι) (v : ι → Fine) (e : Fin Q → Bool) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out e j).1 - G.g (v i)‖)

/-- The risk `R = (1/n)·Σᵢ minⱼ ‖ĝⱼ − gᵢ‖`. -/
noncomputable def risk (v : ι → Fine) (e : Fin Q → Bool) : ℝ :=
  (∑ i, G.dist out i v e) / Fintype.card ι

/-- `E[R]`. -/
noncomputable def ER : ℝ := ∑ v, ∑ e, G.wt probe v e * G.risk out v e

lemma dist_nonneg (i : ι) (v : ι → Fine) (e : Fin Q → Bool) : 0 ≤ G.dist out i v e :=
  Finset.le_inf' _ _ fun j _ => norm_nonneg _

lemma ER_nonneg : 0 ≤ G.ER probe out :=
  Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun e _ => mul_nonneg (G.wt_nonneg probe v e)
    (div_nonneg (Finset.sum_nonneg fun i _ => G.dist_nonneg out i v e) (Nat.cast_nonneg _))

open Classical in
/-- **Lemma 8.0 (risk identity).** `E[R] ≥ ε(1 − E[N_ε]/n)`. -/
theorem lemma80 (ε : ℝ) (hε : 0 ≤ ε) :
    ε * (1 - G.EN probe out ε / Fintype.card ι) ≤ G.ER probe out := by
  have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  -- pathwise: `R ≥ ε(1 − N_ε/n)`
  have hpath : ∀ v e, ε * (1 - G.Ncount out ε v e / Fintype.card ι) ≤ G.risk out v e := by
    intro v e
    have hd : ∀ i, ε * (1 - if G.recovered out ε i v e then (1 : ℝ) else 0) ≤ G.dist out i v e := by
      intro i
      split_ifs with hr
      · simp only [sub_self, mul_zero]; exact G.dist_nonneg out i v e
      · simp only [sub_zero, mul_one]
        refine Finset.le_inf' _ _ fun j _ => ?_
        unfold recovered at hr; push Not at hr
        exact (hr j).le
    have hN : G.Ncount out ε v e = ∑ i, if G.recovered out ε i v e then (1 : ℝ) else 0 := by
      unfold Ncount
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    unfold risk
    rw [le_div_iff₀ hn0]
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hd i
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum] at hs
    rw [hN]
    have e : ε * (1 - (∑ i, if G.recovered out ε i v e then (1 : ℝ) else 0) /
        Fintype.card ι) * Fintype.card ι =
        Fintype.card ι * ε - ε * ∑ i, if G.recovered out ε i v e then (1 : ℝ) else 0 := by
      field_simp
    linarith
  have h1 := G.wt_sum probe (Q := Q)
  have hsum : ∑ v, ∑ e, G.wt probe v e * (ε * (1 - G.Ncount out ε v e / Fintype.card ι)) =
      ε - ε * G.EN probe out ε / Fintype.card ι := by
    have hpt : ∀ v e, G.wt probe v e * (ε * (1 - G.Ncount out ε v e / Fintype.card ι)) =
        G.wt probe v e * ε - ε / Fintype.card ι * (G.wt probe v e * G.Ncount out ε v e) :=
      fun v e => by ring
    simp only [hpt, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [h1]; unfold EN; ring
  calc ε * (1 - G.EN probe out ε / Fintype.card ι)
      = ∑ v, ∑ e, G.wt probe v e * (ε * (1 - G.Ncount out ε v e / Fintype.card ι)) := by
        rw [hsum]; ring
    _ ≤ ∑ v, ∑ e, G.wt probe v e * G.risk out v e :=
        Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun e _ =>
          mul_le_mul_of_nonneg_left (hpath v e) (G.wt_nonneg probe v e)

open Classical in
/-- **Corollary 8.1 (plateau).** For every `r > 0`:
`E[R] ≥ r(1 − Q(μ₁+2ζ) − k_out·p(r))`; hence `E[R] ≥ sup_{0<r≤2} r(1 − Q(μ₁+2ζ) − k_out·p(r))`. -/
theorem cor81_plateau (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (r pr : ℝ) (hr : 0 < r) (hp : 0 ≤ pr)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ r), G.π i l) ≤ pr) :
    r * (1 - Q * (μ₁ + 2 * G.ζ) - kout * pr) ≤ G.ER probe out := by
  have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h3 := G.thm61_3 probe out μ₁ r pr hμ hp hcov hballcov
  have h8 := G.lemma80 probe out r hr.le
  have hx : G.EN probe out r / Fintype.card ι ≤ Q * (μ₁ + 2 * G.ζ) + kout * pr := by
    rw [div_le_iff₀ hn0]; linarith
  nlinarith

open Classical in
/-- **Corollary 8.1 (decay).** If `k_out·p(ε) < 1` and `Λ(ε) ≥ 3B_best(Q)/n + 2`, then
`E[N_ε] < n/2`, hence `E[R] > ε/2`. -/
theorem cor81_decay (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (ε pε : ℝ) (hε : 0 < ε) (hp : 0 ≤ pε) (hkp : (kout : ℝ) * pε < 1)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ pε)
    (hΛ : 3 * Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q / Fintype.card ι + 2 ≤
      Real.log (1 / ((kout : ℝ) * pε))) :
    G.EN probe out ε < Fintype.card ι / 2 ∧ ε / 2 < G.ER probe out := by
  have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hB0 := (G.jointInfo_nonneg probe).trans (G.info_le_Bbest hν βstar hβ μ₁ hμ hcov probe Q)
  have h4 := G.thm61_4 probe out hν βstar hβ μ₁ hμ hcov ε pε hp hkp hballcov
  have hx := Info.cor81_v7_count _ _ _ _ hn0 hB0 hΛ h4
  refine ⟨hx, ?_⟩
  have h8 := G.lemma80 probe out ε hε.le
  have : G.EN probe out ε / Fintype.card ι < 1 / 2 := by
    rw [div_lt_iff₀ hn0]; linarith
  nlinarith

open Classical in
/-- **Corollary 8.1 (decay, sup form).** `E[R] ≥ ½·sup{ε > 0 : k_out·p(ε) < 1,
Λ(ε) ≥ 3B_best(Q)/n + 2}` (`sup ∅ := 0`, no attainment assumed). -/
theorem cor81_decay_sup (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (p : ℝ → ℝ) (hp : ∀ ε, 0 ≤ p ε)
    (hballcov : ∀ ε i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ p ε) :
    1 / 2 * sSup {ε : ℝ | 0 < ε ∧ (kout : ℝ) * p ε < 1 ∧
      3 * Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q / Fintype.card ι + 2 ≤
        Real.log (1 / ((kout : ℝ) * p ε))} ≤ G.ER probe out := by
  set T := {ε : ℝ | 0 < ε ∧ (kout : ℝ) * p ε < 1 ∧
      3 * Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q / Fintype.card ι + 2 ≤
        Real.log (1 / ((kout : ℝ) * p ε))} with hT
  have hER := G.ER_nonneg probe out
  by_cases hne : T.Nonempty
  · by_cases hbdd : BddAbove T
    · have : sSup T ≤ 2 * G.ER probe out := csSup_le hne fun ε ⟨hε, hkp, hΛ⟩ =>
        by linarith [(G.cor81_decay probe out hν βstar hβ μ₁ hμ hcov ε (p ε) hε (hp ε) hkp
          (hballcov ε) hΛ).2]
      linarith
    · rw [Real.sSup_of_not_bddAbove hbdd]; linarith
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, Real.sSup_empty]; linarith

open Classical in
/-- **Corollary 8.1, prior-free sufficient condition.** Since `B_best(Q) ≤ Q·β*`,
`Λ(ε) ≥ 3Qβ*/n + 2` (with `k_out·p(ε) < 1`) already gives `E[R] > ε/2`. -/
theorem cor81_prior_free (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (ε pε : ℝ) (hε : 0 < ε) (hp : 0 ≤ pε) (hkp : (kout : ℝ) * pε < 1)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ pε)
    (hΛ : 3 * (Q * βstar) / Fintype.card ι + 2 ≤ Real.log (1 / ((kout : ℝ) * pε))) :
    ε / 2 < G.ER probe out := by
  have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hB : Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q ≤ Q * βstar := min_le_left _ _
  refine (G.cor81_decay probe out hν βstar hβ μ₁ hμ hcov ε pε hε hp hkp hballcov ?_).2
  have : 3 * Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q / Fintype.card ι ≤
      3 * (Q * βstar) / Fintype.card ι := by gcongr
  linarith

end Risk

end Gallery

end OracleBounds.GeneralPrior
