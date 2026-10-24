import OracleBounds.GeneralPrior.Continuous

/-!
# The risk floor for continuous priors (v2 Cor 8.1 decay, Cor 13.2)

The risk `R = (1/n) Σᵢ minⱼ ‖ĝⱼ − gᵢ‖` is bounded *below*, so the transfer applies
`discretise_pi` to `−E[R | gallery]`: the discretised prior makes the risk no larger.

* `cont_decay` — Cor 8.1 (prior-free decay) for Borel priors: if `k·p < 1` for the `(ε+η)`-ball
  mass `p` and `Λ = log(1/(k·p)) ≥ 3Qβ*/n + 2`, then `E[R] > ε/2`;
* `cont_blind_risk_floor` — v2 Cor 13.2 (prior-free form), continuous density priors, radius `ε`
  not `2ε`: `E[R] ≥ ½·exp(−(3Qβ*/n + 2 + log(kD))/(d_eff−1))`.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6 MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Oracle

variable (O : Oracle E)

/-- The risk of outputs `out e` against the gallery `v`. -/
noncomputable def riskC {Q kout : ℕ} [NeZero kout] (out : (Fin Q → Bool) → Fin kout → Sph E)
    (v : ι → Sph E) (e : Fin Q → Bool) : ℝ :=
  (∑ i, Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out e j).1 - (v i).1‖)) /
    Fintype.card ι

/-- `E[R | gallery v]`. -/
noncomputable def Frisk [Nonempty ι] (probe : List Bool → Sph E) {Q kout : ℕ} [NeZero kout]
    (out : (Fin Q → Bool) → Fin kout → Sph E) (v : ι → Sph E) : ℝ :=
  ∑ e, pathProb (O.respC v) probe Q [] e * riskC out v e

lemma riskC_mem [Nonempty ι] {Q kout : ℕ} [NeZero kout] (out : (Fin Q → Bool) → Fin kout → Sph E)
    (v : ι → Sph E) (e : Fin Q → Bool) : 0 ≤ riskC out v e ∧ riskC out v e ≤ 2 := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hd : ∀ i, 0 ≤ Finset.univ.inf' Finset.univ_nonempty
      (fun j => ‖(out e j).1 - (v i).1‖) ∧
      Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out e j).1 - (v i).1‖) ≤ 2 := by
    intro i
    obtain ⟨j₀⟩ := (inferInstance : Nonempty (Fin kout))
    refine ⟨Finset.le_inf' _ _ fun j _ => norm_nonneg _, ?_⟩
    refine (Finset.inf'_le _ (Finset.mem_univ j₀)).trans ?_
    calc ‖(out e j₀).1 - (v i).1‖ ≤ ‖(out e j₀).1‖ + ‖(v i).1‖ := norm_sub_le _ _
      _ = 2 := by rw [(out e j₀).2, (v i).2]; norm_num
  unfold riskC
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => (hd i).1) hn.le
  · rw [div_le_iff₀ hn]
    calc (∑ i, Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out e j).1 - (v i).1‖))
        ≤ ∑ _i : ι, (2 : ℝ) := Finset.sum_le_sum fun i _ => (hd i).2
      _ = 2 * Fintype.card ι := by simp; ring

lemma measurable_Frisk [Nonempty ι] (probe : List Bool → Sph E) {Q kout : ℕ} [NeZero kout]
    (out : (Fin Q → Bool) → Fin kout → Sph E) : Measurable (O.Frisk probe out (ι := ι)) := by
  unfold Frisk riskC
  refine Finset.measurable_sum _ fun e _ => (O.measurable_pathProb probe Q [] e).mul ?_
  refine Measurable.div_const (Finset.measurable_sum _ fun i _ => ?_) _
  exact (Continuous.finset_inf'_apply Finset.univ_nonempty fun j _ =>
    (continuous_const.sub (continuous_subtype_val.comp (continuous_apply i))).norm).measurable

lemma abs_Frisk_le [Nonempty ι] (probe : List Bool → Sph E) {Q kout : ℕ} [NeZero kout]
    (out : (Fin Q → Bool) → Fin kout → Sph E) (v : ι → Sph E) : |O.Frisk probe out v| ≤ 2 := by
  have h0 : ∀ e, 0 ≤ pathProb (O.respC v) probe Q [] e :=
    pathProb_nonneg probe (O.pathProb_resp_mem v) Q []
  have hs := pathProb_sum probe (O.pathProb_resp_mem v) Q []
  unfold Frisk
  rw [abs_le]; constructor
  · linarith [Finset.sum_nonneg fun e (_ : e ∈ Finset.univ) =>
      mul_nonneg (h0 e) (riskC_mem out v e).1]
  · calc ∑ e, pathProb (O.respC v) probe Q [] e * riskC out v e
        ≤ ∑ e, pathProb (O.respC v) probe Q [] e * 2 :=
          Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (riskC_mem out v e).2 (h0 e)
      _ = 2 := by rw [← Finset.sum_mul, hs, one_mul]

open Classical in
/-- **Cor 8.1 (prior-free decay) for Borel product priors.** -/
theorem cont_decay [Nonempty ι] (hν : 0 ≤ O.ν₀ ∧ O.ν₀ ≤ 1) (βstar : ℝ)
    (hβ : ∀ s, bkl (O.κ s) (1 / 2) ≤ βstar)
    (ν : ι → Measure (Sph E)) [∀ i, IsProbabilityMeasure (ν i)]
    (probe : List Bool → Sph E) {Q kout : ℕ} [NeZero kout] (out : (Fin Q → Bool) → Fin kout → Sph E)
    (ε η p : ℝ) (hε : 0 < ε) (hη : 0 < η) (hp : 0 ≤ p) (hkp : (kout : ℝ) * p < 1)
    (hball : ∀ i (y : Sph E), (ν i (Metric.closedBall y (ε + η))).toReal ≤ p)
    (hΛ : 3 * (Q * βstar) / Fintype.card ι + 2 ≤ Real.log (1 / ((kout : ℝ) * p))) :
    ε / 2 < ∫ v, O.Frisk probe out v ∂(Measure.pi ν) := by
  obtain ⟨K, w, r, hw0, hw1, hmass, hint⟩ := discretise_pi ν (fun v => -O.Frisk probe out v)
    (O.measurable_Frisk probe out).neg 2 (fun v => by rw [abs_neg]; exact O.abs_Frisk_le probe out v)
    η hη
  haveI := disc_nonempty w hw1
  set G := O.disc w r hw0 hw1
  have hcovG : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ 1 := fun i x =>
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun l _ _ => G.hπ0 i l).trans (G.hπ1 i).le
  have hdec := G.cor81_prior_free probe out hν βstar (fun v x => hβ _) 1 zero_le_one hcovG ε p hε hp
    hkp (fun i y => (O.disc_ball w r hw0 hw1 ν η hη.le hmass ε i y).trans (hball i y)) hΛ
  have hER : G.ER probe out = ∑ c : ι → Fin K, (∏ i, w i (c i)) *
      O.Frisk probe out (fun i => r i (c i)) := by
    rw [← O.disc_sum w r hw0 hw1]
    unfold Gallery.ER
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold Frisk
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    unfold Gallery.wt
    rw [mul_assoc]
    rfl
  have hint' : ∑ c : ι → Fin K, (∏ i, w i (c i)) * O.Frisk probe out (fun i => r i (c i)) ≤
      ∫ v, O.Frisk probe out v ∂(Measure.pi ν) := by
    have := hint
    rw [integral_neg] at this
    simp only [mul_neg, Finset.sum_neg_distrib] at this
    linarith
  linarith

variable (Ks : ι → Submodule ℝ E) [∀ i, (Ks i).HasOrthogonalProjection] (deff : ℕ) (D : ℝ)

open Classical in
/-- **v2 Cor 13.2 (prior-free form), continuous density priors, radius `ε`.**
`E[R] ≥ ½·exp(−(3Qβ*/n + 2 + log(kD))/(d_eff−1))`. -/
theorem cont_blind_risk_floor [Nonempty ι] (hν : 0 ≤ O.ν₀ ∧ O.ν₀ ≤ 1) (βstar : ℝ)
    (hβ : ∀ s, bkl (O.κ s) (1 / 2) ≤ βstar)
    (ν : ι → Measure (Sph E)) [∀ i, IsProbabilityMeasure (ν i)] (H : ContDensityHyp Ks deff D ν)
    (probe : List Bool → Sph E) {Q kout : ℕ} [NeZero kout]
    (out : (Fin Q → Bool) → Fin kout → Sph E) (hβ0 : 0 ≤ βstar) :
    Real.exp (-((3 * (Q * βstar) / Fintype.card ι + 2 + Real.log (kout * D)) /
      ((deff - 1 : ℕ) : ℝ))) / 2 ≤ ∫ v, O.Frisk probe out v ∂(Measure.pi ν) := by
  set d1 : ℝ := ((deff - 1 : ℕ) : ℝ) with hd1
  set A := 3 * (Q * βstar) / Fintype.card ι + 2 with hA
  set es := Real.exp (-((A + Real.log (kout * D)) / d1)) with hes
  set ER := ∫ v, O.Frisk probe out v ∂(Measure.pi ν)
  have hd1pos : 1 ≤ d1 := by rw [hd1]; have := H.hdeff; exact_mod_cast (by omega : 1 ≤ deff - 1)
  have hk : (1 : ℝ) ≤ kout := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne kout)
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hA0 : 0 < A := by rw [hA]; positivity
  have hes0 : 0 < es := Real.exp_pos _
  have key : ∀ ε, 0 < ε → ε < es → ε / 2 < ER := by
    intro ε hε hεs
    set η := (es - ε) / 2 with hηdef
    have hη : 0 < η := by rw [hηdef]; linarith
    have hρ : 0 < ε + η := by linarith
    have hρs : ε + η < es := by rw [hηdef]; linarith
    have hlog : Real.log (ε + η) < Real.log es := Real.log_lt_log hρ hρs
    rw [hes, Real.log_exp] at hlog
    have hmul : d1 * Real.log (ε + η) < -(A + Real.log (kout * D)) := by
      have := mul_lt_mul_of_pos_left hlog (by linarith : (0 : ℝ) < d1)
      rwa [show d1 * (-((A + Real.log (kout * D)) / d1)) = -(A + Real.log (kout * D)) by
        field_simp] at this
    have hΛ := Gallery.Lambda_density (k := (kout : ℝ)) (D := D) (by linarith)
      (by linarith [H.hD]) hρ (deff - 1)
    have hbig : A < d1 * Real.log (1 / (ε + η)) - Real.log (kout * D) := by
      rw [one_div, Real.log_inv]; linarith
    have hpos : 0 < (kout : ℝ) * (D * (ε + η) ^ (deff - 1)) := by have := H.hD; positivity
    have hkp : (kout : ℝ) * (D * (ε + η) ^ (deff - 1)) < 1 := by
      by_contra hc
      push Not at hc
      have : Real.log (1 / ((kout : ℝ) * (D * (ε + η) ^ (deff - 1)))) ≤ 0 :=
        Real.log_nonpos (by positivity) (by rw [div_le_one hpos]; exact hc)
      rw [hΛ] at this
      linarith
    exact O.cont_decay hν βstar hβ ν probe out ε η (D * (ε + η) ^ (deff - 1)) hε hη
      (mul_nonneg (by linarith [H.hD]) (by positivity)) hkp
      (fun i y => cont_ball_density H i y _ hρ.le) (by rw [hΛ]; linarith)
  by_contra hcon
  push Not at hcon
  have hER0 : 0 ≤ ER := by
    refine integral_nonneg fun v => ?_
    have h0 : ∀ e, 0 ≤ pathProb (O.respC v) probe Q [] e :=
      pathProb_nonneg probe (O.pathProb_resp_mem v) Q []
    exact Finset.sum_nonneg fun e _ => mul_nonneg (h0 e) (riskC_mem out v e).1
  set ε := (2 * ER + es) / 2 with hεdef
  have h1 := key ε (by rw [hεdef]; linarith) (by rw [hεdef]; linarith)
  rw [hεdef] at h1
  linarith

end Oracle

end OracleBounds.GeneralPrior
