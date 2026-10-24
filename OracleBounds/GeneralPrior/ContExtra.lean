import OracleBounds.GeneralPrior.Continuous

/-!
# Continuous priors: recovery counts and the staircase branch

Complements `Continuous.lean` (which has the information branch `Q₁` and the nominated entry):

* `cont_EN` — Thm 6.1(3) for Borel product priors: `E[N_ε] ≤ n(Q(μ₁+2ζ) + k·p)` with reach masses
  at `thr − η`, ball masses at `ε + η`;
* `cont_staircase` — Cor 6.2(i): if `P[N_ε ≥ m] ≥ ½` then `m/2 ≤ n(Q(μ₁+2ζ) + k·p)`;
* `cont_blind_EN`, `cont_blind_staircase` — the density-prior forms (draft Cor 3.2.1 first display
  and Cor 3.2.2(i)), `η → 0` taken:
  `E[N_ε] ≤ n(Q(D·r_thr^{d−1} + 2ζ) + k·D·ε^{d−1})` and
  `m/2 ≤ n(Q(D·r_thr^{d−1} + 2ζ) + k·D·ε^{d−1})`.

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

open Classical in
/-- `E[N_ε | gallery v]`. -/
noncomputable def FN [Nonempty ι] (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε : ℝ) (v : ι → Sph E) : ℝ :=
  ∑ e, pathProb (O.respC v) probe Q [] e * Nc out ε v e

open Classical in
lemma FN_eq_sum [Nonempty ι] (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε : ℝ) (v : ι → Sph E) :
    O.FN probe out ε v = ∑ i, O.Frec probe out ε i v := by
  unfold FN Frec Nc
  simp only [Finset.natCast_card_filter, Finset.mul_sum]
  exact Finset.sum_comm

lemma integrable_of_bdd {f : (ι → Sph E) → ℝ} (ν : ι → Measure (Sph E))
    [∀ i, IsProbabilityMeasure (ν i)] (hf : Measurable f) (C : ℝ) (hC : ∀ v, |f v| ≤ C) :
    Integrable f (Measure.pi ν) :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun v => by simpa [Real.norm_eq_abs] using hC v)

open Classical in
/-- **Thm 6.1(3) for Borel product priors.** -/
theorem cont_EN [Nonempty ι] (ν : ι → Measure (Sph E)) [∀ i, IsProbabilityMeasure (ν i)]
    (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)
    (ε η μ₁ p : ℝ) (hη : 0 < η) (hμ : 0 ≤ μ₁) (hp : 0 ≤ p)
    (hcov : ∀ i (x : Sph E), (ν i {g : Sph E | O.thr - η ≤ inner ℝ x.1 g.1}).toReal ≤ μ₁)
    (hball : ∀ i (y : Sph E), (ν i (Metric.closedBall y (ε + η))).toReal ≤ p) :
    ∫ v, O.FN probe out ε v ∂(Measure.pi ν) ≤
      Fintype.card ι * (Q * (μ₁ + 2 * O.ζ) + kout * p) := by
  have hint : ∀ i, Integrable (O.Frec probe out ε i) (Measure.pi ν) := fun i =>
    integrable_of_bdd ν (O.measurable_Frec probe out ε i) 1
      (fun v => O.abs_avg_le probe Q v _ fun e => by split_ifs <;> norm_num)
  rw [show (fun v => O.FN probe out ε v) = fun v => ∑ i, O.Frec probe out ε i v from
    funext (O.FN_eq_sum probe out ε), integral_finsetSum _ fun i _ => hint i]
  calc ∑ i, ∫ v, O.Frec probe out ε i v ∂(Measure.pi ν)
      ≤ ∑ _i : ι, (Q * (μ₁ + 2 * O.ζ) + kout * p) := Finset.sum_le_sum fun i _ =>
        O.cont_nominated ν probe out ε η μ₁ p hη hμ hp hcov hball i
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

open Classical in
/-- **Cor 6.2(i) (staircase) for Borel product priors.** If `P[N_ε ≥ m] ≥ ½` (`m ≥ 0`), then
`m/2 ≤ n(Q(μ₁+2ζ) + k·p)`. -/
theorem cont_staircase [Nonempty ι] (ν : ι → Measure (Sph E)) [∀ i, IsProbabilityMeasure (ν i)]
    (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)
    (ε η μ₁ p : ℝ) (hη : 0 < η) (hμ : 0 ≤ μ₁) (hp : 0 ≤ p)
    (hcov : ∀ i (x : Sph E), (ν i {g : Sph E | O.thr - η ≤ inner ℝ x.1 g.1}).toReal ≤ μ₁)
    (hball : ∀ i (y : Sph E), (ν i (Metric.closedBall y (ε + η))).toReal ≤ p)
    (m : ℝ) (hm : 0 ≤ m) (hPN : 1 / 2 ≤ ∫ v, O.FPN probe out ε m v ∂(Measure.pi ν)) :
    m / 2 ≤ Fintype.card ι * (Q * (μ₁ + 2 * O.ζ) + kout * p) := by
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hNle : ∀ (v : ι → Sph E) e, Nc out ε v e ≤ Fintype.card ι := fun v e => by
    unfold Nc; exact_mod_cast Finset.card_filter_le _ _
  have hN0 : ∀ (v : ι → Sph E) e, 0 ≤ Nc out ε v e := fun v e => by unfold Nc; positivity
  have hmarkov : ∀ v : ι → Sph E, m * O.FPN probe out ε m v ≤ O.FN probe out ε v := fun v => by
    unfold FPN FN
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    have h0 := pathProb_nonneg probe (O.pathProb_resp_mem v) Q [] e
    split_ifs with h
    · nlinarith
    · nlinarith [hN0 v e]
  have hmeasN : Measurable (O.FN probe out ε (ι := ι)) := by
    rw [show O.FN probe out ε (ι := ι) = fun v => ∑ i, O.Frec probe out ε i v from
      funext (O.FN_eq_sum probe out ε)]
    exact Finset.measurable_sum _ fun i _ => O.measurable_Frec probe out ε i
  have hintN : Integrable (O.FN probe out ε) (Measure.pi ν) :=
    integrable_of_bdd ν hmeasN (Fintype.card ι) (fun v => by
      rw [abs_le]
      have h0 : ∀ e, 0 ≤ pathProb (O.respC v) probe Q [] e :=
        pathProb_nonneg probe (O.pathProb_resp_mem v) Q []
      have hs := pathProb_sum probe (O.pathProb_resp_mem v) Q []
      unfold FN
      constructor
      · linarith [Finset.sum_nonneg fun e (_ : e ∈ Finset.univ) => mul_nonneg (h0 e) (hN0 v e)]
      · calc ∑ e, pathProb (O.respC v) probe Q [] e * Nc out ε v e
            ≤ ∑ e, pathProb (O.respC v) probe Q [] e * Fintype.card ι :=
              Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hNle v e) (h0 e)
          _ = Fintype.card ι := by rw [← Finset.sum_mul, hs, one_mul])
  have hintP : Integrable (fun v => m * O.FPN probe out ε m v) (Measure.pi ν) :=
    (integrable_of_bdd ν (O.measurable_FPN probe out ε m) 1
      (fun v => O.abs_avg_le probe Q v _ fun e => by split_ifs <;> norm_num)).const_mul m
  have h1 : m * ∫ v, O.FPN probe out ε m v ∂(Measure.pi ν) ≤ ∫ v, O.FN probe out ε v ∂(Measure.pi ν) := by
    rw [← integral_const_mul]
    exact integral_mono hintP hintN hmarkov
  have h2 := O.cont_EN ν probe out ε η μ₁ p hη hμ hp hcov hball
  nlinarith

variable (Ks : ι → Submodule ℝ E) [∀ i, (Ks i).HasOrthogonalProjection] (deff : ℕ) (D : ℝ)

open Classical in
/-- **Draft Cor 3.2.1, first display, continuous density prior** (`η → 0`):
`E[N_ε] ≤ n(Q(D·r_thr^{d−1} + 2ζ) + k·D·ε^{d−1})`. -/
theorem cont_blind_EN [Nonempty ι] (ν : ι → Measure (Sph E)) [∀ i, IsProbabilityMeasure (ν i)]
    (H : ContDensityHyp Ks deff D ν) (hthr : 0 < O.thr) (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε : ℝ) (hε : 0 < ε) :
    ∫ v, O.FN probe out ε v ∂(Measure.pi ν) ≤ Fintype.card ι *
      (Q * (D * Face.chordRad O.thr ^ (deff - 1) + 2 * O.ζ) + kout * (D * ε ^ (deff - 1))) := by
  set f : ℝ → ℝ := fun η => Fintype.card ι * (Q * (D * Face.chordRad (O.thr - η) ^ (deff - 1) +
      2 * O.ζ) + kout * (D * (ε + η) ^ (deff - 1))) with hf
  have h0 : f 0 = Fintype.card ι * (Q * (D * Face.chordRad O.thr ^ (deff - 1) + 2 * O.ζ) +
      kout * (D * ε ^ (deff - 1))) := by simp [hf]
  rw [← h0]
  refine ge_of_small_eta hthr ?_ fun η hη hηt => ?_
  · refine Continuous.continuousWithinAt ?_
    simp only [hf, Face.chordRad]
    fun_prop
  · exact O.cont_EN ν probe out ε η _ _ hη
      (mul_nonneg (by linarith [H.hD]) (pow_nonneg (Real.sqrt_nonneg _) _))
      (mul_nonneg (by linarith [H.hD]) (by positivity))
      (fun j x => cont_reach_density H j x _ (by linarith))
      (fun j y => cont_ball_density H j y _ (by linarith))

open Classical in
/-- **Draft Cor 3.2.2(i), continuous density prior.** If `P[N_ε ≥ m] ≥ ½`:
`m/2 ≤ n(Q(D·r_thr^{d−1} + 2ζ) + k·D·ε^{d−1})`; in particular, when `n·k·D·ε^{d−1} ≤ m/8`,
`Q ≥ 3m/(8n(D·r_thr^{d−1} + 2ζ))`. -/
theorem cont_blind_staircase [Nonempty ι] (ν : ι → Measure (Sph E))
    [∀ i, IsProbabilityMeasure (ν i)] (H : ContDensityHyp Ks deff D ν) (hthr : 0 < O.thr)
    (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)
    (ε : ℝ) (hε : 0 < ε) (m : ℝ) (hm : 0 ≤ m)
    (hPN : 1 / 2 ≤ ∫ v, O.FPN probe out ε m v ∂(Measure.pi ν)) :
    m / 2 ≤ Fintype.card ι *
      (Q * (D * Face.chordRad O.thr ^ (deff - 1) + 2 * O.ζ) + kout * (D * ε ^ (deff - 1))) := by
  set f : ℝ → ℝ := fun η => Fintype.card ι * (Q * (D * Face.chordRad (O.thr - η) ^ (deff - 1) +
      2 * O.ζ) + kout * (D * (ε + η) ^ (deff - 1))) with hf
  have h0 : f 0 = Fintype.card ι * (Q * (D * Face.chordRad O.thr ^ (deff - 1) + 2 * O.ζ) +
      kout * (D * ε ^ (deff - 1))) := by simp [hf]
  rw [← h0]
  refine ge_of_small_eta hthr ?_ fun η hη hηt => ?_
  · refine Continuous.continuousWithinAt ?_
    simp only [hf, Face.chordRad]
    fun_prop
  · exact O.cont_staircase ν probe out ε η _ _ hη
      (mul_nonneg (by linarith [H.hD]) (pow_nonneg (Real.sqrt_nonneg _) _))
      (mul_nonneg (by linarith [H.hD]) (by positivity))
      (fun j x => cont_reach_density H j x _ (by linarith))
      (fun j y => cont_ball_density H j y _ (by linarith)) m hm hPN

end Oracle

end OracleBounds.GeneralPrior
