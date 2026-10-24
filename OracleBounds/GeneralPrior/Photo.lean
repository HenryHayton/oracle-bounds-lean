import OracleBounds.GeneralPrior.Continuous

/-!
# Photo in hand: the residual-knowledge prior (P1 Cor P.4)

The targeted attacker knows face `i` up to a residual radius `r₀` (a photo): its prior is
`(r₀, d_s)`-spread, `p(ρ) ≤ min{1, (ρ/r₀)^{d_s−1}}`.

* `photo_reach` — P.4(i): `μ₁ ≤ (r_thr/r₀)^{d_s−1}` (via P.0(a));
* `photo_m_of_n` — P.4(ii): `Q ≥ m/(2β*)·((d_s−1)·log(r₀/ε) − log k − log(2en/m))`: improving the
  photo from `r₀` to `ε` still costs `(d_s−1)·log(r₀/ε)` nats per face;
* `cont_photo_m_of_n` — the same for a continuous spread prior;
* `photo_collapse` — P.4(iii), the honest collapse: if every template the attacker considers
  possible is accepted at the photo point `c` (e.g. support in `B̄(c, r₀)` with `r₀ ≤ r_{τacc}`),
  then the **zero-query** attacker that outputs `c` is accepted by entry `i` with probability `1`.
  No query lower bound for impersonation exists there; only response noise (Thm 18.1) protects.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6 MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι] [Nonempty Fine]

open Classical in
/-- **P.4(i).** A spread profile at the reach radius bounds `μ₁`:
`μ₁ ≤ (r_thr/r₀)^{d_s−1}`. -/
theorem photo_reach (r₀ : ℝ) (ds : ℕ)
    (hspread : ∀ i (y : E), (∑ l ∈ Finset.univ.filter (fun l => ‖y - G.g l‖ ≤ Face.chordRad G.thr),
      G.π i l) ≤ (Face.chordRad G.thr / r₀) ^ (ds - 1)) (i : ι) (x : Sph E) :
    (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ (Face.chordRad G.thr / r₀) ^ (ds - 1) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun l _ _ => G.hπ0 i l) (hspread i x.1)
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
  have hsq : ‖x.1 - G.g l‖ ^ 2 = 2 * (1 - inner ℝ x.1 (G.g l)) := by
    rw [norm_sub_sq_real, x.2, G.hg l]; ring
  unfold Face.chordRad
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt (by rw [hsq]; unfold reachG at hl; linarith)

variable {Q kout : ℕ} (probe : List Bool → Sph E) (out : (Fin Q → Bool) → Fin kout → Sph E)

open Classical in
/-- **P.4(ii).** With a `(r₀, d_s)`-spread prior: if `P[N_ε ≥ m] ≥ ½`, `1 ≤ m ≤ n`,
`k·(ε/r₀)^{d_s−1} < 1`, then
`Q ≥ m/(2β*)·((d_s−1)·log(r₀/ε) − log k − log(2en/m))`. -/
theorem photo_m_of_n (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ) (hβpos : 0 < βstar)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (hk : 1 ≤ kout)
    (r₀ ε : ℝ) (hr₀ : 0 < r₀) (hε : 0 < ε) (ds : ℕ)
    (hspread : ∀ i (y : Sph E), (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε),
      G.π i l) ≤ (ε / r₀) ^ (ds - 1))
    (hkp : (kout : ℝ) * (ε / r₀) ^ (ds - 1) < 1)
    (m : ℝ) (hm : 1 ≤ m) (hmn : m ≤ Fintype.card ι) (hPN : 1 / 2 ≤ G.PN probe out ε m) :
    m / (2 * βstar) * (((ds - 1 : ℕ) : ℝ) * Real.log (r₀ / ε) - Real.log kout -
      Real.log (2 * Real.exp 1 * Fintype.card ι / m)) ≤ Q := by
  have hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ 1 := fun i x =>
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun l _ _ => G.hπ0 i l).trans (G.hπ1 i).le
  have hΛ : Real.log (1 / ((kout : ℝ) * (ε / r₀) ^ (ds - 1))) =
      ((ds - 1 : ℕ) : ℝ) * Real.log (r₀ / ε) - Real.log kout := by
    have hk0 : (0 : ℝ) < kout := by exact_mod_cast hk
    rw [one_div, Real.log_inv, Real.log_mul hk0.ne' (by positivity), Real.log_pow,
      Real.log_div hε.ne' hr₀.ne', Real.log_div hr₀.ne' hε.ne']
    ring
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  by_cases hLΛ : Real.log (2 * Real.exp 1 * Fintype.card ι / m) ≤
      Real.log (1 / ((kout : ℝ) * (ε / r₀) ^ (ds - 1)))
  · have h := (G.cor62_ii probe out hν βstar hβ 1 zero_le_one hcov ε _ (by positivity) hkp
      hspread m hm hmn hPN).2 hLΛ
    rw [hΛ] at h
    have hB : Bbest (Fintype.card ι) 1 G.ζ G.ν₀ βstar Q ≤ Q * βstar := min_le_left _ _
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  · push Not at hLΛ
    rw [hΛ] at hLΛ
    have : m / (2 * βstar) * (((ds - 1 : ℕ) : ℝ) * Real.log (r₀ / ε) - Real.log kout -
        Real.log (2 * Real.exp 1 * Fintype.card ι / m)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith

open Classical in
/-- **P.4(iii), the honest collapse.** If every template of positive prior weight for face `i` is
accepted at the photo point `c` (`⟨c, g⟩ ≥ τ_acc`; e.g. support in `B̄(c, r₀)` with
`r₀ ≤ r_{τacc}`), then the attacker making **no queries** and outputting `c` is accepted by entry `i`
with probability `1`. -/
theorem photo_collapse (i : ι) (c : Sph E)
    (hacc : ∀ l, 0 < G.π i l → G.acceptsG l c) :
    ∑ v : ι → Fine, (∏ j, G.π j (v j)) * val (G.resp v) (fun _ => c) (fun h =>
      if (∃ k < h.length, G.acceptsG (v i) c) ∨ (∃ _j : Fin 1, G.acceptsG (v i) c)
        then (1 : ℝ) else 0) 0 [] = 1 := by
  have hpt : ∀ v : ι → Fine, (∏ j, G.π j (v j)) * val (G.resp v) (fun _ => c) (fun h =>
      if (∃ k < h.length, G.acceptsG (v i) c) ∨ (∃ _j : Fin 1, G.acceptsG (v i) c)
        then (1 : ℝ) else 0) 0 [] = ∏ j, G.π j (v j) := by
    intro v
    rcases eq_or_lt_of_le (G.hπ0 i (v i)) with h0 | hpos
    · rw [Finset.prod_eq_zero (Finset.mem_univ i) h0.symm, zero_mul]
    · rw [val_zero, if_pos (Or.inr ⟨0, hacc (v i) hpos⟩), mul_one]
  rw [Finset.sum_congr rfl fun v _ => hpt v]
  exact prodPrior_sum G.π G.hπ1

end Gallery

namespace Oracle

variable (O : Oracle E) [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- **P.4(ii) for a continuous `(r₀, d_s)`-spread prior** (`η → 0` taken). -/
theorem cont_photo_m_of_n [Nonempty ι] (hν : 0 ≤ O.ν₀ ∧ O.ν₀ ≤ 1) (βstar : ℝ)
    (hβpos : 0 < βstar) (hβ : ∀ s, bkl (O.κ s) (1 / 2) ≤ βstar)
    (ν : ι → Measure (Sph E)) [∀ i, IsProbabilityMeasure (ν i)] (r₀ : ℝ) (hr₀ : 0 < r₀) (ds : ℕ)
    (hspread : ∀ i (y : Sph E) (ρ : ℝ), 0 ≤ ρ →
      (ν i (Metric.closedBall y ρ)).toReal ≤ (ρ / r₀) ^ (ds - 1))
    (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)
    (hk : 1 ≤ kout) (ε : ℝ) (hε : 0 < ε) (m : ℝ) (hm : 1 ≤ m) (hmn : m ≤ Fintype.card ι)
    (hPN : 1 / 2 ≤ ∫ v, O.FPN probe out ε m v ∂(Measure.pi ν)) :
    m / (2 * βstar) * (((ds - 1 : ℕ) : ℝ) * Real.log (r₀ / ε) - Real.log kout -
      Real.log (2 * Real.exp 1 * Fintype.card ι / m)) ≤ Q := by
  set f : ℝ → ℝ := fun η => m / (2 * βstar) * (((ds - 1 : ℕ) : ℝ) * Real.log (r₀ / (ε + η)) -
      Real.log kout - Real.log (2 * Real.exp 1 * Fintype.card ι / m)) with hf
  have h0 : f 0 = m / (2 * βstar) * (((ds - 1 : ℕ) : ℝ) * Real.log (r₀ / ε) - Real.log kout -
      Real.log (2 * Real.exp 1 * Fintype.card ι / m)) := by simp [hf]
  rw [← h0]
  refine le_of_small_eta one_pos ?_ fun η hη _ => ?_
  · refine ContinuousAt.continuousWithinAt ?_
    have hlog : ContinuousAt (fun η : ℝ => Real.log (r₀ / (ε + η))) 0 :=
      ContinuousAt.log (continuousAt_const.div (continuousAt_const.add continuousAt_id)
        (by simp; linarith)) (by simp; exact ⟨hr₀.ne', hε.ne'⟩)
    exact continuousAt_const.mul (((continuousAt_const.mul hlog).sub continuousAt_const).sub
      continuousAt_const)
  · have hρ : 0 < ε + η := by linarith
    have hmain := O.cont_m_of_n hν βstar hβpos hβ ν probe out ε η (((ε + η) / r₀) ^ (ds - 1)) hη
      (by positivity) (fun i y => hspread i y _ hρ.le) m hm hmn hPN
    have hk0 : (0 : ℝ) < kout := by exact_mod_cast hk
    have e : Real.log (1 / ((kout : ℝ) * (((ε + η) / r₀) ^ (ds - 1)))) =
        ((ds - 1 : ℕ) : ℝ) * Real.log (r₀ / (ε + η)) - Real.log kout := by
      rw [one_div, Real.log_inv, Real.log_mul hk0.ne' (by positivity), Real.log_pow,
        Real.log_div hρ.ne' hr₀.ne', Real.log_div hr₀.ne' hρ.ne']
      ring
    rw [e] at hmain
    exact hmain

end Oracle

end OracleBounds.GeneralPrior
