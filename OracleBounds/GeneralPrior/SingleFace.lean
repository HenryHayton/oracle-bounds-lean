import OracleBounds.GeneralPrior.Exchange
import OracleBounds.GeneralPrior.Photo

/-!
# Single-face information bound (one target, e.g. a partial photograph)

The m-of-n information branch (Cor 6.2 / draft Cor 2.7.3) prices recovering many faces. A targeted
attacker cares about **one** face `i`, and may know it much better than the others (a partial
photograph of one person; the rest of the list blind). Small-ball Fano on face `i` alone, with
superadditivity and the budget:

  `P_i·Λ_i(ε) − h(P_i) ≤ I(gᵢ; transcript) ≤ I(G; transcript) ≤ B`,

`P_i = P[face i recovered at ε]`, `Λ_i(ε) = log(1/(k·p_i(ε)))` with `p_i` the ball mass of face `i`'s
own prior. Hence (`single_face_queries`) recovering face `i` with probability `≥ ½` needs
`Q·β* ≥ Λ_i(ε)/2 − log 2`; for a photograph at residual radius `r₀` (`photo_single_target`):

  `Q ≥ ((d_s−1)·log(r₀/ε) − log k − 2·log 2) / (2β*)`.

This is the right bound for threat case 2 with an imperfect template, where only the target's
prior is concentrated.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6 OracleBounds.V6.Info

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι] [Nonempty Fine]

open Classical in
/-- `P[face i recovered]` in the per-face joint form used by small-ball Fano. -/
lemma Prec_eq_P (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε : ℝ) (i : ι) :
    G.Prec probe out ε i = ∑ le : Fine × (Fin Q → Bool),
      (if le.1 ∈ Finset.univ.filter (fun a => ∃ j, ‖(out le.2 j).1 - G.g a‖ ≤ ε) then
        ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = le.1),
          (∏ j, G.π j (v j)) * pathProb (G.resp v) probe Q [] le.2 else 0) := by
  unfold Prec
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

open Classical in
/-- **Single-face small-ball Fano.** `P_i·log(1/(k·p_i)) − h(P_i) ≤ I(G; transcript)`, where
`p_i` bounds the ball masses of face `i`'s prior only. -/
theorem single_face_info (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε p : ℝ) (hp : 0 ≤ p) (hkp : (kout : ℝ) * p < 1)
    (i : ι) (hball : ∀ y : Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ p) :
    G.Prec probe out ε i * Real.log (1 / ((kout : ℝ) * p)) - Real.binEntropy (G.Prec probe out ε i)
      ≤ G.jointInfo probe Q := by
  set qf : ι → Fine × (Fin Q → Bool) → ℝ := fun j le =>
    ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v j = le.1),
      (∏ k, G.π k (v k)) * pathProb (G.resp v) probe Q [] le.2 with hqf
  have hPv0 : ∀ v e, 0 ≤ pathProb (G.resp v) probe Q [] e :=
    fun v => pathProb_nonneg probe (G.resp_mem v) Q []
  have hPv1 : ∀ v, ∑ e, pathProb (G.resp v) probe Q [] e = 1 :=
    fun v => pathProb_sum probe (G.resp_mem v) Q []
  have hq0 : ∀ j le, 0 ≤ qf j le := fun j le => Finset.sum_nonneg fun v _ =>
    mul_nonneg (Finset.prod_nonneg fun k _ => G.hπ0 k (v k)) (hPv0 v _)
  have hm1 : ∀ j l, marg₁ (qf j) l = G.π j l :=
    fun j l => faceJoint_marg₁ G.π G.hπ1 (fun v e => pathProb (G.resp v) probe Q [] e) hPv1 j l
  have hqsum : ∀ j, ∑ le, qf j le = 1 := by
    intro j
    rw [Fintype.sum_prod_type]
    show ∑ l, marg₁ (qf j) l = 1
    rw [Finset.sum_congr rfl fun l _ => hm1 j l]
    exact G.hπ1 j
  have hb : ∀ c : Sph E, (∑ a ∈ Finset.univ.filter (fun a => ‖c.1 - G.g a‖ ≤ ε),
      marg₁ (qf i) a) ≤ p := by
    intro c
    rw [Finset.sum_congr rfl fun a _ => hm1 i a]
    exact hball c
  have hF := small_ball_fano (qf i) (hq0 i) (hqsum i) (fun a (c : Sph E) => ‖c.1 - G.g a‖ ≤ ε)
    kout out p hp hkp hb
  simp only at hF
  rw [← G.Prec_eq_P probe out ε i] at hF
  have hsup := mutualInfo_superadditive_prior G.π G.hπ0 G.hπ1
    (fun v e => pathProb (G.resp v) probe Q [] e) hPv0 hPv1
  have hle : mutualInfo (qf i) ≤ ∑ j, mutualInfo (qf j) :=
    Finset.single_le_sum (f := fun j => mutualInfo (qf j))
      (fun j _ => mutualInfo_nonneg _ (hq0 j) (hqsum j)) (Finset.mem_univ i)
  have : mutualInfo (qf i) ≤ G.jointInfo probe Q := by
    unfold jointInfo prior; exact hle.trans hsup
  linarith

open Classical in
/-- **Recovering one specified face with probability `≥ ½`** needs `Q·β* ≥ Λ_i(ε)/2 − log 2`. -/
theorem single_face_queries (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (βstar : ℝ)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar)
    (ε p : ℝ) (hp : 0 ≤ p) (hkp : (kout : ℝ) * p < 1)
    (i : ι) (hball : ∀ y : Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ p)
    (hPi : 1 / 2 ≤ G.Prec probe out ε i) :
    Real.log (1 / ((kout : ℝ) * p)) / 2 - Real.log 2 ≤ Q * βstar := by
  have hF := G.single_face_info probe out ε p hp hkp i hball
  have hB := info_le_global G.prior G.prior_nonneg G.prior_sum G.resp (fun v x => G.resp_mem v x)
    probe βstar hβ Q
  have hJ : G.jointInfo probe Q ≤ βstar * Q := by unfold jointInfo; exact hB
  have hΛ := Lambda_nonneg (kout := kout) hp hkp
  have hh : Real.binEntropy (G.Prec probe out ε i) ≤ Real.log 2 := Real.binEntropy_le_log_two
  have : Real.log (1 / ((kout : ℝ) * p)) / 2 ≤
      G.Prec probe out ε i * Real.log (1 / ((kout : ℝ) * p)) := by nlinarith
  linarith

open Classical in
/-- **Refining one partial photograph (threat case 2, imperfect template).** If only the target
face `i` is `(r₀, d_s)`-spread, recovering it at `ε` with probability `≥ ½` needs
`Q ≥ ((d_s−1)·log(r₀/ε) − log k − 2·log 2)/(2β*)`. -/
theorem photo_single_target (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (βstar : ℝ) (hβpos : 0 < βstar)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (hk : 1 ≤ kout)
    (r₀ ε : ℝ) (hr₀ : 0 < r₀) (hε : 0 < ε) (ds : ℕ) (i : ι)
    (hspread : ∀ y : Sph E, (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε),
      G.π i l) ≤ (ε / r₀) ^ (ds - 1))
    (hkp : (kout : ℝ) * (ε / r₀) ^ (ds - 1) < 1)
    (hPi : 1 / 2 ≤ G.Prec probe out ε i) :
    (((ds - 1 : ℕ) : ℝ) * Real.log (r₀ / ε) - Real.log kout - 2 * Real.log 2) / (2 * βstar) ≤ Q := by
  have h := G.single_face_queries probe out βstar hβ ε _ (by positivity) hkp i hspread hPi
  have hΛ : Real.log (1 / ((kout : ℝ) * (ε / r₀) ^ (ds - 1))) =
      ((ds - 1 : ℕ) : ℝ) * Real.log (r₀ / ε) - Real.log kout := by
    have hk0 : (0 : ℝ) < kout := by exact_mod_cast hk
    rw [one_div, Real.log_inv, Real.log_mul hk0.ne' (by positivity), Real.log_pow,
      Real.log_div hε.ne' hr₀.ne', Real.log_div hr₀.ne' hε.ne']
    ring
  rw [hΛ] at h
  rw [div_le_iff₀ (by positivity)]
  linarith

end Gallery

end OracleBounds.GeneralPrior
