import OracleBounds.GeneralPrior.Pool

/-!
# Suspicion: the mixture prior (v2 Thm 17.2; P1 Cor P.6; draft §3.6)

Face `i` is the attacker's guess `ĝᵢ` with probability `λᵢ`, and otherwise drawn from a residual
prior `π⁰ᵢ`: `πᵢ = λᵢ·δ_{ĝᵢ} + (1−λᵢ)·π⁰ᵢ`.

* `mixture_nominated` — `P[face i recovered at ε] ≤ λᵢ + (1−λᵢ)·(Q(μ₁⁰ + 2ζ) + k·p⁰(ε))`, with
  `μ₁⁰`, `p⁰` the residual prior's parameters. (Recovery probability is linear in face `i`'s prior;
  the guessed component is bounded by `1`, the residual one by Prop 7.3.)
* `mixture_EN` — `E[N_ε] ≤ Σᵢλᵢ + n·(Q(μ₁⁰ + 2ζ) + k·p⁰(ε))`.
* `mixture_converse` — the zero-query attacker that simply outputs its guesses recovers face `i`
  with probability `≥ λᵢ`: the degradation is exactly linear and cannot be removed.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι] [Nonempty Fine]

/-- The same gallery with face `i`'s prior replaced by `p`. -/
def withPrior (i : ι) (p : Fine → ℝ) (hp0 : ∀ l, 0 ≤ p l) (hp1 : ∑ l, p l = 1) :
    Gallery E ι Fine :=
  { G with
    π := Function.update G.π i p
    hπ0 := fun j l => by
      by_cases h : j = i
      · subst h; simp [hp0]
      · simp [Function.update_of_ne h, G.hπ0 j l]
    hπ1 := fun j => by
      by_cases h : j = i
      · subst h; simp [hp1]
      · simp [Function.update_of_ne h, G.hπ1 j] }

lemma prior_split (i : ι) (v : ι → Fine) :
    G.prior v = G.π i (v i) * ∏ j ∈ Finset.univ.erase i, G.π j (v j) := by
  unfold prior; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

lemma withPrior_prior (i : ι) (p : Fine → ℝ) (hp0 : ∀ l, 0 ≤ p l) (hp1 : ∑ l, p l = 1)
    (v : ι → Fine) :
    (G.withPrior i p hp0 hp1).prior v = p (v i) * ∏ j ∈ Finset.univ.erase i, G.π j (v j) := by
  rw [(G.withPrior i p hp0 hp1).prior_split i v]
  congr 1
  · simp [withPrior]
  · refine Finset.prod_congr rfl fun j hj => ?_
    simp [withPrior, Function.update_of_ne (Finset.ne_of_mem_erase hj)]

variable (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)

open Classical in
/-- Prop 7.3 in the per-face form: only face `i`'s prior parameters are needed. -/
lemma Prec_le_face (i : ι) (μ₁ ε p : ℝ) (hμ : 0 ≤ μ₁) (hp : 0 ≤ p)
    (hcov : ∀ x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (hballcov : ∀ y : Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ p) :
    G.Prec probe out ε i ≤ Q * (μ₁ + 2 * G.ζ) + kout * p := by
  have h := G.gallery_recovery i probe kout (outL out) Q μ₁ ε p hμ hp hcov hballcov
  refine le_of_eq_of_le ?_ h
  unfold Prec
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [val_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [outL_ofFn]
  unfold wt recovered prior
  ring_nf

open Classical in
/-- **Mixture, one face.** `P[face i recovered at ε] ≤ λ + (1−λ)·(Q(μ₁⁰ + 2ζ) + k·p⁰)`. -/
theorem mixture_nominated (i : ι) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (gh : Fine)
    (π0 : Fine → ℝ) (h00 : ∀ l, 0 ≤ π0 l) (h01 : ∑ l, π0 l = 1)
    (hmix : ∀ l, G.π i l = lam * (if l = gh then 1 else 0) + (1 - lam) * π0 l)
    (μ₀ ε p₀ : ℝ) (hμ : 0 ≤ μ₀) (hp : 0 ≤ p₀)
    (hcov : ∀ x, (∑ l ∈ Finset.univ.filter (G.reachG · x), π0 l) ≤ μ₀)
    (hball : ∀ y : Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), π0 l) ≤ p₀) :
    G.Prec probe out ε i ≤ lam + (1 - lam) * (Q * (μ₀ + 2 * G.ζ) + kout * p₀) := by
  set δg : Fine → ℝ := fun l => if l = gh then 1 else 0 with hδg
  have hδ0 : ∀ l, 0 ≤ δg l := fun l => by simp only [hδg]; split_ifs <;> norm_num
  have hδ1 : ∑ l, δg l = 1 := by simp [hδg]
  set Gδ := G.withPrior i δg hδ0 hδ1
  set G0 := G.withPrior i π0 h00 h01
  set F : (ι → Fine) → ℝ := fun v => ∑ e, pathProb (G.resp v) probe Q [] e *
    (if G.recovered out ε i v e then (1 : ℝ) else 0) with hFdef
  have hF : ∀ v, 0 ≤ F v ∧ F v ≤ 1 := fun v => by
    have h0 : ∀ e, 0 ≤ pathProb (G.resp v) probe Q [] e :=
      pathProb_nonneg probe (G.resp_mem v) Q []
    have hs := pathProb_sum probe (G.resp_mem v) Q []
    constructor
    · exact Finset.sum_nonneg fun e _ => mul_nonneg (h0 e) (by split_ifs <;> norm_num)
    · calc F v ≤ ∑ e, pathProb (G.resp v) probe Q [] e := Finset.sum_le_sum fun e _ =>
            mul_le_of_le_one_right (h0 e) (by split_ifs <;> norm_num)
        _ = 1 := hs
  have hPrec : ∀ H : Gallery E ι Fine, H.resp = G.resp → H.g = G.g →
      H.Prec probe out ε i = ∑ v, H.prior v * F v := by
    intro H hr hg
    unfold Prec wt
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [recovered, hr, hg]; ring
  have hlin : ∀ v, G.prior v = lam * Gδ.prior v + (1 - lam) * G0.prior v := fun v => by
    rw [G.prior_split i v, G.withPrior_prior i δg hδ0 hδ1 v, G.withPrior_prior i π0 h00 h01 v,
      hmix]
    ring
  have hδle : ∑ v, Gδ.prior v * F v ≤ 1 :=
    calc ∑ v, Gδ.prior v * F v ≤ ∑ v, Gδ.prior v := Finset.sum_le_sum fun v _ =>
          mul_le_of_le_one_right (Gδ.prior_nonneg v) (hF v).2
      _ = 1 := Gδ.prior_sum
  have hG0 := G0.Prec_le_face probe out i μ₀ ε p₀ hμ hp
    (fun x => by simp only [G0, withPrior, Function.update_self]; exact hcov x)
    (fun y => by simp only [G0, withPrior, Function.update_self]; exact hball y)
  have hζ0 : G0.ζ = G.ζ := rfl
  rw [hζ0] at hG0
  rw [hPrec G rfl rfl]
  rw [hPrec G0 rfl rfl] at hG0
  calc ∑ v, G.prior v * F v
      = lam * ∑ v, Gδ.prior v * F v + (1 - lam) * ∑ v, G0.prior v * F v := by
        simp only [hlin, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    _ ≤ lam * 1 + (1 - lam) * (Q * (μ₀ + 2 * G.ζ) + kout * p₀) :=
        add_le_add (mul_le_mul_of_nonneg_left hδle hlam0)
          (mul_le_mul_of_nonneg_left hG0 (by linarith))
    _ = _ := by ring

open Classical in
/-- **Mixture, whole list.** `E[N_ε] ≤ Σᵢλᵢ + n·(Q(μ₁⁰ + 2ζ) + k·p⁰(ε))`. -/
theorem mixture_EN (lam : ι → ℝ) (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∀ i, lam i ≤ 1) (gh : ι → Fine)
    (π0 : ι → Fine → ℝ) (h00 : ∀ i l, 0 ≤ π0 i l) (h01 : ∀ i, ∑ l, π0 i l = 1)
    (hmix : ∀ i l, G.π i l = lam i * (if l = gh i then 1 else 0) + (1 - lam i) * π0 i l)
    (μ₀ ε p₀ : ℝ) (hμ : 0 ≤ μ₀) (hp : 0 ≤ p₀)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), π0 i l) ≤ μ₀)
    (hball : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), π0 i l) ≤ p₀) :
    G.EN probe out ε ≤ ∑ i, lam i + Fintype.card ι * (Q * (μ₀ + 2 * G.ζ) + kout * p₀) := by
  have hB0 : 0 ≤ Q * (μ₀ + 2 * G.ζ) + kout * p₀ := by
    have := G.zeta_nonneg; positivity
  rw [G.EN_eq_faces]
  calc ∑ i, ∑ v, ∑ e, G.wt probe v e * (if G.recovered out ε i v e then (1 : ℝ) else 0)
      = ∑ i, G.Prec probe out ε i := rfl
    _ ≤ ∑ i, (lam i + (1 - lam i) * (Q * (μ₀ + 2 * G.ζ) + kout * p₀)) :=
        Finset.sum_le_sum fun i _ => G.mixture_nominated probe out i (lam i) (hlam0 i) (hlam1 i)
          (gh i) (π0 i) (h00 i) (h01 i) (hmix i) μ₀ ε p₀ hμ hp (hcov i) (hball i)
    _ ≤ ∑ i, (lam i + (Q * (μ₀ + 2 * G.ζ) + kout * p₀)) :=
        Finset.sum_le_sum fun i _ => by nlinarith [hlam0 i, hlam1 i]
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

open Classical in
/-- **The converse: the linear floor cannot be removed.** An attacker making **no queries** that
outputs its guess for face `i` recovers face `i` (at any `ε ≥ 0`) with probability
`≥ πᵢ(ĝᵢ) ≥ λᵢ`. -/
theorem mixture_converse (i : ι) (lam : ℝ) (gh : Fine) (π0 : Fine → ℝ) (h00 : ∀ l, 0 ≤ π0 l)
    (hmix : ∀ l, G.π i l = lam * (if l = gh then 1 else 0) + (1 - lam) * π0 l)
    (hlam1 : lam ≤ 1) (ε : ℝ) (hε : 0 ≤ ε) (probe : List Bool → Sph E)
    (c : Sph E) (hc : c.1 = G.g gh) :
    lam ≤ G.Prec probe (Q := 0) (kout := 1) (fun _ _ => c) ε i := by
  have hge : ∀ v : ι → Fine, (if v i = gh then G.prior v else 0) ≤
      ∑ e, G.wt probe v e * (if G.recovered (Q := 0) (kout := 1) (fun _ _ => c) ε i v e then
        (1 : ℝ) else 0) := by
    intro v
    split_ifs with hv
    · have hrec : ∀ e, G.recovered (Q := 0) (kout := 1) (fun _ _ => c) ε i v e := fun e =>
        ⟨0, by rw [hc, hv, sub_self, norm_zero]; exact hε⟩
      simp only [hrec, if_true, mul_one]
      unfold wt
      rw [← Finset.mul_sum, pathProb_sum probe (G.resp_mem v) 0 [], mul_one]
    · exact Finset.sum_nonneg fun e _ => mul_nonneg (G.wt_nonneg probe v e)
        (by split_ifs <;> norm_num)
  have hmarg : ∑ v : ι → Fine, (if v i = gh then G.prior v else 0) = G.π i gh := by
    unfold prior; exact prodPrior_marg G.π G.hπ1 i gh
  have hπgh : lam ≤ G.π i gh := by rw [hmix]; simp; nlinarith [h00 gh]
  unfold Prec
  calc lam ≤ G.π i gh := hπgh
    _ = _ := hmarg.symm
    _ ≤ _ := Finset.sum_le_sum fun v _ => hge v

/-! ### Query form (technical note §3.4, Corollary 3.4.2) -/

open Classical in
/-- **Corollary 3.4.2, division-free form.** *UNSIGNED — statement pending administrator
sign-off.*

Markov (`P[N_ε ≥ m] ≥ ½ ⇒ E[N_ε] ≥ m/2`) applied to `mixture_EN`:

  `m/2 − Λ_tot − n·k_out·p⁰(ε) ≤ n·Q·(μ₁⁰ + 2ζ)`,   `Λ_tot = Σᵢ λᵢ`. -/
theorem mixture_queries (lam : ι → ℝ) (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∀ i, lam i ≤ 1)
    (gh : ι → Fine) (π0 : ι → Fine → ℝ) (h00 : ∀ i l, 0 ≤ π0 i l) (h01 : ∀ i, ∑ l, π0 i l = 1)
    (hmix : ∀ i l, G.π i l = lam i * (if l = gh i then 1 else 0) + (1 - lam i) * π0 i l)
    (μ₀ ε p₀ : ℝ) (hμ : 0 ≤ μ₀) (hp : 0 ≤ p₀)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), π0 i l) ≤ μ₀)
    (hball : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), π0 i l) ≤ p₀)
    (m : ℝ) (hm : 0 ≤ m) (hPN : 1 / 2 ≤ G.PN probe out ε m) :
    m / 2 - (∑ i, lam i) - Fintype.card ι * kout * p₀ ≤
      Fintype.card ι * Q * (μ₀ + 2 * G.ζ) := by
  have hx := G.markov probe out ε m hm hPN
  have hEN := G.mixture_EN probe out lam hlam0 hlam1 gh π0 h00 h01 hmix μ₀ ε p₀ hμ hp hcov hball
  have e : (Fintype.card ι : ℝ) * ((Q : ℝ) * (μ₀ + 2 * G.ζ) + (kout : ℝ) * p₀) =
      (Fintype.card ι : ℝ) * Q * (μ₀ + 2 * G.ζ) + (Fintype.card ι : ℝ) * kout * p₀ := by ring
  rw [e] at hEN
  linarith

open Classical in
/-- **Corollary 3.4.2 (mixture, query form).** *UNSIGNED — statement pending administrator
sign-off.* For a band-null kernel (`ζ = 0`) with `n·μ₁⁰ > 0`, if `P[N_ε ≥ m] ≥ ½` then

  `Q ≥ (m/2 − Λ_tot − n·k_out·p⁰(ε)) / (n·μ₁⁰)`. -/
theorem cor342 (hζ : G.ζ = 0) (lam : ι → ℝ) (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∀ i, lam i ≤ 1)
    (gh : ι → Fine) (π0 : ι → Fine → ℝ) (h00 : ∀ i l, 0 ≤ π0 i l) (h01 : ∀ i, ∑ l, π0 i l = 1)
    (hmix : ∀ i l, G.π i l = lam i * (if l = gh i then 1 else 0) + (1 - lam i) * π0 i l)
    (μ₀ ε p₀ : ℝ) (hμ : 0 < μ₀) (hp : 0 ≤ p₀)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), π0 i l) ≤ μ₀)
    (hball : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), π0 i l) ≤ p₀)
    (m : ℝ) (hm : 0 ≤ m) (hPN : 1 / 2 ≤ G.PN probe out ε m) :
    (m / 2 - (∑ i, lam i) - Fintype.card ι * kout * p₀) / (Fintype.card ι * μ₀) ≤ Q := by
  have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := G.mixture_queries probe out lam hlam0 hlam1 gh π0 h00 h01 hmix μ₀ ε p₀ hμ.le hp
    hcov hball m hm hPN
  rw [hζ] at h
  rw [div_le_iff₀ (by positivity)]
  nlinarith

open Classical in
/-- **Corollary 3.4.2, second sentence.** *Signed off by the administrator, 23 Sep 2026; faithful to technical note Corollary 3.4.2.*
If the residual priors satisfy the hypotheses of §3.2, Lemma 3.2.1 bounds
`μ₁⁰ ≤ (D/2)(1 − thr²)^{(d_s−1)/2}` (`SurfaceDensity.reach_rate_sharp`), and the query bound reads

  `Q ≥ (m − 2Λ_tot − 2n·k_out·p⁰(ε)) / (n·D·(1 − thr²)^{(d_s−1)/2})`,

here in division-free form. -/
theorem cor342_density (hζ : G.ζ = 0) (lam : ι → ℝ) (hlam0 : ∀ i, 0 ≤ lam i)
    (hlam1 : ∀ i, lam i ≤ 1) (gh : ι → Fine) (π0 : ι → Fine → ℝ) (h00 : ∀ i l, 0 ≤ π0 i l)
    (h01 : ∀ i, ∑ l, π0 i l = 1)
    (hmix : ∀ i l, G.π i l = lam i * (if l = gh i then 1 else 0) + (1 - lam i) * π0 i l)
    (μ₀ ε p₀ : ℝ) (hμ : 0 ≤ μ₀) (hp : 0 ≤ p₀)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), π0 i l) ≤ μ₀)
    (hball : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), π0 i l) ≤ p₀)
    (m : ℝ) (hm : 0 ≤ m) (hPN : 1 / 2 ≤ G.PN probe out ε m)
    (D : ℝ) (deff : ℕ)
    (hDμ : μ₀ ≤ D / 2 * (1 - G.thr ^ 2) ^ (((deff - 1 : ℕ) : ℝ) / 2)) :
    m - 2 * (∑ i, lam i) - 2 * (Fintype.card ι * kout * p₀) ≤
      Fintype.card ι * (D * (1 - G.thr ^ 2) ^ (((deff - 1 : ℕ) : ℝ) / 2)) * Q := by
  have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have h := G.mixture_queries probe out lam hlam0 hlam1 gh π0 h00 h01 hmix μ₀ ε p₀ hμ hp
    hcov hball m hm hPN
  rw [hζ] at h
  nlinarith [mul_le_mul_of_nonneg_left hDμ (mul_nonneg hn0.le hQ)]

end Gallery

end OracleBounds.GeneralPrior
