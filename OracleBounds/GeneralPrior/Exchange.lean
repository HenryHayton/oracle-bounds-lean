import OracleBounds.GeneralPrior.Randomised

/-!
# Exchangeability: a nominated entry cannot be targeted (upper-bounds note, Prop 5.1)

If every face has the same prior (the blind, i.i.d. case), the attacker's view is invariant under
relabelling the faces: the response depends on the gallery only through `maxᵢ⟨x, gᵢ⟩`. Hence

* `Prec_exchangeable` — `P[face i recovered at ε]` is the same for every `i`;
* `Prec_eq_EN` — so it equals `E[N_ε]/n`;
* `nominated_info` — recovering a *nominated* entry with probability `≥ ½` forces
  `E[N_ε] ≥ n/2`, so Cor 6.2's information branch applies at `m = n`:
  `Q ≥ n/(2β*)·(Λ(ε) − log(2e))`. A nominated entry is as hard, information-wise, as the whole
  list. (Combined with Prop 7.3 — `Q ≥ (½ − k·p(ε))/(μ₁ + 2ζ)` — this is the lower bound matched
  by the attack of the upper-bounds note within ≈ `2 ln 2`.)

Scope: exchangeability needs identical priors — a *blind* attacker. With a photo in hand the prior
is not exchangeable and the nominated-entry question becomes P.4 / membership.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι] [Nonempty Fine]

lemma score_perm (σ : Equiv.Perm ι) (v : ι → Fine) (x : Sph E) :
    G.score (v ∘ σ) x = G.score v x := by
  unfold score
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun j _ =>
      Finset.le_sup' (f := fun j => inner ℝ x.1 (G.g (v j))) (Finset.mem_univ (σ j))
  · refine Finset.sup'_le _ _ fun j _ => ?_
    have := Finset.le_sup' (f := fun j => inner ℝ x.1 (G.g ((v ∘ σ) j))) (Finset.mem_univ (σ.symm j))
    simpa using this

lemma resp_perm (σ : Equiv.Perm ι) (v : ι → Fine) : G.resp (v ∘ σ) = G.resp v :=
  funext fun x => by unfold resp; rw [G.score_perm]

lemma prior_perm (hiid : ∀ i j, G.π i = G.π j) (σ : Equiv.Perm ι) (v : ι → Fine) :
    G.prior (v ∘ σ) = G.prior v := by
  unfold prior
  calc ∏ k, G.π k ((v ∘ σ) k) = ∏ k, G.π (σ k) (v (σ k)) :=
        Finset.prod_congr rfl fun k _ => by rw [hiid k (σ k)]; rfl
    _ = ∏ k, G.π k (v k) := Equiv.prod_comp σ (fun k => G.π k (v k))

open Classical in
/-- **Prop 5.1 (exchangeability).** With identical priors, `P[face i recovered]` does not depend
on `i`. -/
theorem Prec_exchangeable (hiid : ∀ i j, G.π i = G.π j) (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε : ℝ) (i j : ι) :
    G.Prec probe out ε i = G.Prec probe out ε j := by
  set σ := Equiv.swap i j
  unfold Prec
  have hbij : ∀ F : (ι → Fine) → ℝ, ∑ v, F v = ∑ w, F (w ∘ σ) := fun F =>
    (Fintype.sum_equiv (σ.arrowCongr (Equiv.refl Fine)) _ _ fun w => by
      simp [Equiv.arrowCongr, σ, Function.comp_def, Equiv.swap_inv]).symm
  rw [hbij]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun e _ => ?_
  have hwt : G.wt probe (w ∘ σ) e = G.wt probe w e := by
    unfold wt; rw [G.prior_perm hiid, G.resp_perm]
  have hrec : G.recovered out ε i (w ∘ σ) e ↔ G.recovered out ε j w e := by
    unfold recovered
    simp [σ, Equiv.swap_apply_left]
  rw [hwt]
  congr 1
  exact if_congr hrec rfl rfl

open Classical in
/-- With identical priors, `P[face i recovered] = E[N_ε]/n`. -/
theorem Prec_eq_EN (hiid : ∀ i j, G.π i = G.π j) (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε : ℝ) (i : ι) :
    G.EN probe out ε = Fintype.card ι * G.Prec probe out ε i := by
  rw [G.EN_eq_faces]
  have : ∀ j, (∑ v, ∑ e, G.wt probe v e * (if G.recovered out ε j v e then (1 : ℝ) else 0)) =
      G.Prec probe out ε i := fun j => by
    rw [G.Prec_exchangeable hiid probe out ε i j]; rfl
  rw [Finset.sum_congr rfl fun j _ => this j]
  simp

open Classical in
/-- **A nominated entry is as hard as the whole list (information branch).** With identical
priors: if a *specified* face is recovered at `ε` with probability `≥ ½`, `k·p(ε) < 1` and
`Λ(ε) ≥ log(2e)`, then `B_best(Q) ≥ (n/2)(Λ(ε) − log(2e))` and
`Q ≥ n/(2β*)·(Λ(ε) − log(2e))`. -/
theorem nominated_info (hiid : ∀ i j, G.π i = G.π j) (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ)
    (hβpos : 0 < βstar) (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)
    (ε p : ℝ) (hp : 0 ≤ p) (hkp : (kout : ℝ) * p < 1)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ p)
    (i : ι) (hPi : 1 / 2 ≤ G.Prec probe out ε i)
    (hL : Real.log (2 * Real.exp 1) ≤ Real.log (1 / ((kout : ℝ) * p))) :
    (Fintype.card ι : ℝ) / 2 * (Real.log (1 / ((kout : ℝ) * p)) - Real.log (2 * Real.exp 1)) ≤
      Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q ∧
    (Fintype.card ι : ℝ) / (2 * βstar) *
      (Real.log (1 / ((kout : ℝ) * p)) - Real.log (2 * Real.exp 1)) ≤ Q := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  set Λ := Real.log (1 / ((kout : ℝ) * p))
  set B := Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hx : n / 2 ≤ G.EN probe out ε := by
    rw [G.Prec_eq_EN hiid probe out ε i]; nlinarith
  have hxn := G.EN_le_n probe out ε
  have h4 := G.thm61_4 probe out hν βstar hβ μ₁ hμ hcov ε p hp hkp hballcov
  have cv := Info.cor62_v7 n n Λ 1 B B (G.EN probe out ε) hn1 one_pos le_rfl hx hxn
    (by rw [one_mul]; exact h4)
  have hL2 : Real.log (2 * Real.exp 1) = 1 + Real.log (2 * n / n) := by
    rw [mul_div_assoc, div_self (by linarith), mul_one, Real.log_mul (by norm_num)
      (Real.exp_pos 1).ne', Real.log_exp]; ring
  have hB : n / 2 * (Λ - Real.log (2 * Real.exp 1)) ≤ B := by
    have := cv.2 (by rw [← hL2]; exact hL)
    rw [hL2]; simpa using this
  refine ⟨hB, ?_⟩
  have hB1 : B ≤ Q * βstar := min_le_left _ _
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

open Classical in
/-- **First contact (lower-bound side of the note's Prop 3.3).** For every adaptive attacker,
`P[some face is reached within K probes] ≤ n·K·(μ₁ + 2ζ)`; hence the expected first-contact time
is `≥ 1/(2n(μ₁+2ζ))` (the note's Prop 3.3; matched by random search within `4 + 2n²q`). -/
theorem first_contact (probe : List Bool → Sph E) (K : ℕ) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁) :
    ∑ v, G.prior v * val (G.resp v) probe
      (fun h => if ∃ i, hitBy (G.reachG (v i)) probe h then (1 : ℝ) else 0) K [] ≤
      Fintype.card ι * (K * (μ₁ + 2 * G.ζ)) := by
  have hle : ∀ v, val (G.resp v) probe
      (fun h => if ∃ i, hitBy (G.reachG (v i)) probe h then (1 : ℝ) else 0) K [] ≤
      ∑ i, val (G.resp v) probe (hitInd G.reachG probe (v i)) K [] := by
    intro v
    rw [← val_sum]
    refine val_mono probe (G.resp_mem v) K [] fun h _ => ?_
    split_ifs with hh
    · obtain ⟨i, hi⟩ := hh
      exact le_trans (by simp [hitInd, hi])
        (Finset.single_le_sum (f := fun i => hitInd G.reachG probe (v i) h)
          (fun j _ => by unfold hitInd; split_ifs <;> norm_num) (Finset.mem_univ i))
    · exact Finset.sum_nonneg fun j _ => by unfold hitInd; split_ifs <;> norm_num
  calc _ ≤ ∑ v, G.prior v * ∑ i, val (G.resp v) probe (hitInd G.reachG probe (v i)) K [] :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hle v) (G.prior_nonneg v)
    _ = ∑ i, ∑ v, (∏ j, G.π j (v j)) * val (G.resp v) probe (hitInd G.reachG probe (v i)) K [] := by
        simp only [Finset.mul_sum, prior]; exact Finset.sum_comm
    _ ≤ ∑ _i : ι, (K : ℝ) * (μ₁ + 2 * G.ζ) :=
        Finset.sum_le_sum fun i _ => G.gallery_hitting i probe K μ₁ hμ (hcov i)
    _ = _ := by simp

end Gallery

end OracleBounds.GeneralPrior
