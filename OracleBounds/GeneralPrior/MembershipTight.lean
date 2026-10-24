import OracleBounds.GeneralPrior.SPRT
import OracleBounds.GeneralPrior.FixedSample

/-!
# Membership is tight (v2 Thm 18.1(ii) against the upper-bounds note's Thm 2.3)

For the symmetric-flip kernel (`κ = ρ` at or below `thr`, `1 − ρ` above; `ζ = 0`), with
`KL_ρ = (1−2ρ)·log((1−ρ)/ρ)` and `ℓ = log((1−ρ)/ρ)`:

* **every** attacker whose total error is `≤ δ` needs `E₀[S_c] ≥ log(1/(2δ))/KL_ρ`
  candidate-reaching probes (`Gallery.membership_reach_needed`);
* the **SPRT** with threshold `A = log(2/δ)` uses `E₀[S_c] ≤ (log(2/δ) + ℓ)/KL_ρ`, with type-I
  error `≤ δ/2` absent a collision and type-II error `≤ δ/2 + (log(2/δ) + ℓ)/(KL_ρ·Q)`
  (`Gallery.sprt_membership`; the last term is the truncation at budget `Q`).

The two agree in the rate `1/KL_ρ` and the leading term `log(1/δ)`: the ratio tends to `1` as
`δ → 0`. `sprt_typeI_avg` adds the collision term: averaged over `G₀ ∼ ∏πᵢ`, `δI ≤ δ/2 + n·μ₁`.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι]

open Classical in
/-- **Membership is tight.** Lower bound for every attacker, and the SPRT achieving it. -/
theorem membership_tight (V : ι → Fine) (c : Sph E) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hthr1 : G.thr < 1) (hκq : ∀ s ≤ G.thr, G.κ s = ρ) (hκl : ∀ s, G.thr < s → G.κ s = 1 - ρ)
    (hζ0 : G.ζ = 0) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (Q : ℕ) (hQ : 1 ≤ Q)
    (xf : Sph E) (hxf : inner ℝ xf.1 c.1 ≤ G.thr) :
    -- every attacker with total error ≤ δ needs this many candidate-reaching probes …
    (∀ (probe : List Bool → Sph E) (D : List Bool → ℝ), (∀ h, 0 ≤ D h ∧ D h ≤ 1) →
      val (G.resp V) probe D Q [] + val (G.respWith V c.1) probe (fun h => 1 - D h) Q [] ≤ δ →
      Real.log (1 / (2 * δ)) / ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ)) ≤
        accCount (G.resp V) probe (G.reachC c.1) Q []) ∧
    -- … and the SPRT at `A = log(2/δ)` achieves it
    (accCount (G.resp V) (sprtProbe (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ)) c xf)
        (G.reachC c.1) Q [] ≤
      (Real.log (2 / δ) + Real.log ((1 - ρ) / ρ)) / ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ)) ∧
    (G.score V c ≤ G.thr →
      val (G.resp V) (sprtProbe (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ)) c xf)
        (sprtDecide (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ))) Q [] ≤ δ / 2) ∧
    val (G.respWith V c.1) (sprtProbe (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ)) c xf)
        (fun h => 1 - sprtDecide (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ)) h) Q [] ≤
      δ / 2 + (Real.log (2 / δ) + Real.log ((1 - ρ) / ρ)) /
        ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * Q)) := by
  have hrange : ∀ s, ρ ≤ G.κ s ∧ G.κ s ≤ 1 - ρ := fun s => by
    rcases le_or_gt s G.thr with h | h
    · rw [hκq s h]; constructor <;> linarith
    · rw [hκl s h]; constructor <;> linarith
  refine ⟨fun probe D hD herr => ?_, ?_⟩
  · have := G.membership_reach_needed V c.1 c.2 ρ hρ0 hρ1 hrange (Or.inl hζ0) probe Q D hD δ herr
    simpa [hζ0] using this
  · -- the SPRT, `A = log(2/δ) > 0`; `e^{−A} = δ/2`
    have hA : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
    have hexp : Real.exp (-Real.log (2 / δ)) = δ / 2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
    obtain ⟨h1, -, h3, h4⟩ := G.sprt_membership V c ρ hρ0 hρ1 hthr1 hκq hκl xf hxf _ hA Q hQ
    rw [hexp] at h3 h4
    exact ⟨h1, h3, h4⟩

open Classical in
/-- **SPRT type-I error averaged over `G₀`**: `δI ≤ e^{−A} + n·μ₁` (collision term). -/
theorem sprt_typeI_avg (c : Sph E) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hthr1 : G.thr < 1)
    (hκq : ∀ s ≤ G.thr, G.κ s = ρ) (hκl : ∀ s, G.thr < s → G.κ s = 1 - ρ)
    (xf : Sph E) (hxf : inner ℝ xf.1 c.1 ≤ G.thr) (A : ℝ) (hA : 0 < A) (Q : ℕ) (hQ : 1 ≤ Q)
    (μ₁ : ℝ) (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁) :
    ∑ V, G.prior V * val (G.resp V) (sprtProbe (Real.log ((1 - ρ) / ρ)) A c xf)
      (sprtDecide (Real.log ((1 - ρ) / ρ)) A) Q [] ≤ Real.exp (-A) + Fintype.card ι * μ₁ := by
  have hD01 : ∀ h, 0 ≤ sprtDecide (Real.log ((1 - ρ) / ρ)) A h ∧
      sprtDecide (Real.log ((1 - ρ) / ρ)) A h ≤ 1 := fun h => by
    unfold sprtDecide; split_ifs <;> norm_num
  have hper : ∀ V, val (G.resp V) (sprtProbe (Real.log ((1 - ρ) / ρ)) A c xf)
      (sprtDecide (Real.log ((1 - ρ) / ρ)) A) Q [] ≤
      Real.exp (-A) + (if G.thr < G.score V c then (1 : ℝ) else 0) := by
    intro V
    split_ifs with h
    · linarith [(val_mem_Icc (p := G.resp V) (sprtProbe (Real.log ((1 - ρ) / ρ)) A c xf)
        (fun x => G.resp_mem V x) hD01 Q []).2, Real.exp_pos (-A)]
    · push Not at h
      have := (G.sprt_membership V c ρ hρ0 hρ1 hthr1 hκq hκl xf hxf A hA Q hQ).2.2.1 h
      linarith
  calc _ ≤ ∑ V, G.prior V * (Real.exp (-A) + (if G.thr < G.score V c then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun V _ => mul_le_mul_of_nonneg_left (hper V) (G.prior_nonneg V)
    _ = Real.exp (-A) + ∑ V, G.prior V * (if G.thr < G.score V c then (1 : ℝ) else 0) := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, G.prior_sum, one_mul]
    _ ≤ _ := by linarith [G.collision_le c μ₁ hcov]

end Gallery

end OracleBounds.GeneralPrior
