import OracleBounds.GeneralPrior.Randomised

/-!
# Passive observer (threat case 4): membership from probes the attacker does not choose

The membership bound `E₀[S_c] ≥ (log(1/2δ) − β₀Q)/KL_ρ` (Thm 18.1(ii)) lets the attacker place
every probe at the candidate. A *passive* venue cannot: its probes are the arrivals
`seq u 0, seq u 1, …` (random, with weights `λ u`), issued in order whatever the transcript says.
Then `E₀[S_c] = ∑_k P[arrival k reaches c]`, so with per-round reach probabilities `r k`:

  `(log(1/2δ) − β₀Q)/KL_ρ ≤ ∑_{k<Q} r k`.

Corollaries: if the target never appears and arrivals are population draws with cap mass
`≤ μ_pop` at `c` (the false-accept mass of `c`'s template), `Q·(KL_ρ·μ_pop + β₀) ≥ log(1/2δ)`
observations are needed (`passive_population`); if the target visits on a set `Vis` of rounds
and the other rounds have reach mass `≤ μ`, `KL_ρ·(|Vis| + Qμ) + β₀Q ≥ log(1/2δ)`
(`passive_visits`). This is tight: the passive SPRT on the reaching arrivals achieves it.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {X : Type*}

/-- For a transcript-independent probe sequence, the expected reach count is the plain count. -/
lemma accCount_nonadaptive (p : X → ℝ) (x : ℕ → X) (act : X → Prop) [DecidablePred act] :
    ∀ (r : ℕ) (h : List Bool), accCount p (fun h => x h.length) act r h =
      ∑ k ∈ Finset.range r, if act (x (h.length + k)) then (1 : ℝ) else 0 := by
  intro r
  induction r with
  | zero => intro h; simp [accCount]
  | succ r ih =>
    intro h
    simp only [accCount, ih, List.length_append, List.length_singleton]
    rw [Finset.sum_range_succ']
    have : ∀ k, h.length + 1 + k = h.length + (k + 1) := fun k => by ring
    simp only [this, add_zero]
    ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]
variable {U : Type*} [Fintype U]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι] [Nonempty Fine]

/-- The passive probe rule: round `k` probes arrival `seq u k`, whatever the transcript. -/
def passiveProbe (seq : U → ℕ → Sph E) (u : U) (h : List Bool) : Sph E := seq u h.length

variable (lam : U → ℝ) (hlam0 : ∀ u, 0 ≤ lam u) (hlam1 : ∑ u, lam u = 1)
include hlam0 hlam1

variable (c : E)

open Classical in
/-- Under the passive rule, `E₀[S_c]` is the sum over rounds of the arrival's reach probability. -/
lemma memReach_passive (seq : U → ℕ → Sph E) (Q : ℕ) :
    G.memReach lam c (passiveProbe seq) Q =
      ∑ k ∈ Finset.range Q, ∑ u, lam u * (if G.reachC c (seq u k) then (1 : ℝ) else 0) := by
  unfold memReach passiveProbe
  have hacc : ∀ u (V : ι → Fine), accCount (G.resp V) (fun h => seq u h.length) (G.reachC c) Q []
      = ∑ k ∈ Finset.range Q, if G.reachC c (seq u k) then (1 : ℝ) else 0 := by
    intro u V
    rw [accCount_nonadaptive]
    simp
  simp only [hacc]
  calc ∑ u, ∑ V : ι → Fine, lam u * G.prior V *
          ∑ k ∈ Finset.range Q, (if G.reachC c (seq u k) then (1 : ℝ) else 0)
      = ∑ u, lam u * (∑ k ∈ Finset.range Q, (if G.reachC c (seq u k) then (1 : ℝ) else 0)) *
          ∑ V : ι → Fine, G.prior V := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun V _ => by ring
    _ = ∑ u, ∑ k ∈ Finset.range Q, lam u * (if G.reachC c (seq u k) then (1 : ℝ) else 0) := by
        rw [G.prior_sum]
        exact Finset.sum_congr rfl fun u _ => by rw [mul_one, Finset.mul_sum]
    _ = _ := Finset.sum_comm

variable (D : U → List Bool → ℝ) (hc : ‖c‖ = 1) (hD : ∀ u h, 0 ≤ D u h ∧ D u h ≤ 1)
include hc hD

open Classical in
/-- **Passive membership, general form.** With per-round reach probabilities `r k`, any passive
test with average total error `≤ δ` satisfies `(log(1/2δ) − β₀Q)/KL_ρ ≤ ∑_{k<Q} r k`. -/
theorem passive_membership (ρ : ℝ) (hρ : 0 < ρ) (hρ2 : ρ < 1 / 2)
    (hrange : ∀ s, ρ ≤ G.κ s ∧ G.κ s ≤ 1 - ρ) (hζ : G.ζ = 0 ∨ (G.ζ < G.ν₀ ∧ G.ζ < 1 - G.ν₀))
    (seq : U → ℕ → Sph E) (Q : ℕ) (r : ℕ → ℝ)
    (hr : ∀ k < Q, (∑ u, lam u * (if G.reachC c (seq u k) then (1 : ℝ) else 0)) ≤ r k)
    (δ : ℝ) (herr : G.memErr lam c D (passiveProbe seq) Q ≤ δ) :
    (Real.log (1 / (2 * δ)) - 4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) * Q) /
        ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ)) ≤ ∑ k ∈ Finset.range Q, r k := by
  have h := G.membership_reach_needed_avg lam hlam0 hlam1 c D hc hD ρ hρ hρ2 hrange hζ
    (passiveProbe seq) Q δ herr
  rw [G.memReach_passive lam hlam0 hlam1 c seq Q] at h
  exact h.trans (Finset.sum_le_sum fun k hk => hr k (Finset.mem_range.1 hk))

open Classical in
/-- **Target never appears.** If every arrival reaches `c` with probability `≤ μ`, then
`log(1/2δ) ≤ Q·(KL_ρ·μ + β₀)`. -/
theorem passive_population (ρ : ℝ) (hρ : 0 < ρ) (hρ2 : ρ < 1 / 2)
    (hrange : ∀ s, ρ ≤ G.κ s ∧ G.κ s ≤ 1 - ρ) (hζ : G.ζ = 0 ∨ (G.ζ < G.ν₀ ∧ G.ζ < 1 - G.ν₀))
    (seq : U → ℕ → Sph E) (Q : ℕ) (μ : ℝ)
    (hμ : ∀ k < Q, (∑ u, lam u * (if G.reachC c (seq u k) then (1 : ℝ) else 0)) ≤ μ)
    (δ : ℝ) (herr : G.memErr lam c D (passiveProbe seq) Q ≤ δ) :
    Real.log (1 / (2 * δ)) ≤
      Q * ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * μ +
        4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ))) := by
  have h := G.passive_membership lam hlam0 hlam1 c D hc hD ρ hρ hρ2 hrange hζ seq Q (fun _ => μ)
    hμ δ herr
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  have hKL : 0 < (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) :=
    mul_pos (by linarith) (Real.log_pos (by rw [lt_div_iff₀ hρ]; linarith))
  rw [div_le_iff₀ hKL] at h
  nlinarith

open Classical in
/-- **Target visits on rounds `Vis`, other arrivals reach w.p. `≤ μ`.**
`log(1/2δ) ≤ KL_ρ·(|Vis| + Qμ) + β₀Q`. -/
theorem passive_visits (ρ : ℝ) (hρ : 0 < ρ) (hρ2 : ρ < 1 / 2)
    (hrange : ∀ s, ρ ≤ G.κ s ∧ G.κ s ≤ 1 - ρ) (hζ : G.ζ = 0 ∨ (G.ζ < G.ν₀ ∧ G.ζ < 1 - G.ν₀))
    (seq : U → ℕ → Sph E) (Q : ℕ) (Vis : Finset ℕ) (μ : ℝ) (hμ0 : 0 ≤ μ)
    (hr : ∀ k < Q, k ∉ Vis →
      (∑ u, lam u * (if G.reachC c (seq u k) then (1 : ℝ) else 0)) ≤ μ)
    (δ : ℝ) (herr : G.memErr lam c D (passiveProbe seq) Q ≤ δ) :
    Real.log (1 / (2 * δ)) ≤
      (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * (Vis.card + Q * μ) +
        4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) * Q := by
  have h01 : ∀ k, (∑ u, lam u * (if G.reachC c (seq u k) then (1 : ℝ) else 0)) ≤ 1 := by
    intro k
    calc _ ≤ ∑ u, lam u := Finset.sum_le_sum fun u _ => by
          split_ifs <;> simp [hlam0 u]
      _ = 1 := hlam1
  have h := G.passive_membership lam hlam0 hlam1 c D hc hD ρ hρ hρ2 hrange hζ seq Q
    (fun k => if k ∈ Vis then 1 else μ)
    (fun k hk => by split_ifs with hv; exact h01 k; exact hr k hk hv) δ herr
  have hsum : ∑ k ∈ Finset.range Q, (if k ∈ Vis then (1 : ℝ) else μ) ≤ Vis.card + Q * μ := by
    calc ∑ k ∈ Finset.range Q, (if k ∈ Vis then (1 : ℝ) else μ)
        ≤ ∑ k ∈ Finset.range Q, ((if k ∈ Vis then (1 : ℝ) else 0) + μ) :=
          Finset.sum_le_sum fun k _ => by split_ifs <;> linarith
      _ = ((Finset.range Q).filter (· ∈ Vis)).card + Q * μ := by
          rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
      _ ≤ Vis.card + Q * μ := by
          have hcard : ((Finset.range Q).filter (fun k => k ∈ Vis)).card ≤ Vis.card :=
            Finset.card_le_card (fun k hk => (Finset.mem_filter.1 hk).2)
          have : (((Finset.range Q).filter (fun k => k ∈ Vis)).card : ℝ) ≤ Vis.card :=
            Nat.cast_le.mpr hcard
          linarith
  have hKL : 0 < (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) :=
    mul_pos (by linarith) (Real.log_pos (by rw [lt_div_iff₀ hρ]; linarith))
  rw [div_le_iff₀ hKL] at h
  have := mul_le_mul_of_nonneg_left hsum hKL.le
  linarith

end Gallery

end OracleBounds.GeneralPrior
