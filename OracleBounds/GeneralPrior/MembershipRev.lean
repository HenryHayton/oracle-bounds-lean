import OracleBounds.GeneralPrior.Membership

/-!
# Membership priced by the observable count `E¹[S_c]`

`Gallery.membership_kl` bounds `KL(P⁰‖P¹)` by `KL_ρ·E⁰[S_c]`, the expected number of
candidate-reaching probes **under `H₀`** (candidate not enrolled). The service cannot observe that
count: under `H₀` it holds no record of `c`. The argument is symmetric, and here it is run the
other way: `KL(P¹‖P⁰) ≤ KL_ρ·E¹[S_c] + β₀ᶜᵃᵖ·Q`, with `E¹[S_c]` the expected number of probes
reaching `c` **when `c` is enrolled** — queries the service *can* count (they reach an enrolled
template). Bretagnolle–Huber is symmetric in the two laws, so

  `δI + δII ≥ ½·exp(−KL_ρ·E¹[S_c] − β₀ᶜᵃᵖ·Q)`,  `E¹[S_c] ≥ (log(1/2δ) − β₀ᶜᵃᵖQ)/KL_ρ`.

A per-enrolled-face cap on candidate-reaching queries therefore enforces the membership bound.
(Enforcement must be silent: refusing queries that reach an enrolled face would itself reveal
membership — outside this model, which has the oracle answer every query.)

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι]

open Classical in
/-- **Theorem 18.1(ii), reversed: `KL(P¹‖P⁰) ≤ KL_ρ·E¹[S_c] + β₀ᶜᵃᵖ·Q`.** -/
theorem membership_kl1 (V : ι → Fine) (c : E) (hc : ‖c‖ = 1) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ2 : ρ ≤ 1 / 2) (hrange : ∀ s, ρ ≤ G.κ s ∧ G.κ s ≤ 1 - ρ)
    (hζ : G.ζ = 0 ∨ (G.ζ < G.ν₀ ∧ G.ζ < 1 - G.ν₀))
    (probe : List Bool → Sph E) (Q : ℕ) :
    klPmf (pathProb (G.respWith V c) probe Q []) (pathProb (G.resp V) probe Q []) ≤
      (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * accCount (G.respWith V c) probe (G.reachC c) Q [] +
        4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) * Q := by
  set KL := (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) with hKL
  set β₀ := 4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) with hβ₀
  have hp₀ : ∀ x, 0 ≤ G.resp V x ∧ G.resp V x ≤ 1 := fun x => G.hκ _
  have hp₁ : ∀ x, 0 ≤ G.respWith V c x ∧ G.respWith V c x ≤ 1 := fun x => G.hκ _
  have hac : ∀ x b, bern (G.resp V x) b = 0 → bern (G.respWith V c x) b = 0 := by
    intro x b hb
    exfalso
    have := hrange (G.score V x)
    cases b <;> simp only [bern, Bool.false_eq_true, if_false, if_true] at hb <;>
      unfold resp at hb <;> linarith [this.1, this.2]
  have hβ0 : 0 ≤ β₀ := by
    rcases hζ with h | ⟨h1, h2⟩
    · rw [hβ₀, h]; simp
    · exact div_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))
  have hKL0 : 0 ≤ KL := mul_nonneg (by linarith)
    (Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith))
  have hcost : ∀ x, bkl (G.respWith V c x) (G.resp V x) ≤
      KL * (if G.reachC c x then 1 else 0) + β₀ := by
    intro x
    have hcc := G.cand_cases V c hc 1 (fun s _ s' _ => by
      have h1 := G.hκ (max s s'); have h2 := G.hκ s
      exact abs_le.2 ⟨by linarith, by linarith⟩) x
    split_ifs with hr
    · have := bkl_le_corner hρ hρ2 (hrange _) (hrange _) (a := G.respWith V c x)
        (c := G.resp V x)
      linarith
    · -- quiet round: either identical laws, or both in the ζ-band
      simp only [mul_zero, zero_add]
      unfold reachC at hr
      push Not at hr
      by_cases h0 : G.thr < G.score V x
      · have : G.respWith V c x = G.resp V x := by
          unfold respWith resp; rw [max_eq_left (by linarith)]
        rw [this, bkl_self]; exact hβ0
      · push Not at h0
        have e1 := abs_le.1 (G.hband _ h0)
        have e2 := abs_le.1 (G.hband _ (max_le h0 hr))
        rcases hζ with hz | ⟨hz1, hz2⟩
        · have ha : G.resp V x = G.ν₀ := by unfold resp; rw [hz] at e1; linarith [e1.1, e1.2]
          have hb : G.respWith V c x = G.ν₀ := by
            unfold respWith; rw [hz] at e2; linarith [e2.1, e2.2]
          rw [ha, hb, bkl_self]; exact hβ0
        · set a := G.resp V x
          set b := G.respWith V c x
          have ha1 : a - G.ν₀ = G.κ (G.score V x) - G.ν₀ := rfl
          have hb1 : b - G.ν₀ = G.κ (max (G.score V x) (inner ℝ x.1 c)) - G.ν₀ := rfl
          have hbl : G.ν₀ - G.ζ ≤ a := by linarith [e1.1]
          have hbu : a ≤ G.ν₀ + G.ζ := by linarith [e1.2]
          have hb0 : 0 < a := by linarith
          have hb1' : a < 1 := by linarith
          have hchi := bkl_le_chi2 (hp₁ x).1 (hp₁ x).2 hb0 hb1'
          have hden : 0 < (G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ) := mul_pos (by linarith) (by linarith)
          have hden_le : (G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ) ≤ a * (1 - a) := by
            nlinarith [mul_nonneg (sub_nonneg.2 hbl) (show 0 ≤ 1 - G.ν₀ - G.ζ by linarith),
              mul_nonneg hb0.le (sub_nonneg.2 hbu)]
          have hnum : (b - a) ^ 2 ≤ 4 * G.ζ ^ 2 := by
            have : |b - a| ≤ 2 * G.ζ := by
              rw [abs_le]; constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
            nlinarith [abs_nonneg (b - a), sq_abs (b - a), G.zeta_nonneg]
          refine hchi.trans ?_
          rw [hβ₀]
          calc (b - a) ^ 2 / (a * (1 - a)) ≤ 4 * G.ζ ^ 2 / (a * (1 - a)) :=
                div_le_div_of_nonneg_right hnum (hden.trans_le hden_le).le
            _ ≤ 4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) :=
                div_le_div_of_nonneg_left (by positivity) hden hden_le
  rw [kl_chain hp₁ hp₀ hac Q []]
  exact klRounds_le_cost hp₁ (G.reachC c) KL β₀ hcost Q []


open Classical in
/-- **Bretagnolle–Huber with the observable count:**
`δI + δII ≥ ½·exp(−KL_ρ·E¹[S_c] − β₀ᶜᵃᵖ·Q)`. -/
theorem membership_bh1 (V : ι → Fine) (c : E) (hc : ‖c‖ = 1) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ2 : ρ ≤ 1 / 2) (hrange : ∀ s, ρ ≤ G.κ s ∧ G.κ s ≤ 1 - ρ)
    (hζ : G.ζ = 0 ∨ (G.ζ < G.ν₀ ∧ G.ζ < 1 - G.ν₀))
    (probe : List Bool → Sph E) (Q : ℕ) (D : List Bool → ℝ) (hD : ∀ h, 0 ≤ D h ∧ D h ≤ 1) :
    Real.exp (-((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) *
        accCount (G.respWith V c) probe (G.reachC c) Q [] +
        4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) * Q)) / 2 ≤
      val (G.resp V) probe D Q [] + val (G.respWith V c) probe (fun h => 1 - D h) Q [] := by
  have hp₀ : ∀ x, 0 ≤ G.resp V x ∧ G.resp V x ≤ 1 := fun x => G.hκ _
  have hp₁ : ∀ x, 0 ≤ G.respWith V c x ∧ G.respWith V c x ≤ 1 := fun x => G.hκ _
  have hac : ∀ x b, bern (G.resp V x) b = 0 → bern (G.respWith V c x) b = 0 := by
    intro x b hb
    exfalso
    have := hrange (G.score V x)
    cases b <;> simp only [bern, Bool.false_eq_true, if_false, if_true] at hb <;>
      unfold resp at hb <;> linarith [this.1, this.2]
  set P₀ := pathProb (G.resp V) probe Q []
  set P₁ := pathProb (G.respWith V c) probe Q []
  have hkl := G.membership_kl1 V c hc ρ hρ hρ2 hrange hζ probe Q
  have hBH := bretagnolle_huber P₁ P₀ (pathProb_nonneg probe hp₁ Q [])
    (pathProb_nonneg probe hp₀ Q []) (pathProb_sum probe hp₁ Q []) (pathProb_sum probe hp₀ Q [])
    (fun e he => pathProb_ac hac Q [] e he)
  have herr := sum_min_le_errors P₁ P₀ (fun e => 1 - D ([] ++ List.ofFn e))
    (fun e => ⟨by linarith [(hD ([] ++ List.ofFn e)).2], by linarith [(hD ([] ++ List.ofFn e)).1]⟩)
  simp only [sub_sub_cancel] at herr
  rw [val_eq_sum, val_eq_sum]
  refine le_trans ?_ (hBH.trans (herr.trans (le_of_eq (add_comm _ _))))
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (neg_le_neg hkl)) (by norm_num)

open Classical in
/-- **Membership needs `E¹[S_c] ≥ (log(1/2δ) − β₀ᶜᵃᵖQ)/KL_ρ`** — the count a per-enrolled-face cap
can enforce. -/
theorem membership_reach_needed1 (V : ι → Fine) (c : E) (hc : ‖c‖ = 1) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ2 : ρ < 1 / 2) (hrange : ∀ s, ρ ≤ G.κ s ∧ G.κ s ≤ 1 - ρ)
    (hζ : G.ζ = 0 ∨ (G.ζ < G.ν₀ ∧ G.ζ < 1 - G.ν₀))
    (probe : List Bool → Sph E) (Q : ℕ) (D : List Bool → ℝ) (hD : ∀ h, 0 ≤ D h ∧ D h ≤ 1)
    (δ : ℝ)
    (herr : val (G.resp V) probe D Q [] + val (G.respWith V c) probe (fun h => 1 - D h) Q [] ≤ δ) :
    (Real.log (1 / (2 * δ)) - 4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) * Q) /
        ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ)) ≤
      accCount (G.respWith V c) probe (G.reachC c) Q [] := by
  have hbh := (G.membership_bh1 V c hc ρ hρ hρ2.le hrange hζ probe Q D hD).trans herr
  set S := accCount (G.respWith V c) probe (G.reachC c) Q []
  set KL := (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ)
  set β := 4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) * Q
  have hKL : 0 < KL := mul_pos (by linarith)
    (Real.log_pos (by rw [lt_div_iff₀ hρ]; linarith))
  have h2 : Real.exp (-(KL * S + β)) ≤ 2 * δ := by linarith
  have h3 := Real.log_le_log (Real.exp_pos _) h2
  rw [Real.log_exp] at h3
  have h4 : Real.log (1 / (2 * δ)) = -Real.log (2 * δ) := by rw [one_div, Real.log_inv]
  rw [div_le_iff₀ hKL, h4]
  linarith

end Gallery

end OracleBounds.GeneralPrior
