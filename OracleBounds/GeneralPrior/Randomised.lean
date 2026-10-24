import OracleBounds.GeneralPrior.Corollaries
import OracleBounds.GeneralPrior.Membership

/-!
# Randomised attackers, and membership averaged over the rest of the list

v2 Remark 1.4: every probability statement is proved for a fixed value `U = u` of the attacker's
randomness and then holds for randomised attackers by averaging over `u`. For bounds that are
linear in the attacker's performance this is immediate. For the information branch it is not: the
hypothesis `P[N_ε ≥ m] ≥ ½` holds only *on average* over `u`, so Thm 6.1(4) must be averaged
first, which needs Jensen (`V6.Wave1.convexOn_fano_bound`). Likewise Thm 18.1(ii) averaged over
coins and over a random rest-of-list `G₀` needs Jensen for `exp`.

A randomised attacker is a finite mixture: weights `λ u` over deterministic attackers
`(probe u, out u)`.

* `rand_nominated` — Prop 7.3;
* `rand_thm61_4`, `rand_cor62_ii` — Thm 6.1(4) and Cor 6.2(ii) + Cor 6.3 Q₁;
* `membership_tv_avg`, `membership_bh_avg`, `membership_reach_needed_avg` — Thm 18.1 (i), (ii)
  and its rearrangement, averaged over the attacker's coins **and** over `G₀ ∼ ∏πᵢ`.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]
variable {U : Type*} [Fintype U]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι] [Nonempty Fine]

open Classical in
/-- `P[face i recovered at ε]` for a deterministic attacker. -/
noncomputable def Prec (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε : ℝ) (i : ι) : ℝ :=
  ∑ v, ∑ e, G.wt probe v e * (if G.recovered out ε i v e then (1 : ℝ) else 0)

open Classical in
lemma Prec_le (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)
    (μ₁ ε p : ℝ) (hμ : 0 ≤ μ₁) (hp : 0 ≤ p)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ p) (i : ι) :
    G.Prec probe out ε i ≤ Q * (μ₁ + 2 * G.ζ) + kout * p := by
  have h := G.gallery_recovery i probe kout (outL out) Q μ₁ ε p hμ hp (hcov i) (hballcov i)
  refine le_of_eq_of_le ?_ h
  unfold Prec
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [val_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [outL_ofFn]
  unfold wt recovered prior
  ring_nf

variable (lam : U → ℝ) (hlam0 : ∀ u, 0 ≤ lam u) (hlam1 : ∑ u, lam u = 1)
include hlam0 hlam1

open Classical in
/-- **Prop 7.3, randomised attacker.** -/
theorem rand_nominated (probe : U → List Bool → Sph E) {Q kout : ℕ}
    (out : U → (Fin Q → Bool) → Fin kout → Sph E) (μ₁ ε p : ℝ) (hμ : 0 ≤ μ₁) (hp : 0 ≤ p)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ p) (i : ι) :
    ∑ u, lam u * G.Prec (probe u) (out u) ε i ≤ Q * (μ₁ + 2 * G.ζ) + kout * p :=
  calc ∑ u, lam u * G.Prec (probe u) (out u) ε i
      ≤ ∑ u, lam u * (Q * (μ₁ + 2 * G.ζ) + kout * p) :=
        Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left
          (G.Prec_le (probe u) (out u) μ₁ ε p hμ hp hcov hballcov i) (hlam0 u)
    _ = _ := by rw [← Finset.sum_mul, hlam1, one_mul]

open Classical in
/-- **Thm 6.1(4), randomised attacker** (Jensen over the coins). With `x̄ = Σᵤ λᵤ E_u[N_ε]`:
`x̄·Λ(ε) ≤ B_best(Q) + n·h(min{x̄/n, ½})`. -/
theorem rand_thm61_4 (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (probe : U → List Bool → Sph E) {Q kout : ℕ} (out : U → (Fin Q → Bool) → Fin kout → Sph E)
    (ε p : ℝ) (hp : 0 ≤ p) (hkp : (kout : ℝ) * p < 1)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ p) :
    (∑ u, lam u * G.EN (probe u) (out u) ε) * Real.log (1 / ((kout : ℝ) * p)) ≤
      Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q + (Fintype.card ι : ℝ) *
        Real.binEntropy (min ((∑ u, lam u * G.EN (probe u) (out u) ε) / Fintype.card ι)
          (1 / 2)) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  set Λ := Real.log (1 / ((kout : ℝ) * p))
  set B := Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q
  set f : ℝ → ℝ := fun t => t * Λ - n * Real.binEntropy (min (t / n) (1 / 2)) with hf
  have hn : 0 < n := by show (0 : ℝ) < (Fintype.card ι : ℝ); exact_mod_cast Fintype.card_pos
  have hconv := Wave1.convexOn_fano_bound n Λ hn
  have hx : ∀ u, G.EN (probe u) (out u) ε ∈ Set.Icc 0 n := fun u =>
    ⟨Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun e _ =>
      mul_nonneg (G.wt_nonneg _ v e) (G.Ncount_mem _ ε v e).1, G.EN_le_n _ _ ε⟩
  have hper : ∀ u, f (G.EN (probe u) (out u) ε) ≤ B := fun u => by
    have := G.thm61_4 (probe u) (out u) hν βstar hβ μ₁ hμ hcov ε p hp hkp hballcov
    show _ - _ ≤ B; linarith
  have hJ := hconv.map_sum_le (t := Finset.univ) (w := lam) (p := fun u => G.EN (probe u) (out u) ε)
    (fun u _ => hlam0 u) hlam1 (fun u _ => hx u)
  simp only [smul_eq_mul] at hJ
  have hsum : ∑ u, lam u * f (G.EN (probe u) (out u) ε) ≤ B := by
    calc _ ≤ ∑ u, lam u * B := Finset.sum_le_sum fun u _ =>
          mul_le_mul_of_nonneg_left (hper u) (hlam0 u)
      _ = B := by rw [← Finset.sum_mul, hlam1, one_mul]
  have h2 : (∑ u, lam u * G.EN (probe u) (out u) ε) * Λ - n * Real.binEntropy
      (min ((∑ u, lam u * G.EN (probe u) (out u) ε) / n) (1 / 2)) ≤ B := hJ.trans hsum
  linarith

open Classical in
/-- **Cor 6.2(ii) + Cor 6.3 Q₁, randomised attacker.** If `P[N_ε ≥ m] ≥ ½` *averaged over the
coins*, `1 ≤ m ≤ n`, `k·p(ε) < 1`, `L := log(2en/m) ≤ Λ(ε)`:
`B_best(Q) ≥ (m/2)(Λ(ε) − L)` and `Q ≥ m/(2β*)·(Λ(ε) − L)`. -/
theorem rand_cor62_ii (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ) (hβpos : 0 < βstar)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (probe : U → List Bool → Sph E) {Q kout : ℕ} (out : U → (Fin Q → Bool) → Fin kout → Sph E)
    (ε p : ℝ) (hp : 0 ≤ p) (hkp : (kout : ℝ) * p < 1)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ p)
    (m : ℝ) (hm : 1 ≤ m)
    (hPN : 1 / 2 ≤ ∑ u, lam u * G.PN (probe u) (out u) ε m)
    (hLΛ : Real.log (2 * Real.exp 1 * Fintype.card ι / m) ≤ Real.log (1 / ((kout : ℝ) * p))) :
    m / 2 * (Real.log (1 / ((kout : ℝ) * p)) - Real.log (2 * Real.exp 1 * Fintype.card ι / m)) ≤
      Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q ∧
    m / (2 * βstar) * (Real.log (1 / ((kout : ℝ) * p)) -
      Real.log (2 * Real.exp 1 * Fintype.card ι / m)) ≤ Q := by
  set n : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hndef
  set Λ := Real.log (1 / ((kout : ℝ) * p))
  set B := Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q
  set x := ∑ u, lam u * G.EN (probe u) (out u) ε with hxdef
  have hn0 : 0 < n := by rw [hndef]; exact_mod_cast Fintype.card_pos
  -- Markov, averaged
  have hxm : m / 2 ≤ x := by
    have hle : ∀ u, m * G.PN (probe u) (out u) ε m ≤ G.EN (probe u) (out u) ε := fun u => by
      have h := G.markov (probe u) (out u) ε m (by linarith)
      unfold PN EN
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun e _ => ?_
      have hw := G.wt_nonneg (probe u) v e
      have hN := (G.Ncount_mem (out u) ε v e).1
      split_ifs <;> nlinarith
    calc m / 2 ≤ m * ∑ u, lam u * G.PN (probe u) (out u) ε m := by nlinarith
      _ = ∑ u, lam u * (m * G.PN (probe u) (out u) ε m) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
      _ ≤ x := Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hle u) (hlam0 u)
  have hxn : x ≤ n := by
    calc x ≤ ∑ u, lam u * n := Finset.sum_le_sum fun u _ =>
          mul_le_mul_of_nonneg_left (G.EN_le_n _ _ ε) (hlam0 u)
      _ = n := by rw [← Finset.sum_mul, hlam1, one_mul]
  have h4 := G.rand_thm61_4 lam hlam0 hlam1 hν βstar hβ μ₁ hμ hcov probe out ε p hp hkp hballcov
  have cv := Info.cor62_v7 n m Λ 1 B B x hm one_pos le_rfl hxm hxn (by rw [one_mul]; exact h4)
  have hL : Real.log (2 * Real.exp 1 * n / m) = 1 + Real.log (2 * n / m) :=
    log_two_e hn0 (by linarith)
  have hB : m / 2 * (Λ - Real.log (2 * Real.exp 1 * n / m)) ≤ B := by
    have := cv.2 (by rw [← hL]; exact hLΛ)
    rw [hL]; simpa using this
  refine ⟨hB, ?_⟩
  have hB1 : B ≤ Q * βstar := min_le_left _ _
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-! ### Membership: averaged over coins and over the rest of the list -/

variable (c : E) (D : U → List Bool → ℝ)

open Classical in
/-- Total error `δI + δII`, averaged over the coins `u` and over `G₀ = V ∼ ∏πᵢ`. -/
noncomputable def memErr (probe : U → List Bool → Sph E) (Q : ℕ) : ℝ :=
  ∑ u, ∑ V, lam u * G.prior V * (val (G.resp V) (probe u) (D u) Q [] +
    val (G.respWith V c) (probe u) (fun h => 1 - D u h) Q [])

open Classical in
/-- `E₀[S_c]` averaged over the coins and over `G₀`. -/
noncomputable def memReach (probe : U → List Bool → Sph E) (Q : ℕ) : ℝ :=
  ∑ u, ∑ V, lam u * G.prior V * accCount (G.resp V) (probe u) (G.reachC c) Q []

lemma weights_sum : ∑ u, ∑ V : ι → Fine, lam u * G.prior V = 1 := by
  simp only [← Finset.mul_sum, G.prior_sum, mul_one, hlam1]

lemma weights_nonneg (u : U) (V : ι → Fine) : 0 ≤ lam u * G.prior V :=
  mul_nonneg (hlam0 u) (G.prior_nonneg V)

variable (hc : ‖c‖ = 1) (hD : ∀ u h, 0 ≤ D u h ∧ D u h ≤ 1)
include hc hD

open Classical in
/-- **Thm 18.1(i), averaged over coins and `G₀`.** -/
theorem membership_tv_avg (Δ : ℝ)
    (hΔ : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ∀ s' ∈ Set.Ioc G.thr 1, |G.κ (max s s') - G.κ s| ≤ Δ)
    (probe : U → List Bool → Sph E) (Q : ℕ) :
    1 - Δ * G.memReach lam c probe Q - 2 * Q * G.ζ ≤ G.memErr lam c D probe Q := by
  have hw1 := G.weights_sum lam hlam0 hlam1
  have hper : ∀ u V, 1 - Δ * accCount (G.resp V) (probe u) (G.reachC c) Q [] - 2 * Q * G.ζ ≤
      val (G.resp V) (probe u) (D u) Q [] +
        val (G.respWith V c) (probe u) (fun h => 1 - D u h) Q [] := fun u V =>
    G.membership_tv V c hc Δ hΔ (probe u) Q (D u) (hD u)
  have hlin : ∀ (f : U → (ι → Fine) → ℝ) (a b : ℝ),
      ∑ u, ∑ V, lam u * G.prior V * (a - b * f u V) =
        a - b * ∑ u, ∑ V, lam u * G.prior V * f u V := by
    intro f a b
    calc ∑ u, ∑ V, lam u * G.prior V * (a - b * f u V)
        = ∑ u, ∑ V, (a * (lam u * G.prior V) - b * (lam u * G.prior V * f u V)) :=
          Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun V _ => by ring
      _ = a * (∑ u, ∑ V, lam u * G.prior V) - b * ∑ u, ∑ V, lam u * G.prior V * f u V := by
          simp only [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by rw [hw1, mul_one]
  unfold memErr memReach
  calc 1 - Δ * (∑ u, ∑ V, lam u * G.prior V * accCount (G.resp V) (probe u) (G.reachC c) Q []) -
        2 * Q * G.ζ
      = ∑ u, ∑ V, lam u * G.prior V *
          ((1 - 2 * Q * G.ζ) - Δ * accCount (G.resp V) (probe u) (G.reachC c) Q []) := by
        rw [hlin (fun u V => accCount (G.resp V) (probe u) (G.reachC c) Q [])]; ring
    _ ≤ _ := Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun V _ =>
        mul_le_mul_of_nonneg_left (by linarith [hper u V])
          (G.weights_nonneg lam hlam0 hlam1 u V)

open Classical in
/-- **Thm 18.1(ii), averaged over coins and `G₀`** (Jensen for `exp`):
`avg(δI + δII) ≥ ½·exp(−KL_ρ·avg E₀[S_c] − β₀ᶜᵃᵖ·Q)`. -/
theorem membership_bh_avg (ρ : ℝ) (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2)
    (hrange : ∀ s, ρ ≤ G.κ s ∧ G.κ s ≤ 1 - ρ) (hζ : G.ζ = 0 ∨ (G.ζ < G.ν₀ ∧ G.ζ < 1 - G.ν₀))
    (probe : U → List Bool → Sph E) (Q : ℕ) :
    Real.exp (-((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * G.memReach lam c probe Q +
        4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) * Q)) / 2 ≤
      G.memErr lam c D probe Q := by
  set K := (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ)
  set β := 4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) * Q
  set a : U × (ι → Fine) → ℝ := fun uV =>
    -(K * accCount (G.resp uV.2) (probe uV.1) (G.reachC c) Q [] + β)
  set w : U × (ι → Fine) → ℝ := fun uV => lam uV.1 * G.prior uV.2
  have hw0 : ∀ uV ∈ (Finset.univ : Finset (U × (ι → Fine))), 0 ≤ w uV :=
    fun uV _ => G.weights_nonneg lam hlam0 hlam1 uV.1 uV.2
  have hw1 : ∑ uV, w uV = 1 := by rw [Fintype.sum_prod_type]; exact G.weights_sum lam hlam0 hlam1
  -- Jensen: exp(Σ w a) ≤ Σ w exp(a)
  have hJ := convexOn_exp.map_sum_le (t := Finset.univ) (w := w) (p := a) hw0 hw1
    (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hJ
  have hsum_a : ∑ uV, w uV * a uV = -(K * G.memReach lam c probe Q + β) := by
    unfold memReach
    simp only [a, w, mul_neg, mul_add, Finset.sum_neg_distrib, Finset.sum_add_distrib]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    have : ∑ u, ∑ V : ι → Fine, lam u * G.prior V * β = β := by
      simp only [← Finset.sum_mul]
      rw [show (∑ u, ∑ V : ι → Fine, lam u * G.prior V) = 1 from G.weights_sum lam hlam0 hlam1,
        one_mul]
    rw [this, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun V _ => by ring
  rw [hsum_a] at hJ
  have hper : ∀ uV : U × (ι → Fine), Real.exp (a uV) / 2 ≤
      val (G.resp uV.2) (probe uV.1) (D uV.1) Q [] +
        val (G.respWith uV.2 c) (probe uV.1) (fun h => 1 - D uV.1 h) Q [] := fun uV =>
    G.membership_bh uV.2 c hc ρ hρ hρ2 hrange hζ (probe uV.1) Q (D uV.1) (hD uV.1)
  unfold memErr
  calc Real.exp (-(K * G.memReach lam c probe Q + β)) / 2
      ≤ (∑ uV, w uV * Real.exp (a uV)) / 2 := by linarith
    _ = ∑ uV, w uV * (Real.exp (a uV) / 2) := by rw [Finset.sum_div]; simp only [mul_div_assoc]
    _ ≤ ∑ uV, w uV * (val (G.resp uV.2) (probe uV.1) (D uV.1) Q [] +
          val (G.respWith uV.2 c) (probe uV.1) (fun h => 1 - D uV.1 h) Q []) :=
        Finset.sum_le_sum fun uV _ => mul_le_mul_of_nonneg_left (hper uV) (hw0 uV (by simp))
    _ = _ := by rw [Fintype.sum_prod_type]

open Classical in
/-- **Thm 18.1(ii) rearranged, averaged over coins and `G₀`.** Any randomised test whose
average total error is `≤ δ` needs, on average,
`E₀[S_c] ≥ (log(1/(2δ)) − β₀ᶜᵃᵖ·Q)/KL_ρ` candidate-reaching probes (`ρ < ½`). -/
theorem membership_reach_needed_avg (ρ : ℝ) (hρ : 0 < ρ) (hρ2 : ρ < 1 / 2)
    (hrange : ∀ s, ρ ≤ G.κ s ∧ G.κ s ≤ 1 - ρ) (hζ : G.ζ = 0 ∨ (G.ζ < G.ν₀ ∧ G.ζ < 1 - G.ν₀))
    (probe : U → List Bool → Sph E) (Q : ℕ) (δ : ℝ) (herr : G.memErr lam c D probe Q ≤ δ) :
    (Real.log (1 / (2 * δ)) - 4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) * Q) /
        ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ)) ≤ G.memReach lam c probe Q := by
  have hbh := (G.membership_bh_avg lam hlam0 hlam1 c D hc hD ρ hρ hρ2.le hrange hζ probe Q).trans
    herr
  set S := G.memReach lam c probe Q
  set KL := (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ)
  set β := 4 * G.ζ ^ 2 / ((G.ν₀ - G.ζ) * (1 - G.ν₀ - G.ζ)) * Q
  have hKL : 0 < KL := mul_pos (by linarith) (Real.log_pos (by rw [lt_div_iff₀ hρ]; linarith))
  have h2 : Real.exp (-(KL * S + β)) ≤ 2 * δ := by linarith
  have h3 := Real.log_le_log (Real.exp_pos _) h2
  rw [Real.log_exp] at h3
  have h4 : Real.log (1 / (2 * δ)) = -Real.log (2 * δ) := by rw [one_div, Real.log_inv]
  rw [div_le_iff₀ hKL, h4]
  linarith

end Gallery

end OracleBounds.GeneralPrior
