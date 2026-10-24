import OracleBounds.GeneralPrior.GalleryBounds
import OracleBounds.GeneralPrior.Budget
import OracleBounds.GeneralPrior.Membership
import OracleBounds.GeneralPrior.Information

/-!
# The canonical budget `B_best` (`n-face-general-prior-v2` Thm 5.1(a)–(c), Cor 4.4, Def 2.2)

`Budget.lean` has Thm 5.1(d) (`I ≤ Q·β*`). Here are the other three forms and the canonical
budget built from all four:

* `info_le_const_ref` — the engine of the note's proof: golden formula against an i.i.d.
  `Bern(r)` reference, KL chain rule, and a *pathwise* loud/quiet split where loudness may depend
  on the hidden parameter (this is what distinguishes it from `V6.thm51_process`, whose quiet set
  had to be parameter-free);
* `bkl_le_loud` — a loud round costs at most `log(1/(r ∧ (1−r)))`;
* `thm51_a`, `thm51_b`, `thm51_c` — Thm 5.1(a), (b), (c) for the gallery;
* `staircase` — Cor 4.4: `E[C_Q] ≤ S_n(Q) = Σ_{k≤Q} min{1, n(μ₁+2ζ)k}`;
* `Bbest` and `info_le_Bbest` — Def 2.2 and "Theorem 5.1(a)–(d) proves `I ≤ B_best(Q)`".

No `sorry`s.
-/

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

/-! ### Generic: constant reference -/

section Generic

variable {X : Type*}

lemma accCount_mem (p : X → ℝ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) (probe : List Bool → X)
    (act : X → Prop) [DecidablePred act] :
    ∀ r h, 0 ≤ accCount p probe act r h ∧ accCount p probe act r h ≤ r := by
  intro r
  induction r with
  | zero => intro h; simp [accCount]
  | succ r ih =>
    intro h
    simp only [accCount]
    have h1 := ih (h ++ [true])
    have h2 := ih (h ++ [false])
    have hp0 := (hp (probe h)).1
    have hp1 : 0 ≤ 1 - p (probe h) := by linarith [(hp (probe h)).2]
    have hi : (0 : ℝ) ≤ (if act (probe h) then 1 else 0) ∧ (if act (probe h) then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    push_cast
    constructor
    · nlinarith [mul_nonneg hp0 h1.1, mul_nonneg hp1 h2.1]
    · nlinarith [mul_le_mul_of_nonneg_left h1.2 hp0, mul_le_mul_of_nonneg_left h2.2 hp1]

/-- A loud round against reference `Bern(r)` costs at most `log(1/(r ∧ (1−r)))`. -/
lemma bkl_le_loud {p r : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    bkl p r ≤ Real.log (1 / min r (1 - r)) := by
  simp only [bkl, Fintype.sum_bool, bern, if_true, Bool.false_eq_true, if_false]
  have hr1' : 0 < 1 - r := by linarith
  have hm : 0 < min r (1 - r) := lt_min hr0 hr1'
  have k1 : p * Real.log (p / r) ≤ p * Real.log (1 / r) := by
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [← h]; simp
    refine mul_le_mul_of_nonneg_left ?_ hp0
    rw [Real.log_div h.ne' hr0.ne', one_div, Real.log_inv]
    linarith [Real.log_nonpos hp0 hp1]
  have k2 : (1 - p) * Real.log ((1 - p) / (1 - r)) ≤ (1 - p) * Real.log (1 / (1 - r)) := by
    rcases eq_or_lt_of_le (show 0 ≤ 1 - p by linarith) with h | h
    · rw [← h]; simp
    refine mul_le_mul_of_nonneg_left ?_ h.le
    rw [Real.log_div h.ne' hr1'.ne', one_div, Real.log_inv]
    linarith [Real.log_nonpos h.le (by linarith : 1 - p ≤ 1)]
  have l1 : Real.log (1 / r) ≤ Real.log (1 / min r (1 - r)) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hm (min_le_left _ _))
  have l2 : Real.log (1 / (1 - r)) ≤ Real.log (1 / min r (1 - r)) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hm (min_le_right _ _))
  nlinarith [mul_le_mul_of_nonneg_left l1 hp0,
    mul_le_mul_of_nonneg_left l2 (show 0 ≤ 1 - p by linarith)]

open Classical in
/-- **The engine of Thm 5.1(a)–(c).** Against the i.i.d. `Bern(r)` reference, if every round
costs `KL(Bern(p θ x) ‖ Bern r) ≤ a·[loud θ x] + b` — loudness allowed to depend on `θ` — then
`I(θ; b₁..b_Q) ≤ a · E[#loud rounds] + b·Q`. -/
theorem info_le_const_ref {Θ : Type*} [Fintype Θ] (π : Θ → ℝ) (hπ : ∀ θ, 0 ≤ π θ)
    (hπ1 : ∑ θ, π θ = 1) (p : Θ → X → ℝ) (hp : ∀ θ x, 0 ≤ p θ x ∧ p θ x ≤ 1)
    (probe : List Bool → X) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (loud : Θ → X → Prop) (a b : ℝ)
    (hcost : ∀ θ x, bkl (p θ x) r ≤ a * (if loud θ x then 1 else 0) + b) (Q : ℕ) :
    Info.mutualInfo (fun te : Θ × (Fin Q → Bool) => π te.1 * pathProb (p te.1) probe Q [] te.2)
      ≤ a * ∑ θ, π θ * accCount (p θ) probe (loud θ) Q [] + b * Q := by
  have hq : ∀ _x : X, 0 ≤ r ∧ r ≤ 1 := fun _ => ⟨hr0.le, hr1.le⟩
  have hac : ∀ θ x b', bern ((fun _ : X => r) x) b' = 0 → bern (p θ x) b' = 0 := by
    intro θ x b' h0
    exfalso
    cases b' <;> simp [bern] at h0 <;> linarith
  have hgold := mutualInfo_le_avg_kl π (fun θ => pathProb (p θ) probe Q [])
    (pathProb (fun _ => r) probe Q [])
    hπ hπ1 (fun θ => pathProb_nonneg probe (hp θ) Q []) (fun θ => pathProb_sum probe (hp θ) Q [])
    (pathProb_nonneg probe hq Q []) (pathProb_sum probe hq Q [])
    (fun θ e h0 => pathProb_ac (hac θ) Q [] e h0)
  refine hgold.trans ?_
  have hθ : ∀ θ, klPmf (pathProb (p θ) probe Q []) (pathProb (fun _ => r) probe Q []) ≤
      a * accCount (p θ) probe (loud θ) Q [] + b * Q := by
    intro θ
    rw [kl_chain (hp θ) hq (hac θ)]
    exact klRounds_le_cost (hp θ) (loud θ) a b (hcost θ) Q []
  calc ∑ θ, π θ * klPmf (pathProb (p θ) probe Q []) (pathProb (fun _ => r) probe Q [])
      ≤ ∑ θ, π θ * (a * accCount (p θ) probe (loud θ) Q [] + b * Q) :=
        Finset.sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left (hθ θ) (hπ θ)
    _ = a * ∑ θ, π θ * accCount (p θ) probe (loud θ) Q [] + b * Q * ∑ θ, π θ := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun θ _ => by ring
    _ = _ := by rw [hπ1, mul_one]

end Generic

/-! ### Elementary facts about `t ↦ t·log(2eQ/t)` -/

/-- `t ↦ t·log(A/t)` is nondecreasing on `(0, A/e]`; in the note's form, on `(0, 2Q]` with
`A = 2eQ`. -/
lemma tlog_mono {A s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : Real.exp 1 * t ≤ A) :
    s * Real.log (A / s) ≤ t * Real.log (A / t) := by
  have ht0 : 0 < t := hs.trans_le hst
  have hA : 0 < A := lt_of_lt_of_le (by positivity) ht
  have h1 : 1 ≤ Real.log (A / t) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ ht0]; exact ht
  have h2 : s * Real.log (t / s) ≤ t - s := by
    have := Real.log_le_sub_one_of_pos (div_pos ht0 hs)
    have e : s * (t / s - 1) = t - s := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left this hs.le]
  have e : t * Real.log (A / t) - s * Real.log (A / s) =
      (t - s) * Real.log (A / t) - s * Real.log (t / s) := by
    rw [Real.log_div hA.ne' ht0.ne', Real.log_div hA.ne' hs.ne', Real.log_div ht0.ne' hs.ne']
    ring
  nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hst)]

/-! ### The staircase budget and `B_best` (Def 2.2) -/

/-- `S_n(Q) = Σ_{k=1}^{Q} min{1, n·μ′·k}` (with `μ′ = μ₁ + 2ζ`). -/
noncomputable def Sn (n μ' : ℝ) (Q : ℕ) : ℝ :=
  ∑ k ∈ Finset.range Q, min 1 (n * μ' * ((k : ℝ) + 1))

lemma Sn_nonneg {n μ' : ℝ} (h : 0 ≤ n * μ') (Q : ℕ) : 0 ≤ Sn n μ' Q :=
  Finset.sum_nonneg fun k _ => le_min zero_le_one (mul_nonneg h (by positivity))

lemma Sn_le_Q (n μ' : ℝ) (Q : ℕ) : Sn n μ' Q ≤ Q := by
  unfold Sn
  calc ∑ k ∈ Finset.range Q, min 1 (n * μ' * ((k : ℝ) + 1)) ≤ ∑ _k ∈ Finset.range Q, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => min_le_left _ _
    _ = Q := by simp

/-- `S_n(Q) ≤ n·μ′·Q²` (Cor 6.3's proof: `Σ_{k≤Q} nμ′k ≤ nμ′Q²`). -/
lemma Sn_le_sq {n μ' : ℝ} (h : 0 ≤ n * μ') (Q : ℕ) : Sn n μ' Q ≤ n * μ' * (Q : ℝ) ^ 2 := by
  unfold Sn
  calc ∑ k ∈ Finset.range Q, min 1 (n * μ' * ((k : ℝ) + 1))
      ≤ ∑ _k ∈ Finset.range Q, n * μ' * (Q : ℝ) := Finset.sum_le_sum fun k hk => by
        refine (min_le_right _ _).trans (mul_le_mul_of_nonneg_left ?_ h)
        have := Finset.mem_range.1 hk
        exact_mod_cast this
    _ = n * μ' * (Q : ℝ) ^ 2 := by simp; ring

/-- Form 2 of `B_best`: `β̃·S_n + β₀·Q`, applicable iff `ν₀ ∈ (0,1)`. Inapplicable forms are
replaced by form 1 (`Q·β*`), which leaves the minimum unchanged — this is the note's `+∞`
convention. -/
noncomputable def Bform2 (S ζ ν₀ βstar : ℝ) (Q : ℕ) : ℝ :=
  if 0 < ν₀ ∧ ν₀ < 1 then
    Real.log (1 / min ν₀ (1 - ν₀)) * S + ζ ^ 2 / (ν₀ * (1 - ν₀)) * Q
  else Q * βstar

/-- Form 3 of `B_best`: `inf_{θ∈(0,1]} [log(2/θ)·S_n + (θ + 4ζ + 4ζ²/θ)·Q]`. -/
noncomputable def Bform3 (S ζ : ℝ) (Q : ℕ) : ℝ :=
  ⨅ θ : Set.Ioc (0 : ℝ) 1, (Real.log (2 / θ) * S + (θ + 4 * ζ + 4 * ζ ^ 2 / θ) * Q)

/-- Form 4 of `B_best`: `S_n·log(2eQ/S_n)`, applicable iff `ζ = 0` (`0·log(·) = 0`). -/
noncomputable def Bform4 (S ζ βstar : ℝ) (Q : ℕ) : ℝ :=
  if ζ = 0 then S * Real.log (2 * Real.exp 1 * Q / S) else Q * βstar

/-- **Definition 2.2, `B_best(Q)`**, with `S = S_n(Q)` for `μ′ = μ₁ + 2ζ`. -/
noncomputable def Bbest (n μ₁ ζ ν₀ βstar : ℝ) (Q : ℕ) : ℝ :=
  min (Q * βstar) (min (Bform2 (Sn n (μ₁ + 2 * ζ) Q) ζ ν₀ βstar Q)
    (min (Bform3 (Sn n (μ₁ + 2 * ζ) Q) ζ Q) (Bform4 (Sn n (μ₁ + 2 * ζ) Q) ζ βstar Q)))

lemma Bform3_le {S ζ : ℝ} (hS : 0 ≤ S) (hζ : 0 ≤ ζ) (Q : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Ioc (0 : ℝ) 1) :
    Bform3 S ζ Q ≤ Real.log (2 / θ) * S + (θ + 4 * ζ + 4 * ζ ^ 2 / θ) * Q := by
  unfold Bform3
  refine ciInf_le ⟨0, ?_⟩ (⟨θ, hθ⟩ : Set.Ioc (0 : ℝ) 1)
  rintro _ ⟨⟨t, ht0, ht1⟩, rfl⟩
  have hl : 0 ≤ Real.log (2 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht0]; linarith)
  positivity

/-! ### The gallery -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι]

/-- Product prior weight of a gallery. -/
noncomputable def prior (v : ι → Fine) : ℝ := ∏ j, G.π j (v j)

omit [DecidableEq ι] [Nonempty ι] in
lemma prior_nonneg (v : ι → Fine) : 0 ≤ G.prior v :=
  Finset.prod_nonneg fun j _ => G.hπ0 j (v j)

omit [Nonempty ι] in
lemma prior_sum : ∑ v, G.prior v = 1 := prodPrior_sum G.π G.hπ1

/-- A round is *loud* when the probe reaches some face: `maxᵢ⟨x, gᵢ⟩ > thr` (Def 1.5). -/
def loud (v : ι → Fine) (x : Sph E) : Prop := G.thr < G.score v x

omit [DecidableEq ι] in
lemma resp_mem (v : ι → Fine) (x : Sph E) : 0 ≤ G.resp v x ∧ G.resp v x ≤ 1 := G.hκ _

/-- The attacker's joint information `I(G; b₁..b_Q)` (deterministic attacker, i.e. given `U`). -/
noncomputable def jointInfo (probe : List Bool → Sph E) (Q : ℕ) : ℝ :=
  Info.mutualInfo (fun te : (ι → Fine) × (Fin Q → Bool) =>
    G.prior te.1 * pathProb (G.resp te.1) probe Q [] te.2)

open Classical in
/-- `E[C_Q]`, the expected number of loud rounds. -/
noncomputable def ECQ (probe : List Bool → Sph E) (Q : ℕ) : ℝ :=
  ∑ v, G.prior v * accCount (G.resp v) probe (G.loud v) Q []

lemma ECQ_mem (probe : List Bool → Sph E) (Q : ℕ) : 0 ≤ G.ECQ probe Q ∧ G.ECQ probe Q ≤ Q := by
  classical
  have hb := fun v => accCount_mem (G.resp v) (G.resp_mem v) probe (G.loud v) Q []
  unfold ECQ
  constructor
  · exact Finset.sum_nonneg fun v _ => mul_nonneg (G.prior_nonneg v) (by convert (hb v).1)
  · calc ∑ v, G.prior v * accCount (G.resp v) probe (G.loud v) Q [] ≤ ∑ v, G.prior v * Q :=
          Finset.sum_le_sum fun v _ =>
            mul_le_mul_of_nonneg_left (by convert (hb v).2) (G.prior_nonneg v)
      _ = Q := by rw [← Finset.sum_mul, G.prior_sum, one_mul]

omit [DecidableEq ι] in
lemma quiet_band (v : ι → Fine) (x : Sph E) (hq : ¬ G.loud v x) :
    |G.resp v x - G.ν₀| ≤ G.ζ := by
  unfold loud at hq; push Not at hq
  exact G.hband _ hq

open Classical in
/-- **Theorem 5.1(a).** If `ν₀ ∈ (0,1)`: `I ≤ β̃·E[C_Q] + β₀·Q`, `β̃ = log(1/(ν₀ ∧ (1−ν₀)))`,
`β₀ = ζ²/(ν₀(1−ν₀))`. -/
theorem thm51_a (hν0 : 0 < G.ν₀) (hν1 : G.ν₀ < 1) (probe : List Bool → Sph E) (Q : ℕ) :
    G.jointInfo probe Q ≤ Real.log (1 / min G.ν₀ (1 - G.ν₀)) * G.ECQ probe Q +
      G.ζ ^ 2 / (G.ν₀ * (1 - G.ν₀)) * Q := by
  have hden : 0 < G.ν₀ * (1 - G.ν₀) := mul_pos hν0 (by linarith)
  have hβ0 : 0 ≤ G.ζ ^ 2 / (G.ν₀ * (1 - G.ν₀)) := by positivity
  refine info_le_const_ref G.prior G.prior_nonneg G.prior_sum G.resp G.resp_mem probe G.ν₀ hν0 hν1
    G.loud _ _ (fun v x => ?_) Q
  have hp := G.resp_mem v x
  split_ifs with hl
  · linarith [bkl_le_loud hp.1 hp.2 hν0 hν1]
  · have hb := G.quiet_band v x hl
    have hsq : (G.resp v x - G.ν₀) ^ 2 ≤ G.ζ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have := bkl_le_chi2 hp.1 hp.2 hν0 hν1
    have h2 : (G.resp v x - G.ν₀) ^ 2 / (G.ν₀ * (1 - G.ν₀)) ≤ G.ζ ^ 2 / (G.ν₀ * (1 - G.ν₀)) :=
      div_le_div_of_nonneg_right hsq hden.le
    linarith

open Classical in
/-- **Theorem 5.1(b).** For `ν₀ ∈ [0,1]` and every `θ ∈ (0,1]`:
`I ≤ log(2/θ)·E[C_Q] + (θ + 4ζ + 4ζ²/θ)·Q`. -/
theorem thm51_b (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (probe : List Bool → Sph E) (Q : ℕ) :
    G.jointInfo probe Q ≤ Real.log (2 / θ) * G.ECQ probe Q +
      (θ + 4 * G.ζ + 4 * G.ζ ^ 2 / θ) * Q := by
  set r := (1 - θ) * G.ν₀ + θ / 2 with hr
  have hζ := G.zeta_nonneg
  have hrl : θ / 2 ≤ r := by nlinarith [hν.1]
  have hru : r ≤ 1 - θ / 2 := by nlinarith [hν.2]
  have hr0 : 0 < r := by linarith
  have hr1 : r < 1 := by linarith
  have hrr : θ / 4 ≤ r * (1 - r) := by nlinarith [mul_nonneg (sub_nonneg.2 hrl) (sub_nonneg.2 hru)]
  have hq0 : 0 ≤ θ + 4 * G.ζ + 4 * G.ζ ^ 2 / θ := by positivity
  refine info_le_const_ref G.prior G.prior_nonneg G.prior_sum G.resp G.resp_mem probe r hr0 hr1
    G.loud _ _ (fun v x => ?_) Q
  have hp := G.resp_mem v x
  split_ifs with hl
  · have h1 := bkl_le_loud hp.1 hp.2 hr0 hr1
    have h2 : Real.log (1 / min r (1 - r)) ≤ Real.log (2 / θ) := by
      apply Real.log_le_log (by have := lt_min hr0 (by linarith : (0:ℝ) < 1 - r); positivity)
      rw [show (2 : ℝ) / θ = 1 / (θ / 2) by field_simp]
      exact one_div_le_one_div_of_le (by positivity) (le_min hrl (by linarith))
    linarith
  · have hb := abs_le.1 (G.quiet_band v x hl)
    have hpr : |G.resp v x - r| ≤ G.ζ + θ / 2 := by
      rw [abs_le]; constructor <;> nlinarith [hν.1, hν.2]
    have hsq : (G.resp v x - r) ^ 2 ≤ (G.ζ + θ / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hpr 2
    have hchi := bkl_le_chi2 hp.1 hp.2 hr0 hr1
    have h2 : (G.resp v x - r) ^ 2 / (r * (1 - r)) ≤ (G.ζ + θ / 2) ^ 2 / (θ / 4) :=
      div_le_div₀ (sq_nonneg _) hsq (by positivity) hrr
    have h3 : (G.ζ + θ / 2) ^ 2 / (θ / 4) = θ + 4 * G.ζ + 4 * G.ζ ^ 2 / θ := by
      field_simp; ring
    linarith

open Classical in
/-- **Theorem 5.1(c).** If `ζ = 0` (and `ν₀ ∈ [0,1]`): `I ≤ E[C_Q]·log(2eQ/E[C_Q])`
(`0·log(·) = 0`). -/
theorem thm51_c (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (hζ : G.ζ = 0) (probe : List Bool → Sph E) (Q : ℕ) :
    G.jointInfo probe Q ≤ G.ECQ probe Q * Real.log (2 * Real.exp 1 * Q / G.ECQ probe Q) := by
  have hb := fun θ h0 h1 => G.thm51_b hν θ h0 h1 probe Q
  simp only [hζ, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div] at hb
  obtain ⟨hE0, hEQ⟩ := G.ECQ_mem probe Q
  rcases eq_or_lt_of_le hE0 with h0 | hpos
  · -- no loud rounds in expectation: `I ≤ θQ` for every `θ ∈ (0,1]`, so `I ≤ 0`
    rw [← h0, zero_mul]
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
    set θ := min 1 (δ / (Q + 1)) with hθ
    have hθ0 : 0 < θ := lt_min one_pos (by positivity)
    have hθ1 : θ ≤ 1 := min_le_left _ _
    have := hb θ hθ0 hθ1
    rw [← h0, mul_zero, zero_add] at this
    have hθQ : θ * Q ≤ δ := by
      calc θ * Q ≤ δ / (Q + 1) * Q := mul_le_mul_of_nonneg_right (min_le_right _ _) hQ
        _ ≤ δ := by rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  · have hQpos : (0 : ℝ) < Q := hpos.trans_le hEQ
    have := hb (G.ECQ probe Q / Q) (div_pos hpos hQpos) ((div_le_one hQpos).2 hEQ)
    rw [div_mul_cancel₀ _ hQpos.ne'] at this
    have e : Real.log (2 * Real.exp 1 * Q / G.ECQ probe Q) =
        Real.log (2 / (G.ECQ probe Q / Q)) + 1 := by
      rw [show 2 * Real.exp 1 * Q / G.ECQ probe Q = Real.exp 1 * (2 / (G.ECQ probe Q / Q)) by
        field_simp, Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
      ring
    rw [e]; linarith

open Classical in
/-- **Corollary 4.4 (staircase).** `E[C_Q] ≤ S_n(Q) = Σ_{k=1}^{Q} min{1, n(μ₁+2ζ)k}`: round `k`
is loud only if some face has been hit by time `k`, which Cor 4.2 bounds by `k(μ₁+2ζ)` per face. -/
theorem staircase [DecidableEq Fine] [Nonempty Fine] (probe : List Bool → Sph E) (Q : ℕ) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁) :
    G.ECQ probe Q ≤ Sn (Fintype.card ι) (μ₁ + 2 * G.ζ) Q := by
  set f : (ι → Fine) → ℕ → List Bool → ℝ :=
    fun v k h => if G.loud v (probe (h.take k)) then 1 else 0 with hf
  have hf01 : ∀ v k h, 0 ≤ f v k h ∧ f v k h ≤ 1 := by
    intro v k h; simp only [hf]; split_ifs <;> norm_num
  -- E[C_Q] as a sum over rounds
  have hsplit : G.ECQ probe Q =
      ∑ k ∈ Finset.range Q, ∑ v, G.prior v * val (G.resp v) probe (f v k) Q [] := by
    unfold ECQ
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [accCount_eq_val, ← Finset.mul_sum]
    congr 1
    simp only [List.length_nil, zero_add, ← Finset.range_eq_Ico]
    exact val_sum (G.resp v) probe (Finset.range Q) (fun k h => f v k h) Q []
  rw [hsplit]
  unfold Sn
  refine Finset.sum_le_sum fun k hk => ?_
  have hkQ : k + 1 ≤ Q := Finset.mem_range.1 hk
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hkQ
  refine le_min ?_ ?_
  · calc ∑ v, G.prior v * val (G.resp v) probe (f v k) Q [] ≤ ∑ v, G.prior v * 1 :=
          Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
            (val_mem_Icc probe (G.resp_mem v) (hf01 v k) Q []).2 (G.prior_nonneg v)
      _ = 1 := by simp [G.prior_sum]
  · -- round `k+1` loud ⇒ some face hit within `k+1` rounds
    have hround : ∀ v, val (G.resp v) probe (f v k) Q [] ≤
        ∑ i, val (G.resp v) probe (hitInd G.reachG probe (v i)) (k + 1) [] := by
      intro v
      have hpre : val (G.resp v) probe (f v k) Q [] = val (G.resp v) probe (f v k) (k + 1) [] := by
        rw [hs, ← val_of_prefix (G.resp v) probe (f v k) (k + 1) s]
        apply val_mono_eq
        intro h' _
        simp only [hf, List.take_take, min_eq_left (Nat.le_succ k)]
      rw [hpre, ← val_sum]
      refine val_mono probe (G.resp_mem v) (k + 1) [] fun h' hl => ?_
      simp only [List.length_nil, zero_add] at hl
      simp only [hf]
      split_ifs with hloud
      · unfold loud score at hloud
        obtain ⟨j, -, hj⟩ := (Finset.lt_sup'_iff _).1 hloud
        have hhit : hitInd G.reachG probe (v j) h' = 1 := by
          unfold hitInd
          rw [if_pos ⟨k, by omega, hj⟩]
        calc (1 : ℝ) = hitInd G.reachG probe (v j) h' := hhit.symm
          _ ≤ ∑ i, hitInd G.reachG probe (v i) h' :=
            Finset.single_le_sum (f := fun i => hitInd G.reachG probe (v i) h')
              (fun i _ => by unfold hitInd; split_ifs <;> norm_num) (Finset.mem_univ j)
      · exact Finset.sum_nonneg fun i _ => by unfold hitInd; split_ifs <;> norm_num
    calc ∑ v, G.prior v * val (G.resp v) probe (f v k) Q []
        ≤ ∑ v, G.prior v * ∑ i, val (G.resp v) probe (hitInd G.reachG probe (v i)) (k + 1) [] :=
          Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hround v) (G.prior_nonneg v)
      _ = ∑ i, ∑ v, G.prior v * val (G.resp v) probe (hitInd G.reachG probe (v i)) (k + 1) [] := by
          simp only [Finset.mul_sum]; exact Finset.sum_comm
      _ ≤ ∑ _i : ι, ((k + 1 : ℕ) : ℝ) * (μ₁ + 2 * G.ζ) :=
          Finset.sum_le_sum fun i _ => G.gallery_hitting i probe (k + 1) μ₁ hμ (hcov i)
      _ = Fintype.card ι * (μ₁ + 2 * G.ζ) * ((k : ℝ) + 1) := by simp; ring

open Classical in
/-- **"Theorem 5.1(a)–(d) proves `I(G; b₁..b_Q | U) ≤ B_best(Q)`"** (Def 2.2). Here `β*` is any
bound on the per-round Bernoulli KL to `½` (`log 2` always; `Cap(ρ)` under the range condition),
and `μ₁` any valid reach bound. -/
theorem info_le_Bbest [DecidableEq Fine] [Nonempty Fine] (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (probe : List Bool → Sph E) (Q : ℕ) :
    G.jointInfo probe Q ≤ Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q := by
  unfold Bbest
  set S := Sn (Fintype.card ι) (μ₁ + 2 * G.ζ) Q with hS
  have hζ := G.zeta_nonneg
  have hSt := G.staircase probe Q μ₁ hμ hcov
  rw [← hS] at hSt
  have hS0 : 0 ≤ S := Sn_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) Q
  have hSQ : S ≤ Q := Sn_le_Q _ _ Q
  obtain ⟨hE0, hEQ⟩ := G.ECQ_mem probe Q
  have h1 : G.jointInfo probe Q ≤ Q * βstar := by
    have := info_le_global G.prior G.prior_nonneg G.prior_sum G.resp (fun v x => G.resp_mem v x)
      probe βstar hβ Q
    unfold jointInfo; linarith
  refine le_min h1 (le_min ?_ (le_min ?_ ?_))
  · unfold Bform2
    split_ifs with h
    · have ha := G.thm51_a h.1 h.2 probe Q
      have hl : 0 ≤ Real.log (1 / min G.ν₀ (1 - G.ν₀)) :=
        Real.log_nonneg (by
          rw [le_div_iff₀ (lt_min h.1 (by linarith))]; linarith [min_le_left G.ν₀ (1 - G.ν₀)])
      nlinarith [mul_le_mul_of_nonneg_left hSt hl]
    · exact h1
  · unfold Bform3
    haveI : Nonempty (Set.Ioc (0 : ℝ) 1) := ⟨⟨1, one_pos, le_rfl⟩⟩
    refine le_ciInf fun ⟨θ, hθ0, hθ1⟩ => ?_
    have hb := G.thm51_b hν θ hθ0 hθ1 probe Q
    have hl : 0 ≤ Real.log (2 / θ) := Real.log_nonneg (by rw [le_div_iff₀ hθ0]; linarith)
    nlinarith [mul_le_mul_of_nonneg_left hSt hl]
  · unfold Bform4
    split_ifs with h
    · have hc := G.thm51_c hν h probe Q
      refine hc.trans ?_
      rcases eq_or_lt_of_le hE0 with h0 | hpos
      · rw [← h0, zero_mul]
        rcases eq_or_lt_of_le hS0 with hS00 | hSpos
        · rw [← hS00, zero_mul]
        · exact mul_nonneg hS0 (Real.log_nonneg (by
            rw [le_div_iff₀ hSpos]; nlinarith [Real.add_one_le_exp (1 : ℝ)]))
      · exact tlog_mono hpos hSt (by nlinarith [Real.exp_pos 1])
    · exact h1

end Gallery

end OracleBounds.GeneralPrior
