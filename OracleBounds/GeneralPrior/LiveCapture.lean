import OracleBounds.GeneralPrior.Membership

/-!
# Restricted probes: live capture (technical note §3.6, Proposition 3.6.1)

**Statements signed off by the administrator, 23 Sep 2026 (proof by subagent). Faithful to
technical note Proposition 3.6.1: `presReach` is `R(G)`, `TwoValued` is the two-valued kernel
condition, and the test bound is stated at `E_R[N_p]` with `KL_ρ = (1−2ρ)log((1−ρ)/ρ)`.**

Every probe must lie in a set `P ⊆ Sph E` of *presentable* faces. For a gallery `V` the note
writes `R(V) := {x ∈ P : maxᵢ ⟨x, g(Vᵢ)⟩ > thr}` for the presentable probes that reach the list,
and calls a kernel *two-valued* if it is constant on `[-1, thr]` and constant on `(thr, 1]`.

* **(i)** `live_capture_pathProb` / `live_capture_val`: for a two-valued kernel and any attacker
  all of whose probes lie in `P`, the law of the transcript given the gallery depends on the
  gallery only through `R(V)`: if `R(V) = R(V')` the two transcript pmfs are *equal* (hence so is
  every expectation `val`). The attacker's own randomness `U` is fixed throughout (a deterministic
  `probe` rule), which is the note's convention; a randomised attacker is a mixture of these, so
  the joint law of `(U, b_{1:Q})` follows by averaging.
* **(ii)** `live_capture_test`: under the range condition `κ ∈ [ρ, 1−ρ]`, if `R(V)` and `R(V')`
  differ only in whether they contain the single probe `p`, then any (randomised) test `D` between
  the two worlds has `δ_I + δ_II ≥ ½ exp(−KL_ρ · E_V[N_p])`, where `N_p` counts the rounds that
  probe `p` and `KL_ρ = (1−2ρ)·log((1−ρ)/ρ)`.

The proof of (ii) is the note's: by (i) the two response functions agree at every presentable
probe other than `p`, so the KL chain rule (`OracleBounds.V6.kl_chain`) charges at most `KL_ρ`
per round probing `p` and nothing otherwise (`klRounds_le_cost`), and Bretagnolle–Huber
(`bretagnolle_huber`, `sum_min_le_errors`) converts the KL bound into the error bound — exactly as
in `Gallery.membership_bh` (Theorem 2.7.1), but with the reach count replaced by the count of
probes at `p`.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

/-! ### The transcript law depends on the kernel only through its values at the probes -/

section PathCongr

variable {X : Type*}

/-- Two kernels agreeing at every probe issued by `probe` give the same transcript pmf. -/
lemma pathProb_congr {p q : X → ℝ} {probe : List Bool → X}
    (hpq : ∀ h, p (probe h) = q (probe h)) :
    ∀ (r : ℕ) (h : List Bool) (e : Fin r → Bool),
      pathProb p probe r h e = pathProb q probe r h e := by
  intro r
  induction r with
  | zero => intro h e; rfl
  | succ r ih => intro h e; simp only [pathProb, hpq h, ih]

/-- Two kernels agreeing at every probe issued by `probe` give the same expectations. -/
lemma val_congr_probe {p q : X → ℝ} {probe : List Bool → X}
    (hpq : ∀ h, p (probe h) = q (probe h)) (F : List Bool → ℝ) :
    ∀ (r : ℕ) (h : List Bool), val p probe F r h = val q probe F r h := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih => intro h; simp only [val_succ, hpq h, ih]

end PathCongr

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [Fintype Fine]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι]

/-- `R(V)` of §3.6: the presentable probes that reach the list `V`. -/
def presReach (P : Set (Sph E)) (V : ι → Fine) : Set (Sph E) :=
  {x | x ∈ P ∧ G.thr < G.score V x}

/-- A kernel is **two-valued** when it is constant on `[-1, thr]` and constant on `(thr, 1]`
(the only two ranges a score of unit vectors can occupy). Both kernels of §4.1 are. -/
def TwoValued : Prop :=
  ∃ κq κl : ℝ, (∀ s ∈ Set.Icc (-1 : ℝ) G.thr, G.κ s = κq) ∧
    (∀ s ∈ Set.Ioc G.thr 1, G.κ s = κl)

omit [Nonempty ι] in
lemma twoValued_of_flip (κq κl : ℝ) (hq : ∀ s ≤ G.thr, G.κ s = κq)
    (hl : ∀ s, G.thr < s → G.κ s = κl) : G.TwoValued :=
  ⟨κq, κl, fun _ hs => hq _ hs.2, fun _ hs => hl _ hs.1⟩

/-- For a two-valued kernel the response probability at `x` is determined by whether `x` reaches
the list. -/
lemma resp_eq_of_reach_iff (h2 : G.TwoValued) (V V' : ι → Fine) (x : Sph E)
    (hiff : G.thr < G.score V x ↔ G.thr < G.score V' x) :
    G.resp V x = G.resp V' x := by
  obtain ⟨κq, κl, hq, hl⟩ := h2
  have hm := G.score_mem V x
  have hm' := G.score_mem V' x
  show G.κ (G.score V x) = G.κ (G.score V' x)
  by_cases h : G.thr < G.score V x
  · rw [hl _ ⟨h, hm.2⟩, hl _ ⟨hiff.1 h, hm'.2⟩]
  · have h' : ¬ G.thr < G.score V' x := fun hc => h (hiff.2 hc)
    rw [hq _ ⟨hm.1, not_lt.1 h⟩, hq _ ⟨hm'.1, not_lt.1 h'⟩]

/-- **Proposition 3.6.1(i), transcript pmfs.** For a two-valued kernel and an attacker all of
whose probes are presentable, two galleries with the same presentable reach set `R` induce the
*same* law on the transcript `b_{1:Q}`. -/
theorem live_capture_pathProb (P : Set (Sph E)) (h2 : G.TwoValued) (V V' : ι → Fine)
    (hR : G.presReach P V = G.presReach P V')
    (probe : List Bool → Sph E) (hprobe : ∀ h, probe h ∈ P) (Q : ℕ) :
    pathProb (G.resp V) probe Q [] = pathProb (G.resp V') probe Q [] := by
  have hstep : ∀ h : List Bool, G.resp V (probe h) = G.resp V' (probe h) := by
    intro h
    refine G.resp_eq_of_reach_iff h2 V V' (probe h) ?_
    have h1 := Set.ext_iff.1 hR (probe h)
    simp only [presReach, Set.mem_setOf_eq] at h1
    exact ⟨fun hlt => (h1.1 ⟨hprobe h, hlt⟩).2, fun hlt => (h1.2 ⟨hprobe h, hlt⟩).2⟩
  funext e
  exact pathProb_congr hstep Q [] e

/-- **Proposition 3.6.1(i), expectations.** Consequently every functional of the transcript has
the same expectation under the two galleries. -/
theorem live_capture_val (P : Set (Sph E)) (h2 : G.TwoValued) (V V' : ι → Fine)
    (hR : G.presReach P V = G.presReach P V')
    (probe : List Bool → Sph E) (hprobe : ∀ h, probe h ∈ P) (F : List Bool → ℝ) (Q : ℕ) :
    val (G.resp V) probe F Q [] = val (G.resp V') probe F Q [] := by
  refine val_congr_probe (fun h => ?_) F Q []
  refine G.resp_eq_of_reach_iff h2 V V' (probe h) ?_
  have h1 := Set.ext_iff.1 hR (probe h)
  simp only [presReach, Set.mem_setOf_eq] at h1
  exact ⟨fun hlt => (h1.1 ⟨hprobe h, hlt⟩).2, fun hlt => (h1.2 ⟨hprobe h, hlt⟩).2⟩

open Classical in
/-- **Proposition 3.6.1(ii).** Under the range condition `κ ∈ [ρ, 1−ρ]` (so `KL_ρ` is the note's
`(1−2ρ)·log((1−ρ)/ρ)`), let the presentable reach sets `R(V)` and `R(V')` differ only in whether
they contain the single probe `p`. Then for any adaptive attacker with presentable probes and any
randomised decision `D` (the probability of declaring the `V'` world after transcript `h`),

  `δ_I + δ_II ≥ ½ · exp(−KL_ρ · E_V[N_p])`,

where `N_p` is the number of rounds that probe `p` and the expectation is under the `V` world. -/
theorem live_capture_test (P : Set (Sph E)) (h2 : G.TwoValued)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (hrange : ∀ s, ρ ≤ G.κ s ∧ G.κ s ≤ 1 - ρ)
    (V V' : ι → Fine) (p : Sph E)
    (hR : G.presReach P V \ {p} = G.presReach P V' \ {p})
    (probe : List Bool → Sph E) (hprobe : ∀ h, probe h ∈ P) (Q : ℕ)
    (D : List Bool → ℝ) (hD : ∀ h, 0 ≤ D h ∧ D h ≤ 1) :
    Real.exp (-((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) *
        accCount (G.resp V) probe (fun x => x = p) Q [])) / 2 ≤
      val (G.resp V) probe D Q [] + val (G.resp V') probe (fun h => 1 - D h) Q [] := by
  set KL := (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) with hKLdef
  have hKL0 : 0 ≤ KL :=
    mul_nonneg (by linarith) (Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith))
  have hp0 : ∀ x, 0 ≤ G.resp V x ∧ G.resp V x ≤ 1 := fun x => G.hκ _
  -- the reference kernel: `V'` on presentable probes, `V` elsewhere (never queried)
  set q : Sph E → ℝ := fun x => if x ∈ P then G.resp V' x else G.resp V x with hqdef
  have hq_at : ∀ h, q (probe h) = G.resp V' (probe h) := fun h => if_pos (hprobe h)
  have hq01 : ∀ x, 0 ≤ q x ∧ q x ≤ 1 := by
    intro x; simp only [hqdef]; split_ifs <;> exact G.hκ _
  have hqrange : ∀ x, ρ ≤ q x ∧ q x ≤ 1 - ρ := by
    intro x; simp only [hqdef]; split_ifs <;> exact hrange _
  have hac : ∀ x b, bern (q x) b = 0 → bern (G.resp V x) b = 0 := by
    intro x b hb
    exfalso
    have hx := hqrange x
    cases b <;> simp only [bern, Bool.false_eq_true, if_false, if_true] at hb <;>
      linarith [hx.1, hx.2]
  -- off `p`, the presentable responses agree
  have hsame : ∀ x, x ∈ P → x ≠ p → G.resp V x = G.resp V' x := by
    intro x hxP hxp
    refine G.resp_eq_of_reach_iff h2 V V' x ?_
    have h1 := Set.ext_iff.1 hR x
    simp only [presReach, Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff] at h1
    exact ⟨fun hlt => ((h1.1 ⟨⟨hxP, hlt⟩, hxp⟩).1).2,
      fun hlt => ((h1.2 ⟨⟨hxP, hlt⟩, hxp⟩).1).2⟩
  have hcost : ∀ x, bkl (G.resp V x) (q x) ≤ KL * (if x = p then 1 else 0) + 0 := by
    intro x
    rw [add_zero]
    by_cases hxp : x = p
    · rw [if_pos hxp, mul_one]
      exact bkl_le_corner (a := G.resp V x) (c := q x) hρ hρ2 (hrange _) (hqrange x)
    · rw [if_neg hxp, mul_zero]
      have hqx : q x = G.resp V x := by
        simp only [hqdef]
        by_cases hxP : x ∈ P
        · rw [if_pos hxP, ← hsame x hxP hxp]
        · rw [if_neg hxP]
      rw [hqx, bkl_self]
  have hkl : klPmf (pathProb (G.resp V) probe Q []) (pathProb q probe Q []) ≤
      KL * accCount (G.resp V) probe (fun x => x = p) Q [] := by
    rw [kl_chain hp0 hq01 hac Q []]
    have h := klRounds_le_cost (probe := probe) hp0 (fun x => x = p) KL 0 hcost Q []
    simpa using h
  have hBH := bretagnolle_huber (pathProb (G.resp V) probe Q []) (pathProb q probe Q [])
    (pathProb_nonneg probe hp0 Q []) (pathProb_nonneg probe hq01 Q [])
    (pathProb_sum probe hp0 Q []) (pathProb_sum probe hq01 Q [])
    (fun e he => pathProb_ac hac Q [] e he)
  have herr := sum_min_le_errors (pathProb (G.resp V) probe Q []) (pathProb q probe Q [])
    (fun e => D ([] ++ List.ofFn e)) (fun e => hD _)
  have hqeq : pathProb q probe Q [] = pathProb (G.resp V') probe Q [] := by
    funext e; exact pathProb_congr hq_at Q [] e
  rw [val_eq_sum, val_eq_sum, ← hqeq]
  refine le_trans ?_ (hBH.trans herr)
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (neg_le_neg hkl)) (by norm_num)

end Gallery

end OracleBounds.GeneralPrior
