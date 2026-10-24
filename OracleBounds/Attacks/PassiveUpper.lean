import OracleBounds.GeneralPrior.Passive
import OracleBounds.GeneralPrior.MembershipTight

/-!
# The passive venue's sequential membership test (airlock draft v11.1, Corollary 4.2.5)

**UNSIGNED: the statements in this file have not been signed off by the administrator.**

A venue holding a candidate template `c` cannot choose its probes: it only watches the arrivals
that the day brings. It runs Wald's test (Theorem 4.2.3 = `GeneralPrior.Gallery.sprt_membership`)
on the arrivals that *reach* `c` (`⟨x, c⟩ > thr`) and ignores the rest.

The reduction to the SPRT is justified by `reaching_resp`/`nonreaching_resp` below: at the
symmetric-flip kernel (`κ = ρ` at or below `thr`, `1 − ρ` above),

* a *reaching* arrival answers `Bern(1−ρ)` under `H₁` (c enrolled) and `Bern(ρ)` under `H₀`
  provided it does not collide with an enrolled face — so reaching arrivals are exactly the
  i.i.d. trials at `c` of Theorem 4.2.3;
* a *non-reaching* arrival has the **same** response law under `H₀` and `H₁` — it carries no
  information, so ignoring it is free.

`pval` is therefore the model: each arrival reaches `c` with probability `μ` independently of the
past (`μ = μ_pop`, the false-accept mass of `c`'s template over the venue's footfall); a reaching
arrival answers `true` with probability `p`; a non-reaching arrival is recorded as `none`. The
venue stops observing once the test leaves `(−A, A)`, so the arrival counter `N` counts exactly
"the arrivals before a decision".

Results (`passive_sprt`, and `passive_sprt_delta` at `A = log(2/δ)`), with
`ℓ = log((1−ρ)/ρ)` and `KL_ρ = (1−2ρ)ℓ`:

* `E⁰[N], E¹[N] ≤ (A + ℓ)/(KL_ρ·μ)` — two Wald identities: `Λ − d·S` and `S − μ·N` are both
  martingales, so `E[Λ] = d·μ·E[N]` with `|d| = KL_ρ`, and `|Λ| < A + ℓ` always (overshoot);
* `δ_I ≤ e^{−A}`, `δ_II ≤ e^{−A} + (A+ℓ)/(KL_ρ·μ·Q)` (change of measure; the last term is the
  truncation at a budget of `Q` arrivals).

At `μ = 1` this is Theorem 4.2.3 itself: "each visit by the target counts one".

`passive_tight` puts the upper bound beside the passive lower bound
`GeneralPrior.Gallery.passive_population` (Corollary 2.7.1′): `log(1/2δ)/(KL_ρ·μ) ≤ Q` against
`E[N] ≤ (log(2/δ) + ℓ)/(KL_ρ·μ)`.

**Caveats, for the administrator's statement review.**

1. `passive_sprt`/`passive_sprt_delta` live in the abstract `pval` model, not in `Gallery`.
   `reaching_resp`/`nonreaching_resp` justify the reduction pointwise, but there is **no** Lean
   theorem here identifying the venue's transcript law on a `Gallery` with the `pval` law; the
   i.i.d. structure of the arrivals ("each arrival reaches `c` with probability `μ_pop`",
   independently of the past — what the note's appeal to Wald's identity needs) is built into
   `pval` by fiat.
2. **No collision term.** Under `H₀` the response probability is taken to be exactly `ρ` at every
   reaching arrival. By `reaching_resp` that is right only when the arrival does not itself
   reach an enrolled face. The note says "with the errors of Theorem 4.2.3", i.e. `δ_I ≤ δ/2 +
   n·μ₁`; but Theorem 4.2.3 probes only at `c`, so its collision event is a single event of
   probability `≤ n·μ₁`, whereas a passive venue draws a *fresh* arrival each round and the
   collision term should be of order `E[τ]·n·μ₁` — one chance per reaching arrival. That term is
   not formalised here, in either form.
3. `N` is truncated at the budget of `Q` arrivals, so the first two conjuncts bound `E[N ∧ Q]`.
   The bound is uniform in `Q`, so the note's untruncated `E[N]` follows by monotone convergence
   — not formalised.
4. "each visit by the target counts one" is the instance `μ = 1`; a mixed model (some rounds with
   `μ = 1`, the rest with `μ = μ_pop`) is not formalised.
5. "the ratio tends to 1" is not formalised as a limit; `passive_tight` states both sides, as
   `GeneralPrior.Gallery.membership_tight` does for Corollary 4.2.4.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.Attacks

open Finset OracleBounds.V6 OracleBounds.GeneralPrior

/-! ## The passive arrival process -/

/-- What the venue records about one arrival: `none` = it did not reach the candidate (its answer
carries no information about membership and is ignored); `some b` = it reached, and the oracle
answered `b`. -/
abbrev Obs := Option Bool

/-- Expectation of `F` over the next `r` arrivals from history `h`. The arrival reaches the
candidate with probability `m h` and, if it does, answers `true` with probability `p h`. -/
noncomputable def pval (m p : List Obs → ℝ) (F : List Obs → ℝ) : ℕ → List Obs → ℝ
  | 0, h => F h
  | r + 1, h => (1 - m h) * pval m p F r (h ++ [none]) +
      m h * (p h * pval m p F r (h ++ [some true]) +
        (1 - p h) * pval m p F r (h ++ [some false]))

section basic

variable (m p : List Obs → ℝ)

@[simp] lemma pval_zero (F : List Obs → ℝ) (h : List Obs) : pval m p F 0 h = F h := rfl

lemma pval_succ (F : List Obs → ℝ) (r : ℕ) (h : List Obs) :
    pval m p F (r + 1) h = (1 - m h) * pval m p F r (h ++ [none]) +
      m h * (p h * pval m p F r (h ++ [some true]) +
        (1 - p h) * pval m p F r (h ++ [some false])) := rfl

/-- `pval` is affine in the leaf function. -/
lemma pval_affine (a b : ℝ) (F : List Obs → ℝ) :
    ∀ r h, pval m p (fun h' => a + b * F h') r h = a + b * pval m p F r h := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih => intro h; simp only [pval_succ, ih]; ring

lemma pval_const (c : ℝ) : ∀ r h, pval m p (fun _ => c) r h = c := by
  intro r h
  simpa using pval_affine m p c 0 (fun _ => 0) r h

lemma pval_add (F G : List Obs → ℝ) :
    ∀ r h, pval m p (fun h' => F h' + G h') r h = pval m p F r h + pval m p G r h := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih => intro h; simp only [pval_succ, ih]; ring

variable {m p}

/-- Monotonicity; only leaves reachable from `h` in `r` rounds matter. -/
lemma pval_mono (hm : ∀ h, 0 ≤ m h ∧ m h ≤ 1) (hp : ∀ h, 0 ≤ p h ∧ p h ≤ 1)
    {F G : List Obs → ℝ} :
    ∀ r h, (∀ h', h'.length = h.length + r → F h' ≤ G h') →
      pval m p F r h ≤ pval m p G r h := by
  intro r
  induction r with
  | zero => intro h hFG; exact hFG h (by simp)
  | succ r ih =>
    intro h hFG
    have hn := ih (h ++ [none]) (fun h' hl => hFG h' (by simp at hl; omega))
    have ht := ih (h ++ [some true]) (fun h' hl => hFG h' (by simp at hl; omega))
    have hf := ih (h ++ [some false]) (fun h' hl => hFG h' (by simp at hl; omega))
    simp only [pval_succ]
    have h0 := (hm h).1
    have h1 : 0 ≤ 1 - m h := by linarith [(hm h).2]
    have hp0 := (hp h).1
    have hp1 : 0 ≤ 1 - p h := by linarith [(hp h).2]
    have : p h * pval m p F r (h ++ [some true]) + (1 - p h) * pval m p F r (h ++ [some false]) ≤
        p h * pval m p G r (h ++ [some true]) + (1 - p h) * pval m p G r (h ++ [some false]) :=
      add_le_add (mul_le_mul_of_nonneg_left ht hp0) (mul_le_mul_of_nonneg_left hf hp1)
    exact add_le_add (mul_le_mul_of_nonneg_left hn h1) (mul_le_mul_of_nonneg_left this h0)

end basic

/-! ## The test's state -/

/-- One step of the passive SPRT on the state `(Λ, S, N)`: the log-likelihood ratio, the number of
*reaching* arrivals used, and the number of arrivals observed. The state freezes as soon as
`|Λ| ≥ A` — the venue has decided and stops watching. -/
noncomputable def pStep (ℓ A : ℝ) (st : ℝ × ℕ × ℕ) (o : Obs) : ℝ × ℕ × ℕ :=
  if |st.1| < A then
    match o with
    | none => (st.1, st.2.1, st.2.2 + 1)
    | some b => (st.1 + (if b then ℓ else -ℓ), st.2.1 + 1, st.2.2 + 1)
  else st

lemma pStep_none (ℓ A : ℝ) (st : ℝ × ℕ × ℕ) :
    pStep ℓ A st none = if |st.1| < A then (st.1, st.2.1, st.2.2 + 1) else st := rfl

lemma pStep_some (ℓ A : ℝ) (st : ℝ × ℕ × ℕ) (b : Bool) :
    pStep ℓ A st (some b) =
      if |st.1| < A then (st.1 + (if b then ℓ else -ℓ), st.2.1 + 1, st.2.2 + 1) else st := rfl

/-- The state after the observed history `h`. -/
noncomputable def pState (ℓ A : ℝ) (h : List Obs) : ℝ × ℕ × ℕ := h.foldl (pStep ℓ A) (0, 0, 0)

/-- Reach probability of the next arrival: `μ` while the venue is still watching, `0` once it has
decided (it stops observing, so `N` counts the arrivals *before the decision*). -/
noncomputable def pReach (μ ℓ A : ℝ) (h : List Obs) : ℝ :=
  if |(pState ℓ A h).1| < A then μ else 0

/-- The venue's decision: "enrolled" iff `Λ ≥ A`. -/
noncomputable def pDecide (ℓ A : ℝ) (h : List Obs) : ℝ :=
  if A ≤ (pState ℓ A h).1 then 1 else 0

@[simp] lemma pState_nil (ℓ A : ℝ) : pState ℓ A [] = (0, 0, 0) := rfl

lemma pState_append (ℓ A : ℝ) (h : List Obs) (o : Obs) :
    pState ℓ A (h ++ [o]) = pStep ℓ A (pState ℓ A h) o := by
  simp [pState, List.foldl_append]

/-- Once `|Λ| ≥ A` the state is frozen. -/
lemma pFrozen (ℓ A : ℝ) (l : List Obs) (st : ℝ × ℕ × ℕ) (hst : ¬ |st.1| < A) :
    l.foldl (pStep ℓ A) st = st := by
  induction l with
  | nil => rfl
  | cons o t ih =>
    rw [List.foldl_cons, show pStep ℓ A st o = st by cases o <;> simp [pStep_none, pStep_some, hst]]
    exact ih

/-- If the final `|Λ| < A` the venue never stopped, so it observed every arrival. -/
lemma pFoldl_count (ℓ A : ℝ) (l : List Obs) : ∀ st : ℝ × ℕ × ℕ,
    |(l.foldl (pStep ℓ A) st).1| < A → (l.foldl (pStep ℓ A) st).2.2 = st.2.2 + l.length := by
  induction l with
  | nil => intro st _; simp
  | cons o t ih =>
    intro st hlt
    rw [List.foldl_cons] at hlt ⊢
    by_cases hst : |st.1| < A
    · rw [ih _ hlt]
      cases o <;> simp [pStep_none, pStep_some, hst] <;> omega
    · exfalso
      rw [show pStep ℓ A st o = st by cases o <;> simp [pStep_none, pStep_some, hst],
        pFrozen ℓ A t st hst] at hlt
      exact hst hlt

lemma pState_count (ℓ A : ℝ) (h : List Obs) (hlt : |(pState ℓ A h).1| < A) :
    (pState ℓ A h).2.2 = h.length :=
  (pFoldl_count ℓ A h (0, 0, 0) hlt).trans (by simp)

/-- Overshoot: `|Λ| < A + ℓ` is invariant. -/
lemma pFoldl_bound (ℓ A : ℝ) (hℓ : 0 ≤ ℓ) (l : List Obs) : ∀ st : ℝ × ℕ × ℕ,
    |st.1| < A + ℓ → |(l.foldl (pStep ℓ A) st).1| < A + ℓ := by
  induction l with
  | nil => intro st h; simpa using h
  | cons o t ih =>
    intro st hst
    rw [List.foldl_cons]
    apply ih
    by_cases h1 : |st.1| < A
    · cases o with
      | none => simpa [pStep_none, h1] using hst
      | some b =>
        rw [pStep_some, if_pos h1]
        have habs : |(if b then ℓ else -ℓ)| = ℓ := by cases b <;> simp [abs_of_nonneg hℓ]
        calc |st.1 + (if b then ℓ else -ℓ)| ≤ |st.1| + |(if b then ℓ else -ℓ)| := abs_add_le _ _
          _ < A + ℓ := by rw [habs]; linarith
    · rw [show pStep ℓ A st o = st by cases o <;> simp [pStep_none, pStep_some, h1]]; exact hst

lemma pState_bound (ℓ A : ℝ) (hℓ : 0 ≤ ℓ) (hA : 0 < A) (h : List Obs) :
    |(pState ℓ A h).1| < A + ℓ :=
  pFoldl_bound ℓ A hℓ h (0, 0, 0) (by simp; linarith)

/-! ## Two Wald identities -/

/-- **Wald's identity for the log-likelihood ratio.** `Λ − d·S` is a martingale, where `S` counts
the *reaching* arrivals and `d = pℓ − (1−p)ℓ` is the per-reaching-arrival drift. -/
lemma pval_wald (ℓ A μ p d : ℝ) (hd : d = p * ℓ - (1 - p) * ℓ) :
    ∀ r h, pval (pReach μ ℓ A) (fun _ => p)
      (fun h' => (pState ℓ A h').1 - d * ((pState ℓ A h').2.1 : ℝ)) r h
      = (pState ℓ A h).1 - d * ((pState ℓ A h).2.1 : ℝ) := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    rw [pval_succ, ih, ih, ih, pState_append, pState_append, pState_append]
    unfold pReach
    by_cases hA : |(pState ℓ A h).1| < A
    · rw [if_pos hA, pStep_none, pStep_some, pStep_some, if_pos hA, if_pos hA, if_pos hA]
      simp only [if_true, Bool.false_eq_true, if_false, Nat.cast_add, Nat.cast_one]
      rw [hd]; ring
    · rw [if_neg hA, pStep_none, if_neg hA]; ring

/-- **Wald's identity for the arrivals.** `S − μ·N` is a martingale: each arrival observed is a
reaching one with probability `μ`, so collecting `S` reaching arrivals costs `S/μ` arrivals. -/
lemma pval_arrivals (ℓ A μ p : ℝ) :
    ∀ r h, pval (pReach μ ℓ A) (fun _ => p)
      (fun h' => ((pState ℓ A h').2.1 : ℝ) - μ * ((pState ℓ A h').2.2 : ℝ)) r h
      = ((pState ℓ A h).2.1 : ℝ) - μ * ((pState ℓ A h).2.2 : ℝ) := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    rw [pval_succ, ih, ih, ih, pState_append, pState_append, pState_append]
    unfold pReach
    by_cases hA : |(pState ℓ A h).1| < A
    · rw [if_pos hA, pStep_none, pStep_some, pStep_some, if_pos hA, if_pos hA, if_pos hA]
      push_cast; ring
    · rw [if_neg hA, pStep_none, if_neg hA]; ring

/-! ## Change of measure -/

/-- Along the passive SPRT the likelihood ratio between the two response levels `a₀`, `a₁` is
`exp(θ·ΔΛ)`; the arrival process is the same under both, and contributes nothing. -/
lemma pval_change (ℓ A μ θ a0 a1 : ℝ) (φ : ℝ × ℕ × ℕ → ℝ)
    (ht : a1 * Real.exp (θ * ℓ) = a0) (hf : (1 - a1) * Real.exp (-(θ * ℓ)) = 1 - a0) :
    ∀ r h, pval (pReach μ ℓ A) (fun _ => a0) (fun h' => φ (pState ℓ A h')) r h =
      pval (pReach μ ℓ A) (fun _ => a1)
        (fun h' => φ (pState ℓ A h') *
          Real.exp (θ * ((pState ℓ A h').1 - (pState ℓ A h).1))) r h := by
  intro r
  induction r with
  | zero => intro h; simp
  | succ r ih =>
    intro h
    have key : ∀ (k : ℝ) (h₀ : List Obs),
        pval (pReach μ ℓ A) (fun _ => a1)
          (fun h' => φ (pState ℓ A h') * Real.exp (θ * ((pState ℓ A h').1 - k))) r h₀ =
        Real.exp (θ * ((pState ℓ A h₀).1 - k)) * pval (pReach μ ℓ A) (fun _ => a1)
          (fun h' => φ (pState ℓ A h') *
            Real.exp (θ * ((pState ℓ A h').1 - (pState ℓ A h₀).1))) r h₀ := by
      intro k h₀
      rw [← zero_add (Real.exp _ * _), ← pval_affine]
      congr 1
      funext h'
      rw [show θ * ((pState ℓ A h').1 - k) = θ * ((pState ℓ A h₀).1 - k) +
        θ * ((pState ℓ A h').1 - (pState ℓ A h₀).1) by ring, Real.exp_add]
      ring
    rw [pval_succ, pval_succ, ih, ih, ih, key (pState ℓ A h).1 (h ++ [none]),
      key (pState ℓ A h).1 (h ++ [some true]), key (pState ℓ A h).1 (h ++ [some false])]
    set Vn := pval (pReach μ ℓ A) (fun _ => a1) (fun h' => φ (pState ℓ A h') *
      Real.exp (θ * ((pState ℓ A h').1 - (pState ℓ A (h ++ [none])).1))) r (h ++ [none]) with hVn
    set Vt := pval (pReach μ ℓ A) (fun _ => a1) (fun h' => φ (pState ℓ A h') *
      Real.exp (θ * ((pState ℓ A h').1 - (pState ℓ A (h ++ [some true])).1))) r (h ++ [some true])
    set Vf := pval (pReach μ ℓ A) (fun _ => a1) (fun h' => φ (pState ℓ A h') *
      Real.exp (θ * ((pState ℓ A h').1 - (pState ℓ A (h ++ [some false])).1))) r (h ++ [some false])
    rw [pState_append, pState_append, pState_append]
    unfold pReach
    by_cases hA : |(pState ℓ A h).1| < A
    · rw [if_pos hA, pStep_none, pStep_some, pStep_some, if_pos hA, if_pos hA, if_pos hA]
      simp only [if_true, Bool.false_eq_true, if_false]
      rw [show θ * ((pState ℓ A h).1 - (pState ℓ A h).1) = 0 by ring, Real.exp_zero,
        show θ * ((pState ℓ A h).1 + ℓ - (pState ℓ A h).1) = θ * ℓ by ring,
        show θ * ((pState ℓ A h).1 + -ℓ - (pState ℓ A h).1) = -(θ * ℓ) by ring, ← hf, ← ht]
      ring
    · rw [if_neg hA, pStep_none, if_neg hA]
      rw [show θ * ((pState ℓ A h).1 - (pState ℓ A h).1) = 0 by ring, Real.exp_zero]
      ring

/-! ## Why the passive venue may ignore the non-reaching arrivals

These two lemmas justify the `pval` model against the real oracle of
`OracleBounds.GeneralPrior.Gallery` at the symmetric-flip kernel. -/

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [Fintype Fine]

/-- A **reaching** arrival is an i.i.d. trial at the candidate: it answers `Bern(1−ρ)` under
`H₁` (`c` enrolled) and `Bern(ρ)` under `H₀`, unless it collides with an enrolled face. -/
lemma reaching_resp (G : Gallery E ι Fine) [Nonempty ι] (V : ι → Fine) (c : E) (ρ : ℝ)
    (hκq : ∀ s ≤ G.thr, G.κ s = ρ) (hκl : ∀ s, G.thr < s → G.κ s = 1 - ρ)
    (x : Sph E) (hx : G.reachC c x) :
    G.respWith V c x = 1 - ρ ∧ (G.score V x ≤ G.thr → G.resp V x = ρ) :=
  ⟨hκl _ (lt_of_lt_of_le hx (le_max_right _ _)), fun hs => hκq _ hs⟩

/-- A **non-reaching** arrival has the same response law under `H₀` and under `H₁`: it carries no
information about membership, so the venue loses nothing by ignoring it. -/
lemma nonreaching_resp (G : Gallery E ι Fine) [Nonempty ι] (V : ι → Fine) (c : E) (ρ : ℝ)
    (hκq : ∀ s ≤ G.thr, G.κ s = ρ) (hκl : ∀ s, G.thr < s → G.κ s = 1 - ρ)
    (x : Sph E) (hx : ¬ G.reachC c x) : G.resp V x = G.respWith V c x := by
  unfold Gallery.resp Gallery.respWith
  unfold Gallery.reachC at hx
  push Not at hx
  by_cases hs : G.score V x ≤ G.thr
  · rw [hκq _ hs, hκq _ (max_le hs hx)]
  · push Not at hs
    rw [hκl _ hs, hκl _ (lt_of_lt_of_le hs (le_max_left _ _))]

end Bridge

/-! ## Corollary 4.2.5 -/

open Classical in
/-- **Corollary 4.2.5 (passive venue).** A venue holding `c` runs the test of Theorem 4.2.3 on the
arrivals that reach `c` and ignores the rest. With each arrival reaching `c` with probability `μ`
(`= μ_pop`) independently of the past, and with `ℓ = log((1−ρ)/ρ)`, `KL_ρ = (1−2ρ)ℓ`:

* the expected number of arrivals observed before a decision is at most `(A + ℓ)/(KL_ρ·μ)`, under
  `H₀` (first conjunct) and under `H₁` (second);
* the errors are those of Theorem 4.2.3: `δ_I ≤ e^{−A}` and
  `δ_II ≤ e^{−A} + (A + ℓ)/(KL_ρ·μ·Q)` at a budget of `Q` arrivals.

At `μ = 1` (the target visits every round) this is Theorem 4.2.3 itself: each visit counts one. -/
theorem passive_sprt (ρ μ A : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (hA : 0 < A) (Q : ℕ) (hQ : 1 ≤ Q) :
    pval (pReach μ (Real.log ((1 - ρ) / ρ)) A) (fun _ => ρ)
        (fun h => ((pState (Real.log ((1 - ρ) / ρ)) A h).2.2 : ℝ)) Q [] ≤
      (A + Real.log ((1 - ρ) / ρ)) / ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * μ) ∧
    pval (pReach μ (Real.log ((1 - ρ) / ρ)) A) (fun _ => 1 - ρ)
        (fun h => ((pState (Real.log ((1 - ρ) / ρ)) A h).2.2 : ℝ)) Q [] ≤
      (A + Real.log ((1 - ρ) / ρ)) / ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * μ) ∧
    pval (pReach μ (Real.log ((1 - ρ) / ρ)) A) (fun _ => ρ)
        (pDecide (Real.log ((1 - ρ) / ρ)) A) Q [] ≤ Real.exp (-A) ∧
    pval (pReach μ (Real.log ((1 - ρ) / ρ)) A) (fun _ => 1 - ρ)
        (fun h => 1 - pDecide (Real.log ((1 - ρ) / ρ)) A h) Q [] ≤
      Real.exp (-A) + (A + Real.log ((1 - ρ) / ρ)) /
        ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * μ * Q) := by
  set ℓ := Real.log ((1 - ρ) / ρ) with hℓdef
  have hρ1' : 0 < 1 - ρ := by linarith
  have hratio : 1 < (1 - ρ) / ρ := by rw [lt_div_iff₀ hρ0]; linarith
  have hℓ : 0 < ℓ := Real.log_pos hratio
  have hexp : Real.exp ℓ = (1 - ρ) / ρ := Real.exp_log (by positivity)
  have hexpn : Real.exp (-ℓ) = ρ / (1 - ρ) := by rw [Real.exp_neg, hexp, inv_div]
  have hKL : 0 < (1 - 2 * ρ) * ℓ := mul_pos (by linarith) hℓ
  have hKLμ : 0 < (1 - 2 * ρ) * ℓ * μ := mul_pos hKL hμ0
  have hm : ∀ h, 0 ≤ pReach μ ℓ A h ∧ pReach μ ℓ A h ≤ 1 := by
    intro h; unfold pReach; split_ifs <;> exact ⟨by linarith, by linarith⟩
  -- the expected number of arrivals, under either hypothesis
  have hEN : ∀ p : ℝ, 0 ≤ p → p ≤ 1 → (p = ρ ∨ p = 1 - ρ) →
      pval (pReach μ ℓ A) (fun _ => p) (fun h => ((pState ℓ A h).2.2 : ℝ)) Q [] ≤
        (A + ℓ) / ((1 - 2 * ρ) * ℓ * μ) := by
    intro p hp0 hp1 hpc
    have hp : ∀ _h : List Obs, 0 ≤ p ∧ p ≤ 1 := fun _ => ⟨hp0, hp1⟩
    set d := p * ℓ - (1 - p) * ℓ with hd
    -- Wald I: `Λ − d·S` is a martingale
    have hw := pval_wald ℓ A μ p d hd Q []
    have e1 := pval_add (pReach μ ℓ A) (fun _ => p) (fun h => (pState ℓ A h).1)
      (fun h => 0 + (-d) * ((pState ℓ A h).2.1 : ℝ)) Q []
    rw [pval_affine] at e1
    have e1' : pval (pReach μ ℓ A) (fun _ => p)
        (fun h => (pState ℓ A h).1 - d * ((pState ℓ A h).2.1 : ℝ)) Q [] =
        pval (pReach μ ℓ A) (fun _ => p)
        (fun h => (pState ℓ A h).1 + (0 + (-d) * ((pState ℓ A h).2.1 : ℝ))) Q [] := by
      congr 1; funext h; ring
    rw [e1', e1] at hw
    -- Wald II: `S − μ·N` is a martingale
    have ha := pval_arrivals ℓ A μ p Q []
    have e2 := pval_add (pReach μ ℓ A) (fun _ => p) (fun h => ((pState ℓ A h).2.1 : ℝ))
      (fun h => 0 + (-μ) * ((pState ℓ A h).2.2 : ℝ)) Q []
    rw [pval_affine] at e2
    have e2' : pval (pReach μ ℓ A) (fun _ => p)
        (fun h => ((pState ℓ A h).2.1 : ℝ) - μ * ((pState ℓ A h).2.2 : ℝ)) Q [] =
        pval (pReach μ ℓ A) (fun _ => p)
        (fun h => ((pState ℓ A h).2.1 : ℝ) + (0 + (-μ) * ((pState ℓ A h).2.2 : ℝ))) Q [] := by
      congr 1; funext h; ring
    rw [e2', e2] at ha
    simp only [pState_nil, Nat.cast_zero, mul_zero, sub_zero] at hw ha
    -- overshoot bounds on `Λ`
    have hlo : -(A + ℓ) ≤ pval (pReach μ ℓ A) (fun _ => p) (fun h => (pState ℓ A h).1) Q [] := by
      have := pval_mono hm hp (F := fun _ => -(A + ℓ)) (G := fun h => (pState ℓ A h).1) Q []
        (fun h' _ => (abs_lt.1 (pState_bound ℓ A hℓ.le hA h')).1.le)
      rwa [pval_const] at this
    have hhi : pval (pReach μ ℓ A) (fun _ => p) (fun h => (pState ℓ A h).1) Q [] ≤ A + ℓ := by
      have := pval_mono hm hp (G := fun _ => (A + ℓ)) (F := fun h => (pState ℓ A h).1) Q []
        (fun h' _ => (abs_lt.1 (pState_bound ℓ A hℓ.le hA h')).2.le)
      rwa [pval_const] at this
    set W := pval (pReach μ ℓ A) (fun _ => p) (fun h => (pState ℓ A h).1) Q [] with hWdef
    set Sv := pval (pReach μ ℓ A) (fun _ => p) (fun h => ((pState ℓ A h).2.1 : ℝ)) Q [] with hSdef
    set Nv := pval (pReach μ ℓ A) (fun _ => p) (fun h => ((pState ℓ A h).2.2 : ℝ)) Q [] with hNdef
    have hSv : Sv = μ * Nv := by linarith
    have hW : W = d * (μ * Nv) := by rw [show W = d * Sv by linarith, hSv]
    rw [le_div_iff₀ hKLμ]
    rcases hpc with h | h
    · have hdv : d = -((1 - 2 * ρ) * ℓ) := by rw [hd, h]; ring
      rw [hdv] at hW
      have : Nv * ((1 - 2 * ρ) * ℓ * μ) = -W := by rw [hW]; ring
      rw [this]; linarith
    · have hdv : d = (1 - 2 * ρ) * ℓ := by rw [hd, h]; ring
      rw [hdv] at hW
      have : Nv * ((1 - 2 * ρ) * ℓ * μ) = W := by rw [hW]; ring
      rw [this]; linarith
  have hEN1 := hEN (1 - ρ) (by linarith) (by linarith) (Or.inr rfl)
  refine ⟨hEN ρ hρ0.le (by linarith) (Or.inl rfl), hEN1, ?_, ?_⟩
  · -- type I error, by change of measure (θ = −1)
    have hp1 : ∀ _h : List Obs, (0 : ℝ) ≤ 1 - ρ ∧ (1 : ℝ) - ρ ≤ 1 := fun _ =>
      ⟨by linarith, by linarith⟩
    have hcm := pval_change ℓ A μ (-1) ρ (1 - ρ) (fun st => if A ≤ st.1 then (1 : ℝ) else 0)
      (by rw [show (-1 : ℝ) * ℓ = -ℓ by ring, hexpn]; field_simp)
      (by rw [show -((-1 : ℝ) * ℓ) = ℓ by ring, hexp]; field_simp; ring) Q []
    rw [show pDecide ℓ A = fun h => (fun st : ℝ × ℕ × ℕ => if A ≤ st.1 then (1 : ℝ) else 0)
      (pState ℓ A h) from rfl, hcm]
    have := pval_mono hm hp1 (G := fun _ => Real.exp (-A))
      (F := fun h' => (if A ≤ (pState ℓ A h').1 then (1 : ℝ) else 0) *
        Real.exp (-1 * ((pState ℓ A h').1 - (pState ℓ A []).1))) Q []
      (fun h' _ => by
        rw [pState_nil]
        split_ifs with hge
        · rw [one_mul]; apply Real.exp_le_exp.2; simp; linarith
        · rw [zero_mul]; exact (Real.exp_pos _).le)
    rwa [pval_const] at this
  · -- type II error: either `Λ ≤ −A` (change of measure, θ = 1) or the test never stopped
    have hp1 : ∀ _h : List Obs, (0 : ℝ) ≤ 1 - ρ ∧ (1 : ℝ) - ρ ≤ 1 := fun _ =>
      ⟨by linarith, by linarith⟩
    have hpr : ∀ _h : List Obs, (0 : ℝ) ≤ ρ ∧ ρ ≤ 1 := fun _ => ⟨hρ0.le, by linarith⟩
    have hcm := pval_change ℓ A μ 1 (1 - ρ) ρ (fun st => if st.1 ≤ -A then (1 : ℝ) else 0)
      (by rw [one_mul, hexp]; field_simp)
      (by rw [show -((1 : ℝ) * ℓ) = -ℓ by ring, hexpn]; field_simp; ring) Q []
    have hL : pval (pReach μ ℓ A) (fun _ => 1 - ρ)
        (fun h => if (pState ℓ A h).1 ≤ -A then (1 : ℝ) else 0) Q [] ≤ Real.exp (-A) := by
      rw [show (fun h => if (pState ℓ A h).1 ≤ -A then (1 : ℝ) else 0) =
        fun h => (fun st : ℝ × ℕ × ℕ => if st.1 ≤ -A then (1 : ℝ) else 0) (pState ℓ A h) from rfl,
        hcm]
      have := pval_mono hm hpr (G := fun _ => Real.exp (-A))
        (F := fun h' => (if (pState ℓ A h').1 ≤ -A then (1 : ℝ) else 0) *
          Real.exp (1 * ((pState ℓ A h').1 - (pState ℓ A []).1))) Q []
        (fun h' _ => by
          rw [pState_nil]
          split_ifs with hle
          · rw [one_mul]; apply Real.exp_le_exp.2; simp; linarith
          · rw [zero_mul]; exact (Real.exp_pos _).le)
      rwa [pval_const] at this
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
    calc pval (pReach μ ℓ A) (fun _ => 1 - ρ) (fun h => 1 - pDecide ℓ A h) Q []
        ≤ pval (pReach μ ℓ A) (fun _ => 1 - ρ)
            (fun h => (if (pState ℓ A h).1 ≤ -A then (1 : ℝ) else 0) +
              (0 + (1 / (Q : ℝ)) * ((pState ℓ A h).2.2 : ℝ))) Q [] := by
          refine pval_mono hm hp1 Q [] ?_
          intro h' hl
          simp only [List.length_nil, zero_add] at hl
          have hS0 : (0 : ℝ) ≤ (1 / (Q : ℝ)) * ((pState ℓ A h').2.2 : ℝ) := by positivity
          unfold pDecide
          by_cases hge : A ≤ (pState ℓ A h').1
          · rw [if_pos hge]; split_ifs <;> linarith
          · rw [if_neg hge]
            by_cases hle : (pState ℓ A h').1 ≤ -A
            · rw [if_pos hle]; linarith
            · rw [if_neg hle]
              push Not at hge hle
              have habs : |(pState ℓ A h').1| < A := abs_lt.2 ⟨hle, hge⟩
              rw [pState_count ℓ A h' habs, hl]
              field_simp
              norm_num
      _ = pval (pReach μ ℓ A) (fun _ => 1 - ρ)
            (fun h => if (pState ℓ A h).1 ≤ -A then (1 : ℝ) else 0) Q [] +
            (0 + (1 / (Q : ℝ)) * pval (pReach μ ℓ A) (fun _ => 1 - ρ)
              (fun h => ((pState ℓ A h).2.2 : ℝ)) Q []) := by
          rw [pval_add, pval_affine]
      _ ≤ Real.exp (-A) + (0 + (1 / (Q : ℝ)) * ((A + ℓ) / ((1 - 2 * ρ) * ℓ * μ))) := by
          gcongr
      _ = Real.exp (-A) + (A + ℓ) / ((1 - 2 * ρ) * ℓ * μ * Q) := by
          rw [zero_add, one_div_mul_eq_div, div_div]

open Classical in
/-- **Corollary 4.2.5 at `A = log(2/δ)`.** The expected number of arrivals before a decision is at
most `(log(2/δ) + ℓ)/(KL_ρ·μ_pop)`, with `δ_I ≤ δ/2` and `δ_II ≤ δ/2 + (log(2/δ)+ℓ)/(KL_ρ·μ·Q)`
— the errors of Theorem 4.2.3. -/
theorem passive_sprt_delta (ρ μ δ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (Q : ℕ) (hQ : 1 ≤ Q) :
    pval (pReach μ (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ))) (fun _ => ρ)
        (fun h => ((pState (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ)) h).2.2 : ℝ)) Q [] ≤
      (Real.log (2 / δ) + Real.log ((1 - ρ) / ρ)) /
        ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * μ) ∧
    pval (pReach μ (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ))) (fun _ => 1 - ρ)
        (fun h => ((pState (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ)) h).2.2 : ℝ)) Q [] ≤
      (Real.log (2 / δ) + Real.log ((1 - ρ) / ρ)) /
        ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * μ) ∧
    pval (pReach μ (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ))) (fun _ => ρ)
        (pDecide (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ))) Q [] ≤ δ / 2 ∧
    pval (pReach μ (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ))) (fun _ => 1 - ρ)
        (fun h => 1 - pDecide (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ)) h) Q [] ≤
      δ / 2 + (Real.log (2 / δ) + Real.log ((1 - ρ) / ρ)) /
        ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * μ * Q) := by
  have hA : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hexp : Real.exp (-Real.log (2 / δ)) = δ / 2 := by
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  obtain ⟨h1, h2, h3, h4⟩ := passive_sprt ρ μ (Real.log (2 / δ)) hρ0 hρ1 hμ0 hμ1 hA Q hQ
  rw [hexp] at h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-! ## Against the passive lower bound (Corollary 2.7.1′) -/

section Tight

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]
variable {U : Type*} [Fintype U]

open Classical in
/-- **The passive bound is tight** (Corollary 4.2.5's last sentence). The first conjunct is the
passive lower bound `GeneralPrior.Gallery.passive_population` (Corollary 2.7.1′) at `ζ = 0`:
*every* passive test with total error `≤ δ` must watch `Q ≥ log(1/2δ)/(KL_ρ·μ)` arrivals. The
rest is the passive SPRT, which watches `(log(2/δ) + ℓ)/(KL_ρ·μ)` arrivals in expectation and has
the errors of Theorem 4.2.3. The ratio of the two is
`(log(2/δ) + ℓ)/log(1/2δ) → 1` as `δ → 0`. -/
theorem passive_tight (G : Gallery E ι Fine) [Nonempty ι] [Nonempty Fine]
    (lam : U → ℝ) (hlam0 : ∀ u, 0 ≤ lam u) (hlam1 : ∑ u, lam u = 1)
    (c : Sph E) (D : U → List Bool → ℝ) (hD : ∀ u h, 0 ≤ D u h ∧ D u h ≤ 1)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hκq : ∀ s ≤ G.thr, G.κ s = ρ) (hκl : ∀ s, G.thr < s → G.κ s = 1 - ρ) (hζ0 : G.ζ = 0)
    (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Q : ℕ) (hQ : 1 ≤ Q) :
    -- every passive test with total error ≤ δ must watch this many arrivals …
    (∀ seq : U → ℕ → Sph E,
      (∀ k < Q, (∑ u, lam u * (if G.reachC c.1 (seq u k) then (1 : ℝ) else 0)) ≤ μ) →
      G.memErr lam c.1 D (Gallery.passiveProbe seq) Q ≤ δ →
      Real.log (1 / (2 * δ)) / ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * μ) ≤ Q) ∧
    -- … and the passive SPRT at `A = log(2/δ)` watches this many, with the errors of Thm 4.2.3
    (pval (pReach μ (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ))) (fun _ => ρ)
        (fun h => ((pState (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ)) h).2.2 : ℝ)) Q [] ≤
      (Real.log (2 / δ) + Real.log ((1 - ρ) / ρ)) /
        ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * μ) ∧
    pval (pReach μ (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ))) (fun _ => ρ)
        (pDecide (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ))) Q [] ≤ δ / 2 ∧
    pval (pReach μ (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ))) (fun _ => 1 - ρ)
        (fun h => 1 - pDecide (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ)) h) Q [] ≤
      δ / 2 + (Real.log (2 / δ) + Real.log ((1 - ρ) / ρ)) /
        ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * μ * Q)) := by
  have hrange : ∀ s, ρ ≤ G.κ s ∧ G.κ s ≤ 1 - ρ := fun s => by
    rcases le_or_gt s G.thr with h | h
    · rw [hκq s h]; constructor <;> linarith
    · rw [hκl s h]; constructor <;> linarith
  have hKL : 0 < (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) :=
    mul_pos (by linarith) (Real.log_pos (by rw [lt_div_iff₀ hρ0]; linarith))
  obtain ⟨h1, -, h3, h4⟩ := passive_sprt_delta ρ μ δ hρ0 hρ1 hμ0 hμ1 hδ0 hδ1 Q hQ
  refine ⟨fun seq hμseq herr => ?_, h1, h3, h4⟩
  have h := G.passive_population lam hlam0 hlam1 c.1 D c.2 hD ρ hρ0 hρ1 hrange (Or.inl hζ0)
    seq Q μ hμseq δ herr
  rw [hζ0] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    add_zero, sub_zero] at h
  rw [div_le_iff₀ (mul_pos hKL hμ0)]
  linarith

end Tight

end OracleBounds.Attacks
