import OracleBounds.GeneralPrior.Gallery

/-!
# The candidate sieve (Airlock technical note, Proposition 4.4.2), K1(ρ)

**Statements signed off by the administrator, 23 Sep 2026 (proof by subagent). Faithful to
technical note Proposition 4.4.2, with one recorded limitation: every bound is stated at a finite
horizon `T` (uniformly in `T`), so the note's untruncated `E[Q]` and its a.s. termination follow
by monotone convergence, which is NOT formalised; the error bound carries the explicit `+
costBound/T` truncation term.**

The sieve of Proposition 4.4.2: a `thr`-separated pool of `M` candidates contains the `n` enrolled
points.  The attacker keeps a log-likelihood ratio `λ_j ∈ ℓ_ρ ℤ` for each candidate (initially
`0`) and a confirmed set `C`; while `|C| < n` it probes the unconfirmed candidate with the largest
`λ_j` (ties by index), adds `± ℓ_ρ` to it as the answer is `1` or `0`, and confirms `j` once
`λ_j ≥ A`.

## Model

Everything is written in units of `ℓ_ρ`, so the log-likelihood ratios are integers `σ : Fin M → ℤ`
and the confirmation threshold is an integer `a` with `A ≤ a·ℓ_ρ ≤ A + ℓ_ρ` (take `a = ⌈A/ℓ_ρ⌉`).
The state `St M` carries, per candidate, its walk `σ j`, the running minimum `m j` of that walk,
and the number `N j` of probes it has received; `step`/`state` run the sieve along a transcript
and `probeIdx` is the resulting probe rule `List Bool → Fin M`.

Every expectation is `OracleBounds.V6.val`, the repo's adaptive one-bit process, so **adaptivity
is carried honestly by the transcript recursion**: the walks are *not* pre-sampled and no coupling
is assumed.  `resp_poolPt` derives the response law `pJ j = 1 − ρ` (listed) / `ρ` (unlisted)
from the K1(ρ) kernel and `thr`-separation, and `gallery_sieve` states the conclusions for the
real oracle `Gallery.resp`.

All bounds hold at every horizon `T` (the number of rounds), uniformly in `T`.  This is the honest
finitary form of the note's untruncated statements: `E[Q] = lim_T E[Q ∧ T]` and `P[Q = ∞] = 0`
follow from them by monotone convergence, which is not formalised here.

## What is proved — steps (a)–(f) of the note's proof, all six

* (a) **Greedy invariant**: `Inv` / `inv_state`.  The clause `∀ j ∉ L, −D* − 1 ≤ σ j`, with
  `D* = dstar L s = maxᵢ∈L (−minₖ σ_i(k))`, is proved by induction along the transcript from the
  argmax property of `pick` and the fact that some listed candidate is unconfirmed while
  `|C| < n` (`exists_listed_unconf`).
* (b) **Unlisted cost**: `sieve_unlisted_cost`, `(1−2ρ)·E[N_j(T)] ≤ E[D*] + 1`, from `wald_zero`
  applied to a walk of drift `−(1−2ρ)` together with (a).
* (c) **Listed cost**: `sieve_listed_cost`, `(1−2ρ)·E[N_i(T)] ≤ a`, from `wald_zero` and the
  invariant `σ_i ≤ a` (overshoot below one step).
* (d) **Depth**: `depth_tail`, `P[minₖ σ_i(k) ≤ −k] ≤ e^{−kℓ}`, proved from the *stopped*
  exponential supermartingale `depthW` (this is the gambler's-ruin/Ville bound, proved here, not
  assumed); `sieve_depth` sums the tail, `E[D*] ≤ log n/ℓ + (1−ρ)/(1−2ρ)`.
* (e) **Error**: `error_tail`, `P[σ_j(T) ≥ a] ≤ e^{−aℓ}` for unlisted `j`, from the *exact*
  mean-one martingale `errW = e^{ℓσ_j}` (an unlisted candidate is probed only while unconfirmed);
  `sieve_error` is the union bound `≤ (M−n)e^{−aℓ}`.
* (f) **Termination**: `sieve_not_halted`, `P[not terminated within T probes] ≤ costBound/T`
  (Markov on the cost bound, using `sumN_eq`: every round of a non-terminated run spends a probe).

Assembled:

* `sieve_cost`: `E[Q ∧ T] ≤ (M−n)(log n/KL_ρ + (2−3ρ)/(1−2ρ)²) + n(A/KL_ρ + 1/(1−2ρ))`
  (`= costBound M n ρ ℓ A`, `KL_ρ = (1−2ρ)ℓ_ρ`) — the note's display.
* `sieve_correct`: `P[C ≠ L] ≤ (M−n)e^{−aℓ} + costBound/T`.
* `sieve_prop442`: the same with `A = log((M−n)/δ)`, giving `P[C ≠ L] ≤ δ + costBound/T`.
* `gallery_sieve`: both, for the oracle `Gallery.resp v` on a `thr`-separated pool with the
  K1(ρ) kernel and an injective enrolled list.

Hypotheses (all explicit, none hidden): `0 < ρ < 1/2`, `exp ℓ = (1−ρ)/ρ` and `0 < ℓ`
(i.e. `ℓ = ℓ_ρ = log((1−ρ)/ρ)`), `L.card = n`, `0 < n ≤ M`, `0 ≤ a`, `A ≤ aℓ ≤ A + ℓ`, `0 < T`.
Nothing is assumed about martingale theory, optional stopping or Ville's inequality: the two
exponential (super)martingale facts are proved from the process recursion by `val_mart`/
`val_super`.

No `sorry`s, no new axioms.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.Attacks

open Finset OracleBounds.V6

namespace Sieve

variable {M : ℕ}

/-- The sieve's state: per candidate, its log-likelihood walk `σ` (in units of `ℓ_ρ`), the
running minimum `m` of that walk, and the number `N` of probes it has received. -/
structure St (M : ℕ) where
  /-- log-likelihood ratio of candidate `j`, in units of `ℓ_ρ` -/
  σ : Fin M → ℤ
  /-- running minimum of `σ j` -/
  m : Fin M → ℤ
  /-- number of probes spent on `j` -/
  N : Fin M → ℕ

/-- The initial state: all walks at `0`, no probes spent. -/
def St.init (M : ℕ) : St M := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- Unconfirmed candidates. -/
def unconf (a : ℤ) (s : St M) : Finset (Fin M) := univ.filter (fun j => s.σ j < a)

/-- Confirmed candidates: the sieve's output. -/
def conf (a : ℤ) (s : St M) : Finset (Fin M) := univ.filter (fun j => a ≤ s.σ j)

lemma mem_unconf {a : ℤ} {s : St M} {j : Fin M} : j ∈ unconf a s ↔ s.σ j < a := by
  simp [unconf]

lemma mem_conf {a : ℤ} {s : St M} {j : Fin M} : j ∈ conf a s ↔ a ≤ s.σ j := by
  simp [conf]

/-- The unconfirmed candidates of maximal `σ`. -/
def maxers (a : ℤ) (s : St M) : Finset (Fin M) :=
  (unconf a s).filter (fun j => ∀ i ∈ unconf a s, s.σ i ≤ s.σ j)

lemma maxers_nonempty {a : ℤ} {s : St M} (h : (unconf a s).Nonempty) :
    (maxers a s).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image (unconf a s) s.σ h
  exact ⟨x, by simp only [maxers, Finset.mem_filter]; exact ⟨hx, hmax⟩⟩

/-- The probed candidate: the unconfirmed one of largest `σ`, ties broken by index. -/
noncomputable def pick [NeZero M] (a : ℤ) (s : St M) : Fin M :=
  if h : (maxers a s).Nonempty then (maxers a s).min' h else (0 : Fin M)

lemma pick_mem [NeZero M] {a : ℤ} {s : St M} (h : (unconf a s).Nonempty) :
    pick a s ∈ maxers a s := by
  rw [pick, dif_pos (maxers_nonempty h)]
  exact Finset.min'_mem _ _

lemma pick_unconf [NeZero M] {a : ℤ} {s : St M} (h : (unconf a s).Nonempty) :
    pick a s ∈ unconf a s :=
  (Finset.mem_filter.1 (pick_mem h)).1

lemma pick_max [NeZero M] {a : ℤ} {s : St M} (h : (unconf a s).Nonempty)
    {i : Fin M} (hi : i ∈ unconf a s) : s.σ i ≤ s.σ (pick a s) :=
  (Finset.mem_filter.1 (pick_mem h)).2 i hi

/-- One round of the sieve: if `n` candidates are already confirmed the sieve has halted and the
state is frozen; otherwise the probed candidate's walk moves by `±1`. -/
noncomputable def step [NeZero M] (n : ℕ) (a : ℤ) (s : St M) (b : Bool) : St M :=
  if n ≤ (conf a s).card then s
  else
    { σ := Function.update s.σ (pick a s) (s.σ (pick a s) + (if b then 1 else -1)),
      m := Function.update s.m (pick a s)
        (min (s.m (pick a s)) (s.σ (pick a s) + (if b then 1 else -1))),
      N := Function.update s.N (pick a s) (s.N (pick a s) + 1) }

/-- The sieve's state after a transcript. -/
noncomputable def state [NeZero M] (n : ℕ) (a : ℤ) (h : List Bool) : St M :=
  h.foldl (step n a) (St.init M)

/-- The sieve as a probe rule on transcripts. -/
noncomputable def probeIdx [NeZero M] (n : ℕ) (a : ℤ) (h : List Bool) : Fin M :=
  pick a (state n a h)

lemma state_nil [NeZero M] (n : ℕ) (a : ℤ) : state n a ([] : List Bool) = St.init M := rfl

lemma state_append [NeZero M] (n : ℕ) (a : ℤ) (h : List Bool) (b : Bool) :
    state (M := M) n a (h ++ [b]) = step n a (state n a h) b := by
  simp [state, List.foldl_append]

section

variable [NeZero M] {n : ℕ} {a : ℤ}

lemma step_halted (s : St M) (b : Bool) (hh : n ≤ (conf a s).card) : step n a s b = s := by
  rw [step, if_pos hh]

lemma unconf_nonempty_of_not_halted (s : St M) (hn : n ≤ M) (hh : ¬ n ≤ (conf a s).card) :
    (unconf a s).Nonempty := by
  rw [← Finset.card_pos]
  have hdisj : Disjoint (conf a s) (unconf a s) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact absurd (mem_conf.1 hx) (not_le.2 (mem_unconf.1 hx'))
  have hunion : conf a s ∪ unconf a s = univ := by
    ext x
    simp only [Finset.mem_union, mem_conf, mem_unconf, Finset.mem_univ, iff_true]
    exact le_or_gt a (s.σ x)
  have : (conf a s).card + (unconf a s).card = M := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  omega

/-- A listed candidate is unconfirmed whenever the sieve has not halted. -/
lemma exists_listed_unconf (L : Finset (Fin M)) (hL : L.card = n) (s : St M)
    (hh : ¬ n ≤ (conf a s).card) : ∃ i ∈ L, i ∈ unconf a s := by
  by_contra hcon
  push Not at hcon
  have hsub : L ⊆ conf a s := by
    intro i hi
    have := hcon i hi
    rw [mem_conf]
    exact not_lt.1 (fun hlt => this (mem_unconf.2 hlt))
  exact hh (hL ▸ Finset.card_le_card hsub)

end

/-! ### The running depth `D*` -/

/-- `D* = maxᵢ (−minₖ σ_i(k))` over the listed candidates, as a natural number. -/
def dstar (L : Finset (Fin M)) (s : St M) : ℕ := L.sup (fun i => (s.m i).natAbs)

lemma le_dstar (L : Finset (Fin M)) (s : St M) {i : Fin M} (hi : i ∈ L) :
    (s.m i).natAbs ≤ dstar L s :=
  Finset.le_sup (f := fun i => (s.m i).natAbs) hi

lemma neg_dstar_le (L : Finset (Fin M)) (s : St M) {i : Fin M} (hi : i ∈ L) (h0 : s.m i ≤ 0) :
    -(dstar L s : ℤ) ≤ s.m i := by
  have := le_dstar L s hi
  omega

lemma lt_dstar_iff {L : Finset (Fin M)} {s : St M} {k : ℕ} :
    k < dstar L s ↔ ∃ i ∈ L, k < (s.m i).natAbs := Finset.lt_sup_iff

/-! ### The invariants (step (a) of the note's proof) -/

/-- The sieve's state invariants: walks stop at `a`, `m` is the running minimum and is `≤ 0`,
`m j ≥ −N j`, and the **greedy invariant**: an unlisted walk never falls below `−D* − 1`. -/
def Inv (a : ℤ) (L : Finset (Fin M)) (s : St M) : Prop :=
  (∀ j, s.σ j ≤ a) ∧ (∀ j, s.m j ≤ s.σ j) ∧ (∀ j, s.m j ≤ 0) ∧
  (∀ j, -(s.N j : ℤ) ≤ s.m j) ∧ (∀ j ∉ L, -(dstar L s : ℤ) - 1 ≤ s.σ j)

section

variable [NeZero M] {n : ℕ} {a : ℤ}

lemma inv_init (L : Finset (Fin M)) (ha : 0 ≤ a) : Inv a L (St.init M) := by
  refine ⟨fun j => ha, fun j => le_rfl, fun j => le_rfl, fun j => by simp [St.init], fun j _ => ?_⟩
  have : (0 : ℤ) ≤ (dstar L (St.init M) : ℤ) := Int.natCast_nonneg _
  simp only [St.init]
  omega

/-- `m` only decreases, so `D*` only increases. -/
lemma dstar_mono {L : Finset (Fin M)} {s s' : St M} (hm : ∀ i, s'.m i ≤ s.m i)
    (h0 : ∀ i, s'.m i ≤ 0) (h0s : ∀ i, s.m i ≤ 0) : dstar L s ≤ dstar L s' := by
  apply Finset.sup_le
  intro i hi
  have h1 := hm i
  have h2 := h0 i
  have h2s := h0s i
  have h3 : (s.m i).natAbs ≤ (s'.m i).natAbs := by omega
  exact h3.trans (le_dstar L s' hi)

/-- **The greedy invariant is preserved.** -/
lemma inv_step (L : Finset (Fin M)) (hL : L.card = n) (hn : n ≤ M) (s : St M) (b : Bool)
    (h : Inv a L s) : Inv a L (step n a s b) := by
  obtain ⟨hσa, hms, hm0, hmN, hgreedy⟩ := h
  by_cases hh : n ≤ (conf a s).card
  · rw [step_halted s b hh]; exact ⟨hσa, hms, hm0, hmN, hgreedy⟩
  have hne := unconf_nonempty_of_not_halted (a := a) s hn hh
  set j₀ := pick a s with hj₀
  have hj₀u : s.σ j₀ < a := mem_unconf.1 (pick_unconf hne)
  set inc : ℤ := (if b then 1 else -1) with hinc
  have hinc1 : inc = 1 ∨ inc = -1 := by rcases b with _ | _ <;> simp [hinc]
  set s' := step n a s b with hs'
  have hs'eq : s' = { σ := Function.update s.σ j₀ (s.σ j₀ + inc)
                      m := Function.update s.m j₀ (min (s.m j₀) (s.σ j₀ + inc))
                      N := Function.update s.N j₀ (s.N j₀ + 1) } := by
    rw [hs', step, if_neg hh]
  have hσ' : ∀ j, s'.σ j = if j = j₀ then s.σ j₀ + inc else s.σ j := by
    intro j; rw [hs'eq]; simp only [Function.update]; split_ifs with h1 <;> simp_all
  have hm' : ∀ j, s'.m j = if j = j₀ then min (s.m j₀) (s.σ j₀ + inc) else s.m j := by
    intro j; rw [hs'eq]; simp only [Function.update]; split_ifs with h1 <;> simp_all
  have hN' : ∀ j, s'.N j = if j = j₀ then s.N j₀ + 1 else s.N j := by
    intro j; rw [hs'eq]; simp only [Function.update]; split_ifs with h1 <;> simp_all
  have hmle : ∀ j, s'.m j ≤ s.m j := by
    intro j; rw [hm' j]; split_ifs with h1
    · rw [h1]; exact min_le_left (s.m j₀) (s.σ j₀ + inc)
    · exact le_rfl
  have hm0' : ∀ j, s'.m j ≤ 0 := fun j => (hmle j).trans (hm0 j)
  refine ⟨?_, ?_, hm0', ?_, ?_⟩
  · intro j; rw [hσ' j]; split_ifs with h1
    · rcases hinc1 with h | h <;> omega
    · exact hσa j
  · intro j; rw [hσ' j, hm' j]; split_ifs with h1
    · exact min_le_right _ _
    · exact hms j
  · intro j; rw [hm' j, hN' j]; split_ifs with h1
    · have h2 := hmN j₀
      have h3 := hms j₀
      rcases hinc1 with h | h <;> simp only [le_min_iff] <;> omega
    · have := hmN j; omega
  · intro j hj
    rw [hσ' j]
    by_cases h1 : j = j₀
    · -- the probed candidate is unlisted: `m` is unchanged on `L`, so `D*` is unchanged
      have hjL : j₀ ∉ L := by rw [← h1]; exact hj
      have hLm : ∀ i ∈ L, s'.m i = s.m i := by
        intro i hi
        have hne' : i ≠ j₀ := fun hc => hjL (hc ▸ hi)
        rw [hm' i, if_neg hne']
      have hdeq : dstar L s' = dstar L s := by
        unfold dstar
        exact Finset.sup_congr rfl (fun i hi => by rw [hLm i hi])
      obtain ⟨i₀, hi₀L, hi₀u⟩ := exists_listed_unconf (a := a) L hL s hh
      have hchain : -(dstar L s : ℤ) ≤ s.σ j₀ :=
        (neg_dstar_le L s hi₀L (hm0 i₀)).trans ((hms i₀).trans (pick_max hne hi₀u))
      rw [if_pos h1, hdeq]
      rcases hinc1 with h | h <;> omega
    · rw [if_neg h1]
      have := hgreedy j hj
      have hd := dstar_mono (L := L) hmle hm0' hm0
      omega

/-- The invariants hold at every reachable state. -/
lemma inv_state (L : Finset (Fin M)) (hL : L.card = n) (hn : n ≤ M) (ha : 0 ≤ a)
    (h : List Bool) : Inv a L (state n a h) := by
  have key : ∀ (l : List Bool) (s : St M), Inv a L s → Inv a L (l.foldl (step n a) s) := by
    intro l
    induction l with
    | nil => intro s hs; exact hs
    | cons b t ih => intro s hs; exact ih _ (inv_step L hL hn s b hs)
  exact key h _ (inv_init L ha)

/-- Total probe count is at most the number of rounds. -/
lemma sumN_le (h : List Bool) : ∑ j, (state (M := M) n a h).N j ≤ h.length := by
  have key : ∀ (l : List Bool) (s : St M),
      ∑ j, (l.foldl (step n a) s).N j ≤ ∑ j, s.N j + l.length := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons b t ih =>
      intro s
      rw [List.foldl_cons]
      refine (ih _).trans ?_
      have : ∑ j, (step n a s b).N j ≤ ∑ j, s.N j + 1 := by
        by_cases hh : n ≤ (conf a s).card
        · rw [step_halted s b hh]; omega
        · rw [step, if_neg hh]
          simp only
          rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
          have : ∑ x ∈ univ \ {pick a s}, s.N x + s.N (pick a s) = ∑ j, s.N j := by
            rw [Finset.sdiff_singleton_eq_erase]
            exact Finset.sum_erase_add _ _ (Finset.mem_univ _)
          omega
      simp only [List.length_cons]
      omega
  have := key h (St.init M)
  simpa [state, St.init] using this

/-- If the sieve has not halted, every round spent a probe. -/
lemma sumN_eq (h : List Bool) (hh : ¬ n ≤ (conf a (state (M := M) n a h)).card) :
    ∑ j, (state (M := M) n a h).N j = h.length := by
  have key : ∀ (l : List Bool) (s : St M), ¬ n ≤ (conf a (l.foldl (step n a) s)).card →
      ∑ j, (l.foldl (step n a) s).N j = ∑ j, s.N j + l.length := by
    intro l
    induction l with
    | nil => intro s _; simp
    | cons b t ih =>
      intro s hs
      rw [List.foldl_cons] at hs ⊢
      by_cases hh0 : n ≤ (conf a s).card
      · exfalso
        rw [step_halted s b hh0] at hs
        have hfrozen : ∀ (l' : List Bool) (s' : St M), n ≤ (conf a s').card →
            l'.foldl (step n a) s' = s' := by
          intro l'
          induction l' with
          | nil => intro s' _; rfl
          | cons b' t' ih' =>
            intro s' hs'
            rw [List.foldl_cons, step_halted s' b' hs']
            exact ih' s' hs'
        rw [hfrozen t s hh0] at hs
        exact hs hh0
      · rw [ih _ hs, step, if_neg hh0]
        simp only
        rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
        have : ∑ x ∈ univ \ {pick a s}, s.N x + s.N (pick a s) = ∑ j, s.N j := by
          rw [Finset.sdiff_singleton_eq_erase]
          exact Finset.sum_erase_add _ _ (Finset.mem_univ _)
        simp only [List.length_cons]
        omega
  have := key h (St.init M) hh
  simpa [state, St.init] using this

end

/-! ### Martingales along the sieve -/

section Process

variable [NeZero M] {n : ℕ} {a : ℤ}

lemma step_sigma (s : St M) (b : Bool) (hh : ¬ n ≤ (conf a s).card) (j : Fin M) :
    (step n a s b).σ j =
      if j = pick a s then s.σ (pick a s) + (if b then 1 else -1) else s.σ j := by
  rw [step, if_neg hh]
  by_cases hj : j = pick a s
  · simp [hj]
  · simp [hj, Function.update_of_ne hj]

lemma step_m (s : St M) (b : Bool) (hh : ¬ n ≤ (conf a s).card) (j : Fin M) :
    (step n a s b).m j =
      if j = pick a s then min (s.m (pick a s)) (s.σ (pick a s) + (if b then 1 else -1))
      else s.m j := by
  rw [step, if_neg hh]
  by_cases hj : j = pick a s
  · simp [hj]
  · simp [hj, Function.update_of_ne hj]

lemma step_N (s : St M) (b : Bool) (hh : ¬ n ≤ (conf a s).card) (j : Fin M) :
    (step n a s b).N j = if j = pick a s then s.N (pick a s) + 1 else s.N j := by
  rw [step, if_neg hh]
  by_cases hj : j = pick a s
  · simp [hj]
  · simp [hj, Function.update_of_ne hj]

/-- **Supermartingale principle.** A state function whose one-step average never increases has
non-increasing expectation along the sieve, at every horizon. -/
lemma val_super (pJ : Fin M → ℝ) (hp : ∀ j, 0 ≤ pJ j ∧ pJ j ≤ 1) (W : St M → ℝ)
    (hone : ∀ s : St M, pJ (pick a s) * W (step n a s true)
      + (1 - pJ (pick a s)) * W (step n a s false) ≤ W s) :
    ∀ (r : ℕ) (h : List Bool),
      val pJ (probeIdx (M := M) n a) (fun h' => W (state n a h')) r h ≤ W (state n a h) := by
  intro r
  induction r with
  | zero => intro h; exact le_rfl
  | succ r ih =>
    intro h
    have hb : val pJ (probeIdx n a) (fun h' => W (state n a h')) r (h ++ [true])
        ≤ W (step n a (state n a h) true) := by
      have := ih (h ++ [true]); rwa [state_append] at this
    have hf : val pJ (probeIdx n a) (fun h' => W (state n a h')) r (h ++ [false])
        ≤ W (step n a (state n a h) false) := by
      have := ih (h ++ [false]); rwa [state_append] at this
    have h0 := (hp (probeIdx n a h)).1
    have h1 : 0 ≤ 1 - pJ (probeIdx n a h) := by linarith [(hp (probeIdx n a h)).2]
    have hkey := hone (state n a h)
    have he : probeIdx (M := M) n a h = pick a (state n a h) := rfl
    rw [val_succ, he]
    rw [he] at h0 h1
    nlinarith [mul_le_mul_of_nonneg_left hb h0, mul_le_mul_of_nonneg_left hf h1]

/-- **Martingale principle.** -/
lemma val_mart (pJ : Fin M → ℝ) (W : St M → ℝ)
    (hone : ∀ s : St M, pJ (pick a s) * W (step n a s true)
      + (1 - pJ (pick a s)) * W (step n a s false) = W s) :
    ∀ (r : ℕ) (h : List Bool),
      val pJ (probeIdx (M := M) n a) (fun h' => W (state n a h')) r h = W (state n a h) := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    have hb := ih (h ++ [true])
    have hf := ih (h ++ [false])
    rw [state_append] at hb hf
    have he : probeIdx (M := M) n a h = pick a (state n a h) := rfl
    rw [val_succ, hb, hf, he]
    exact hone (state n a h)

/-! ### Step (b), (c): Wald's identity -/

/-- **Wald's identity** for candidate `j`: `σ_j(T) − (2p_j − 1)·N_j(T)` is a martingale. -/
theorem wald (pJ : Fin M → ℝ) (j : Fin M) :
    ∀ (r : ℕ) (h : List Bool),
      val pJ (probeIdx n a)
        (fun h' => ((state n a h').σ j : ℝ) - (2 * pJ j - 1) * ((state (M := M) n a h').N j : ℝ)) r h
      = ((state n a h).σ j : ℝ) - (2 * pJ j - 1) * ((state (M := M) n a h).N j : ℝ) := by
  refine val_mart pJ (fun s => ((s.σ j : ℝ) - (2 * pJ j - 1) * (s.N j : ℝ))) ?_
  intro s
  by_cases hh : n ≤ (conf a s).card
  · rw [step_halted s true hh, step_halted s false hh]; ring
  · rw [step_sigma s true hh, step_sigma s false hh, step_N s true hh, step_N s false hh]
    by_cases hj : j = pick a s
    · rw [hj]
      simp only [reduceIte]
      push_cast
      ring
    · simp only [if_neg hj]
      ring

/-- Wald from the empty history: `E[σ_j(T)] = (2p_j − 1)·E[N_j(T)]`. -/
theorem wald_zero (pJ : Fin M → ℝ) (j : Fin M) (T : ℕ) :
    val pJ (probeIdx n a) (fun h => ((state n a h).σ j : ℝ)) T []
      = (2 * pJ j - 1) * val pJ (probeIdx n a) (fun h => ((state (M := M) n a h).N j : ℝ)) T [] := by
  have hw := wald (a := a) (n := n) pJ j T []
  have hsplit : val pJ (probeIdx n a)
      (fun h' => ((state n a h').σ j : ℝ) - (2 * pJ j - 1) * ((state (M := M) n a h').N j : ℝ)) T [] =
      val pJ (probeIdx n a) (fun h => ((state n a h).σ j : ℝ)) T []
        + (0 + (-(2 * pJ j - 1)) *
            val pJ (probeIdx n a) (fun h => ((state (M := M) n a h).N j : ℝ)) T []) := by
    rw [← val_affine pJ (probeIdx n a) 0 (-(2 * pJ j - 1))
      (fun h => ((state (M := M) n a h).N j : ℝ)) T [], ← val_add]
    congr 1
    funext h'
    ring
  rw [hsplit] at hw
  simp only [state_nil, St.init] at hw
  simp only [Nat.cast_zero, Int.cast_zero, mul_zero, sub_zero] at hw
  linarith

/-! ### Steps (d), (e): exponential (super)martingales

`errW` is the exact martingale `e^{ℓ σ_j}` used for Ville's inequality on an unlisted walk;
`depthW` is the *stopped* exponential `e^{−ℓ σ_c}` used for the gambler's-ruin depth bound on a
listed walk. -/

/-- `e^{ℓ σ_j}`: an exact martingale when candidate `j` answers `Bern(ρ)`. -/
noncomputable def errW (ℓ : ℝ) (j : Fin M) (s : St M) : ℝ := Real.exp (ℓ * (s.σ j : ℝ))

/-- `e^{−ℓ σ_c}`, stopped when the walk first drops to `−k`: a supermartingale when candidate `c`
answers `Bern(1−ρ)`. -/
noncomputable def depthW (ℓ : ℝ) (c : Fin M) (k : ℕ) (s : St M) : ℝ :=
  if s.m c ≤ -(k : ℤ) then Real.exp ((k : ℝ) * ℓ) else Real.exp (-ℓ * (s.σ c : ℝ))

section Exp


/-- **Step (e): Ville's inequality.** An unlisted candidate is confirmed (its walk reaches `a`)
with probability at most `e^{−aℓ}`, at every horizon. -/
theorem error_tail (ρ ℓ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hexp : Real.exp ℓ = (1 - ρ) / ρ)
    (hℓ0 : 0 < ℓ) (pJ : Fin M → ℝ) (hp : ∀ x, 0 ≤ pJ x ∧ pJ x ≤ 1) (j : Fin M) (hj : pJ j = ρ)
    (T : ℕ) :
    val pJ (probeIdx (M := M) n a) (fun h => if a ≤ (state n a h).σ j then (1 : ℝ) else 0) T []
      ≤ Real.exp (-((a : ℝ) * ℓ)) := by
  have hρ0' : ρ ≠ 0 := ne_of_gt hρ0
  have hρ1' : (1 : ℝ) - ρ ≠ 0 := by intro hc; linarith
  have hone : ∀ s : St M, pJ (pick a s) * errW ℓ j (step n a s true)
      + (1 - pJ (pick a s)) * errW ℓ j (step n a s false) = errW ℓ j s := by
    intro s
    by_cases hh : n ≤ (conf a s).card
    · rw [step_halted s true hh, step_halted s false hh]; ring
    by_cases hjp : j = pick a s
    · have key : ∀ (b : Bool) (inc : ℤ), (if b then (1 : ℤ) else -1) = inc →
          errW ℓ j (step n a s b) = Real.exp (ℓ * (s.σ j : ℝ)) * Real.exp (ℓ * (inc : ℝ)) := by
        intro b inc hinc
        rw [errW, step_sigma s b hh j, if_pos hjp, ← hjp, hinc, ← Real.exp_add]
        push_cast
        ring_nf
      rw [key true 1 rfl, key false (-1) rfl, ← hjp, hj, errW]
      rw [show ((1 : ℤ) : ℝ) = (1 : ℝ) from by norm_num, show ((-1 : ℤ) : ℝ) = (-1 : ℝ) from by norm_num,
        mul_one, show ℓ * (-1 : ℝ) = -ℓ from by ring, Real.exp_neg, hexp]
      field_simp
      ring
    · rw [errW, errW, errW, step_sigma s true hh j, step_sigma s false hh j, if_neg hjp,
        if_neg hjp]
      ring
  have hval := val_mart (a := a) (n := n) pJ (errW ℓ j) hone T []
  rw [state_nil] at hval
  have hinit : errW ℓ j (St.init M) = 1 := by simp [errW, St.init]
  have hdom : ∀ h' : List Bool, (if a ≤ (state n a h').σ j then (1 : ℝ) else 0)
      ≤ Real.exp (-((a : ℝ) * ℓ)) * errW ℓ j (state n a h') := by
    intro h'
    by_cases hge : a ≤ (state n a h').σ j
    · rw [if_pos hge, errW, ← Real.exp_add]
      have hcast : ((a : ℤ) : ℝ) ≤ (((state n a h').σ j : ℤ) : ℝ) := by exact_mod_cast hge
      have : (0 : ℝ) ≤ -((a : ℝ) * ℓ) + ℓ * (((state n a h').σ j : ℤ) : ℝ) := by nlinarith
      calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ _ := Real.exp_le_exp.2 this
    · rw [if_neg hge, errW]; positivity
  have haff : val pJ (probeIdx (M := M) n a)
      (fun h' => Real.exp (-((a : ℝ) * ℓ)) * errW ℓ j (state n a h')) T []
      = Real.exp (-((a : ℝ) * ℓ)) *
        val pJ (probeIdx (M := M) n a) (fun h' => errW ℓ j (state n a h')) T [] := by
    simpa using val_affine pJ (probeIdx (M := M) n a) 0 (Real.exp (-((a : ℝ) * ℓ)))
      (fun h' => errW ℓ j (state n a h')) T []
  calc val pJ (probeIdx (M := M) n a)
        (fun h => if a ≤ (state n a h).σ j then (1 : ℝ) else 0) T []
      ≤ val pJ (probeIdx (M := M) n a)
          (fun h' => Real.exp (-((a : ℝ) * ℓ)) * errW ℓ j (state n a h')) T [] :=
        val_mono (probeIdx (M := M) n a) hp T [] (fun h' _ => hdom h')
    _ = Real.exp (-((a : ℝ) * ℓ)) * val pJ (probeIdx (M := M) n a)
          (fun h' => errW ℓ j (state n a h')) T [] := haff
    _ = Real.exp (-((a : ℝ) * ℓ)) := by rw [hval, hinit, mul_one]

/-- **Step (d): gambler's ruin.** A listed candidate's walk drops to `−k` with probability at most
`e^{−kℓ}`, at every horizon. -/
theorem depth_tail (ρ ℓ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hexp : Real.exp ℓ = (1 - ρ) / ρ)
    (hℓ0 : 0 < ℓ) (pJ : Fin M → ℝ) (hp : ∀ x, 0 ≤ pJ x ∧ pJ x ≤ 1) (c : Fin M) (hc : pJ c = 1 - ρ)
    (k : ℕ) (hk : 1 ≤ k) (T : ℕ) :
    val pJ (probeIdx (M := M) n a)
        (fun h => if (state n a h).m c ≤ -(k : ℤ) then (1 : ℝ) else 0) T []
      ≤ Real.exp (-((k : ℝ) * ℓ)) := by
  have hρ0' : ρ ≠ 0 := ne_of_gt hρ0
  have hρ1' : (1 : ℝ) - ρ ≠ 0 := by intro hcon; linarith
  have hone : ∀ s : St M, pJ (pick a s) * depthW ℓ c k (step n a s true)
      + (1 - pJ (pick a s)) * depthW ℓ c k (step n a s false) ≤ depthW ℓ c k s := by
    intro s
    by_cases hh : n ≤ (conf a s).card
    · rw [step_halted s true hh, step_halted s false hh]; exact le_of_eq (by ring)
    by_cases hmc : s.m c ≤ -(k : ℤ)
    · have hmono : ∀ b : Bool, (step n a s b).m c ≤ s.m c := by
        intro b
        rw [step_m s b hh c]
        by_cases hcp : c = pick a s
        · rw [if_pos hcp, hcp]; exact min_le_left _ _
        · rw [if_neg hcp]
      have hb : ∀ b : Bool, depthW ℓ c k (step n a s b) = Real.exp ((k : ℝ) * ℓ) := by
        intro b; rw [depthW, if_pos ((hmono b).trans hmc)]
      rw [hb true, hb false, depthW, if_pos hmc]
      exact le_of_eq (by ring)
    by_cases hcp : c = pick a s
    · have key : ∀ (b : Bool) (inc : ℤ), (if b then (1 : ℤ) else -1) = inc →
          depthW ℓ c k (step n a s b)
            ≤ Real.exp (-ℓ * (s.σ c : ℝ)) * Real.exp (-ℓ * (inc : ℝ)) := by
        intro b inc hinc
        rw [depthW, step_m s b hh c, step_sigma s b hh c, if_pos hcp, if_pos hcp, ← hcp, hinc,
          ← Real.exp_add]
        split_ifs with hmin
        · apply Real.exp_le_exp.2
          have hle : s.σ c + inc ≤ -(k : ℤ) := by
            rcases min_le_iff.1 hmin with hcon | hcon
            · exact absurd hcon hmc
            · exact hcon
          have h2 : ((s.σ c : ℤ) : ℝ) + ((inc : ℤ) : ℝ) ≤ -(k : ℝ) := by exact_mod_cast hle
          nlinarith
        · push_cast
          apply le_of_eq
          congr 1
          ring
      have hpc : pJ (pick a s) = 1 - ρ := by rw [← hcp]; exact hc
      have h0 : 0 ≤ pJ (pick a s) := (hp (pick a s)).1
      have h1 : 0 ≤ 1 - pJ (pick a s) := by linarith [(hp (pick a s)).2]
      have hsum : pJ (pick a s) * (Real.exp (-ℓ * (s.σ c : ℝ)) * Real.exp (-ℓ * ((1 : ℤ) : ℝ)))
          + (1 - pJ (pick a s)) *
            (Real.exp (-ℓ * (s.σ c : ℝ)) * Real.exp (-ℓ * ((-1 : ℤ) : ℝ)))
          = depthW ℓ c k s := by
        rw [depthW, if_neg hmc, hpc]
        rw [show ((1 : ℤ) : ℝ) = (1 : ℝ) from by norm_num, show ((-1 : ℤ) : ℝ) = (-1 : ℝ) from by norm_num]
        rw [show -ℓ * (1 : ℝ) = -ℓ from by ring, show -ℓ * (-1 : ℝ) = ℓ from by ring,
          Real.exp_neg, hexp]
        field_simp
        ring
      nlinarith [key true 1 rfl, key false (-1) rfl,
        mul_le_mul_of_nonneg_left (key true 1 rfl) h0,
        mul_le_mul_of_nonneg_left (key false (-1) rfl) h1]
    · have hb : ∀ b : Bool, depthW ℓ c k (step n a s b) = depthW ℓ c k s := by
        intro b
        rw [depthW, depthW, step_m s b hh c, step_sigma s b hh c, if_neg hcp, if_neg hcp]
      rw [hb true, hb false]
      exact le_of_eq (by ring)
  have hval := val_super (a := a) (n := n) pJ hp (depthW ℓ c k) hone T []
  rw [state_nil] at hval
  have hinit : depthW ℓ c k (St.init M) = 1 := by
    rw [depthW, if_neg]
    · simp [St.init]
    · simp only [St.init]
      omega
  have hdom : ∀ h' : List Bool, (if (state n a h').m c ≤ -(k : ℤ) then (1 : ℝ) else 0)
      ≤ Real.exp (-((k : ℝ) * ℓ)) * depthW ℓ c k (state n a h') := by
    intro h'
    by_cases hge : (state n a h').m c ≤ -(k : ℤ)
    · rw [if_pos hge, depthW, if_pos hge, ← Real.exp_add]
      rw [show -((k : ℝ) * ℓ) + (k : ℝ) * ℓ = 0 from by ring, Real.exp_zero]
    · rw [if_neg hge, depthW, if_neg hge]; positivity
  have haff : val pJ (probeIdx (M := M) n a)
      (fun h' => Real.exp (-((k : ℝ) * ℓ)) * depthW ℓ c k (state n a h')) T []
      = Real.exp (-((k : ℝ) * ℓ)) *
        val pJ (probeIdx (M := M) n a) (fun h' => depthW ℓ c k (state n a h')) T [] := by
    simpa using val_affine pJ (probeIdx (M := M) n a) 0 (Real.exp (-((k : ℝ) * ℓ)))
      (fun h' => depthW ℓ c k (state n a h')) T []
  have hfin : Real.exp (-((k : ℝ) * ℓ)) *
      val pJ (probeIdx (M := M) n a) (fun h' => depthW ℓ c k (state n a h')) T []
      ≤ Real.exp (-((k : ℝ) * ℓ)) := by
    rw [hinit] at hval
    nlinarith [Real.exp_pos (-((k : ℝ) * ℓ))]
  calc val pJ (probeIdx (M := M) n a)
        (fun h => if (state n a h).m c ≤ -(k : ℤ) then (1 : ℝ) else 0) T []
      ≤ val pJ (probeIdx (M := M) n a)
          (fun h' => Real.exp (-((k : ℝ) * ℓ)) * depthW ℓ c k (state n a h')) T [] :=
        val_mono (probeIdx (M := M) n a) hp T [] (fun h' _ => hdom h')
    _ = _ := haff
    _ ≤ Real.exp (-((k : ℝ) * ℓ)) := hfin

end Exp

/-! ### Elementary sums -/

lemma sum_lt_indicator (D : ℕ) : ∀ T : ℕ, D ≤ T →
    ∑ k ∈ Finset.range T, (if k < D then (1 : ℝ) else 0) = D := by
  intro T
  induction T with
  | zero => intro h; have : D = 0 := by omega
            subst this; simp
  | succ T ih =>
    intro h
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge T D with hTD | hTD
    · have hD : D = T + 1 := by omega
      subst hD
      rw [if_pos (by omega)]
      have hall : ∀ k ∈ Finset.range T, (if k < T + 1 then (1 : ℝ) else 0) = 1 := by
        intro k hk; rw [if_pos (by simp only [Finset.mem_range] at hk; omega)]
      rw [Finset.sum_congr rfl hall]
      simp
    · rw [if_neg (by omega), ih hTD, add_zero]

lemma geom_range_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, r ^ k ≤ 1 / (1 - r) := by
  have h1 : (0 : ℝ) < 1 - r := by linarith
  rw [le_div_iff₀ h1]
  have h2 : (∑ k ∈ Finset.range N, r ^ k) * (1 - r) = 1 - r ^ N := by
    linear_combination -geom_sum_mul r N
  rw [h2]
  have : (0 : ℝ) ≤ r ^ N := pow_nonneg hr0 N
  linarith

lemma tail_geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k₀ T : ℕ) (f : ℕ → ℝ)
    (hf1 : ∀ k, f k ≤ 1) (hf2 : ∀ k, k₀ ≤ k → f k ≤ r ^ (k + 1 - k₀)) :
    ∑ k ∈ Finset.range T, f k ≤ (k₀ : ℝ) + r / (1 - r) := by
  have hr1' : (0 : ℝ) < 1 - r := by linarith
  have hgeo : (0 : ℝ) ≤ r / (1 - r) := by positivity
  rcases le_or_gt T k₀ with hT | hT
  · have h1 : ∑ k ∈ Finset.range T, f k ≤ (T : ℝ) := by
      calc ∑ k ∈ Finset.range T, f k ≤ ∑ _k ∈ Finset.range T, (1 : ℝ) :=
            Finset.sum_le_sum (fun k _ => hf1 k)
        _ = (T : ℝ) := by simp
    have h2 : (T : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hT
    linarith
  · have hsplit : ∑ k ∈ Finset.range T, f k
        = ∑ k ∈ Finset.range k₀, f k + ∑ k ∈ Finset.Ico k₀ T, f k := by
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive f (Nat.zero_le k₀) hT.le,
        ← Finset.range_eq_Ico]
    rw [hsplit]
    have h1 : ∑ k ∈ Finset.range k₀, f k ≤ (k₀ : ℝ) := by
      calc ∑ k ∈ Finset.range k₀, f k ≤ ∑ _k ∈ Finset.range k₀, (1 : ℝ) :=
            Finset.sum_le_sum (fun k _ => hf1 k)
        _ = (k₀ : ℝ) := by simp
    have h2 : ∑ k ∈ Finset.Ico k₀ T, f k ≤ r / (1 - r) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hb : ∀ i ∈ Finset.range (T - k₀), f (k₀ + i) ≤ r * r ^ i := by
        intro i _
        have hfi := hf2 (k₀ + i) (Nat.le_add_right _ _)
        rw [show k₀ + i + 1 - k₀ = i + 1 by omega] at hfi
        calc f (k₀ + i) ≤ r ^ (i + 1) := hfi
          _ = r * r ^ i := by ring
      calc ∑ i ∈ Finset.range (T - k₀), f (k₀ + i)
          ≤ ∑ i ∈ Finset.range (T - k₀), r * r ^ i := Finset.sum_le_sum hb
        _ = r * ∑ i ∈ Finset.range (T - k₀), r ^ i := by rw [Finset.mul_sum]
        _ ≤ r * (1 / (1 - r)) := mul_le_mul_of_nonneg_left (geom_range_le hr0 hr1 _) hr0
        _ = r / (1 - r) := by ring
    linarith

/-! ### The response law of the `thr`-separated pool under K1(ρ) -/

/-- Response probability at pool point `j`: `1 − ρ` if `j` is enrolled, `ρ` otherwise. -/
noncomputable def poolResp (L : Finset (Fin M)) (ρ : ℝ) (j : Fin M) : ℝ :=
  if j ∈ L then 1 - ρ else ρ

lemma poolResp_mem_Icc (L : Finset (Fin M)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    ∀ j, 0 ≤ poolResp L ρ j ∧ poolResp L ρ j ≤ 1 := by
  intro j; unfold poolResp; split_ifs <;> constructor <;> linarith

section Main

/-- **Step (d), assembled.** `E[D*] ≤ log n/ℓ + (1−ρ)/(1−2ρ)`, i.e.
`E[ℓ D*] ≤ log n + ℓ(1−ρ)/(1−2ρ)`. -/
theorem sieve_depth (ρ ℓ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hexp : Real.exp ℓ = (1 - ρ) / ρ)
    (hℓ0 : 0 < ℓ) (L : Finset (Fin M)) (hL : L.card = n) (hn : 0 < n) (hnM : n ≤ M)
    (ha : 0 ≤ a) (T : ℕ) :
    val (poolResp L ρ) (probeIdx (M := M) n a) (fun h => (dstar L (state n a h) : ℝ)) T []
      ≤ Real.log n / ℓ + (1 - ρ) / (1 - 2 * ρ) := by
  have hp := poolResp_mem_Icc L hρ0 hρ1
  set pJ := poolResp L ρ with hpJ
  set r : ℝ := Real.exp (-ℓ) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hrv : r = ρ / (1 - ρ) := by rw [hr, Real.exp_neg, hexp, inv_div]
  have hρ1' : (0 : ℝ) < 1 - ρ := by linarith
  have hr1 : r < 1 := by rw [hrv, div_lt_one hρ1']; linarith
  -- pointwise: `D* ≤ T` at a leaf of depth `T`
  have hbound : ∀ h' : List Bool, h'.length = T → dstar L (state n a h') ≤ T := by
    intro h' hlen
    apply Finset.sup_le
    intro i _
    obtain ⟨-, -, hm0, hmN, -⟩ := inv_state (a := a) L hL hnM ha h'
    have h1 : ((state n a h').m i).natAbs ≤ (state n a h').N i := by
      have := hmN i; have := hm0 i; omega
    have h2 : (state n a h').N i ≤ ∑ j, (state n a h').N j :=
      Finset.single_le_sum (f := fun j => (state n a h').N j)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h3 := sumN_le (M := M) (n := n) (a := a) h'
    omega
  -- rewrite `D*` as a sum of indicators and split the expectation
  have hrw : val pJ (probeIdx (M := M) n a) (fun h => (dstar L (state n a h) : ℝ)) T []
      = val pJ (probeIdx (M := M) n a)
          (fun h => ∑ k ∈ Finset.range T,
            (if k < dstar L (state n a h) then (1 : ℝ) else 0)) T [] := by
    apply val_mono_eq
    intro h' hlen
    simp only [List.length_nil, zero_add] at hlen
    rw [sum_lt_indicator _ T (hbound h' hlen)]
  rw [hrw, val_sum pJ (probeIdx (M := M) n a) (Finset.range T)
    (fun k h => if k < dstar L (state n a h) then (1 : ℝ) else 0) T []]
  -- each term: `P[D* > k] ≤ min(1, n e^{−(k+1)ℓ})`
  have hterm : ∀ k : ℕ, val pJ (probeIdx (M := M) n a)
      (fun h => if k < dstar L (state n a h) then (1 : ℝ) else 0) T [] ≤ 1 := by
    intro k
    have := val_mono (probeIdx (M := M) n a) hp (G := fun _ => (1 : ℝ))
      (F := fun h => if k < dstar L (state n a h) then (1 : ℝ) else 0) T []
      (fun h' _ => by split_ifs <;> norm_num)
    rwa [val_const] at this
  have hterm2 : ∀ k : ℕ, val pJ (probeIdx (M := M) n a)
      (fun h => if k < dstar L (state n a h) then (1 : ℝ) else 0) T []
      ≤ (n : ℝ) * r ^ (k + 1) := by
    intro k
    have hdom : ∀ h' : List Bool, (if k < dstar L (state n a h') then (1 : ℝ) else 0)
        ≤ ∑ i ∈ L, (if (state n a h').m i ≤ -((k + 1 : ℕ) : ℤ) then (1 : ℝ) else 0) := by
      intro h'
      obtain ⟨-, -, hm0, -, -⟩ := inv_state (a := a) L hL hnM ha h'
      by_cases hk : k < dstar L (state n a h')
      · rw [if_pos hk]
        obtain ⟨i, hiL, hi⟩ := lt_dstar_iff.1 hk
        have hmi : (state n a h').m i ≤ -((k + 1 : ℕ) : ℤ) := by
          have := hm0 i; push_cast; omega
        calc (1 : ℝ) = (if (state n a h').m i ≤ -((k + 1 : ℕ) : ℤ) then (1 : ℝ) else 0) := by
              rw [if_pos hmi]
          _ ≤ _ := Finset.single_le_sum
              (f := fun i => if (state n a h').m i ≤ -((k + 1 : ℕ) : ℤ) then (1 : ℝ) else 0)
              (fun i _ => by split_ifs <;> norm_num) hiL
      · rw [if_neg hk]
        exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
    calc val pJ (probeIdx (M := M) n a)
          (fun h => if k < dstar L (state n a h) then (1 : ℝ) else 0) T []
        ≤ val pJ (probeIdx (M := M) n a)
            (fun h => ∑ i ∈ L,
              (if (state n a h).m i ≤ -((k + 1 : ℕ) : ℤ) then (1 : ℝ) else 0)) T [] :=
          val_mono (probeIdx (M := M) n a) hp T [] (fun h' _ => hdom h')
      _ = ∑ i ∈ L, val pJ (probeIdx (M := M) n a)
            (fun h => if (state n a h).m i ≤ -((k + 1 : ℕ) : ℤ) then (1 : ℝ) else 0) T [] :=
          val_sum pJ (probeIdx (M := M) n a) L
            (fun i h => if (state n a h).m i ≤ -((k + 1 : ℕ) : ℤ) then (1 : ℝ) else 0) T []
      _ ≤ ∑ _i ∈ L, Real.exp (-(((k + 1 : ℕ) : ℝ) * ℓ)) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact depth_tail ρ ℓ hρ0 hρ1 hexp hℓ0 pJ hp i (by rw [hpJ, poolResp, if_pos hi])
            (k + 1) (by omega) T
      _ = (n : ℝ) * r ^ (k + 1) := by
          rw [Finset.sum_const, hL, nsmul_eq_mul, hr, ← Real.exp_nat_mul]
          congr 2
          push_cast
          ring
  -- geometric tail with `k₀ = ⌈log n/ℓ⌉`
  set k₀ : ℕ := ⌈Real.log n / ℓ⌉₊ with hk₀
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hk₀ge : Real.log n / ℓ ≤ (k₀ : ℝ) := Nat.le_ceil _
  have hk₀lt : (k₀ : ℝ) < Real.log n / ℓ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hnr : (n : ℝ) * r ^ k₀ ≤ 1 := by
    rw [hr, ← Real.exp_nat_mul]
    have hlog : Real.log n ≤ (k₀ : ℝ) * ℓ := by
      rw [div_le_iff₀ hℓ0] at hk₀ge; linarith
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← Real.exp_log hn0, ← Real.exp_add]
    rw [show (k₀ : ℝ) * -ℓ = -((k₀ : ℝ) * ℓ) from by ring]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by linarith)
  have hmain := tail_geom_le hr0.le hr1 k₀ T
    (fun k => val pJ (probeIdx (M := M) n a)
      (fun h => if k < dstar L (state n a h) then (1 : ℝ) else 0) T [])
    hterm (by
      intro k hk
      have h1 := hterm2 k
      have h2 : (n : ℝ) * r ^ (k + 1) ≤ r ^ (k + 1 - k₀) := by
        have hsplit : r ^ (k + 1) = r ^ k₀ * r ^ (k + 1 - k₀) := by
          rw [← pow_add]; congr 1; omega
        have hpos : (0 : ℝ) ≤ r ^ (k + 1 - k₀) := pow_nonneg hr0.le _
        calc (n : ℝ) * r ^ (k + 1) = ((n : ℝ) * r ^ k₀) * r ^ (k + 1 - k₀) := by
              rw [hsplit]; ring
          _ ≤ 1 * r ^ (k + 1 - k₀) := by exact mul_le_mul_of_nonneg_right hnr hpos
          _ = r ^ (k + 1 - k₀) := one_mul _
      linarith)
  have h2ρ : (0 : ℝ) < 1 - 2 * ρ := by linarith
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hgeo : r / (1 - r) = ρ / (1 - 2 * ρ) := by
    rw [div_eq_div_iff (ne_of_gt h1r) (ne_of_gt h2ρ), hrv]
    field_simp
    ring
  have hfinal : (k₀ : ℝ) + r / (1 - r) ≤ Real.log n / ℓ + (1 - ρ) / (1 - 2 * ρ) := by
    rw [hgeo]
    have hsplit2 : (1 - ρ) / (1 - 2 * ρ) = 1 + ρ / (1 - 2 * ρ) := by
      have he : (1 : ℝ) - ρ = (1 - 2 * ρ) + ρ := by ring
      rw [he, add_div, div_self (ne_of_gt h2ρ)]
    rw [hsplit2]
    linarith
  linarith [hmain, hfinal]

/-! ### Steps (b), (c): per-candidate costs -/

/-- **Step (c).** A listed candidate: `(1−2ρ)·E[N_i(T)] ≤ a`. -/
theorem sieve_listed_cost (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (L : Finset (Fin M))
    (hL : L.card = n) (hnM : n ≤ M) (ha : 0 ≤ a) (i : Fin M) (hi : i ∈ L) (T : ℕ) :
    (1 - 2 * ρ) * val (poolResp L ρ) (probeIdx (M := M) n a)
      (fun h => ((state n a h).N i : ℝ)) T [] ≤ (a : ℝ) := by
  have hp := poolResp_mem_Icc L hρ0 hρ1
  have hw := wald_zero (a := a) (n := n) (poolResp L ρ) i T
  rw [show poolResp L ρ i = 1 - ρ from by rw [poolResp, if_pos hi],
    show 2 * (1 - ρ) - 1 = 1 - 2 * ρ from by ring] at hw
  have hσ : val (poolResp L ρ) (probeIdx (M := M) n a)
      (fun h => ((state n a h).σ i : ℝ)) T [] ≤ (a : ℝ) := by
    have := val_mono (probeIdx (M := M) n a) hp (G := fun _ => (a : ℝ))
      (F := fun h => ((state n a h).σ i : ℝ)) T []
      (fun h' _ => by exact_mod_cast (inv_state (a := a) L hL hnM ha h').1 i)
    rwa [val_const] at this
  linarith

/-- **Step (b).** An unlisted candidate: `(1−2ρ)·E[N_j(T)] ≤ E[D*] + 1` — the greedy invariant
feeding Wald's identity for a walk of drift `−KL_ρ`. -/
theorem sieve_unlisted_cost (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (L : Finset (Fin M))
    (hL : L.card = n) (hnM : n ≤ M) (ha : 0 ≤ a) (j : Fin M) (hj : j ∉ L) (T : ℕ) :
    (1 - 2 * ρ) * val (poolResp L ρ) (probeIdx (M := M) n a)
        (fun h => ((state (M := M) n a h).N j : ℝ)) T []
      ≤ val (poolResp L ρ) (probeIdx (M := M) n a)
          (fun h => (dstar L (state n a h) : ℝ)) T [] + 1 := by
  have hp := poolResp_mem_Icc L hρ0 hρ1
  have hw := wald_zero (a := a) (n := n) (poolResp L ρ) j T
  rw [show poolResp L ρ j = ρ from by rw [poolResp, if_neg hj],
    show 2 * ρ - 1 = -(1 - 2 * ρ) from by ring] at hw
  have hdom : ∀ h' : List Bool,
      (-1 : ℝ) + (-1 : ℝ) * (dstar L (state n a h') : ℝ) ≤ ((state n a h').σ j : ℝ) := by
    intro h'
    have hinv := (inv_state (a := a) L hL hnM ha h').2.2.2.2 j hj
    have hc : ((-(dstar L (state n a h') : ℤ) - 1 : ℤ) : ℝ)
        ≤ (((state n a h').σ j : ℤ) : ℝ) := by exact_mod_cast hinv
    push_cast at hc
    linarith
  have hlow := val_mono (probeIdx (M := M) n a) hp
    (F := fun h' => (-1 : ℝ) + (-1 : ℝ) * (dstar L (state n a h') : ℝ))
    (G := fun h' => ((state n a h').σ j : ℝ)) T [] (fun h' _ => hdom h')
  rw [val_affine] at hlow
  linarith

/-- The bound of Proposition 4.4.2 on `E[Q]`. -/
noncomputable def costBound (M n : ℕ) (ρ ℓ A : ℝ) : ℝ :=
  ((M - n : ℕ) : ℝ) * (Real.log n / ((1 - 2 * ρ) * ℓ) + (2 - 3 * ρ) / (1 - 2 * ρ) ^ 2)
    + (n : ℝ) * (A / ((1 - 2 * ρ) * ℓ) + 1 / (1 - 2 * ρ))

/-- **Proposition 4.4.2, expected query count.** At every horizon `T`, the expected number of
probes issued in the first `T` rounds is at most
`(M−n)(log n/KL_ρ + (2−3ρ)/(1−2ρ)²) + n(A/KL_ρ + 1/(1−2ρ))`, with `KL_ρ = (1−2ρ)ℓ_ρ`. -/
theorem sieve_cost (ρ ℓ A : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hexp : Real.exp ℓ = (1 - ρ) / ρ)
    (hℓ0 : 0 < ℓ) (L : Finset (Fin M)) (hL : L.card = n) (hn : 0 < n) (hnM : n ≤ M)
    (ha0 : 0 ≤ a) (haA : (a : ℝ) * ℓ ≤ A + ℓ) (T : ℕ) :
    val (poolResp L ρ) (probeIdx (M := M) n a) (fun h => ∑ j, ((state (M := M) n a h).N j : ℝ)) T []
      ≤ costBound M n ρ ℓ A := by
  have hp := poolResp_mem_Icc L hρ0 hρ1
  have h2ρ : (0 : ℝ) < 1 - 2 * ρ := by linarith
  set CL : ℝ := A / ((1 - 2 * ρ) * ℓ) + 1 / (1 - 2 * ρ) with hCLdef
  set CU : ℝ := Real.log n / ((1 - 2 * ρ) * ℓ) + (2 - 3 * ρ) / (1 - 2 * ρ) ^ 2 with hCUdef
  have hCLmul : (1 - 2 * ρ) * CL = A / ℓ + 1 := by rw [hCLdef]; field_simp
  have hCUmul : (1 - 2 * ρ) * CU = Real.log n / ℓ + (2 - 3 * ρ) / (1 - 2 * ρ) := by
    rw [hCUdef]; field_simp
  have haA' : (a : ℝ) ≤ A / ℓ + 1 := by
    have h1 : A / ℓ + 1 - (a : ℝ) = (A + ℓ - (a : ℝ) * ℓ) / ℓ := by field_simp
    have h2 : 0 ≤ (A + ℓ - (a : ℝ) * ℓ) / ℓ := div_nonneg (by linarith) hℓ0.le
    linarith
  have hdep := sieve_depth (a := a) ρ ℓ hρ0 hρ1 hexp hℓ0 L hL hn hnM ha0 T
  have hsplit2 : (1 - ρ) / (1 - 2 * ρ) + 1 = (2 - 3 * ρ) / (1 - 2 * ρ) := by
    have he : (2 : ℝ) - 3 * ρ = (1 - ρ) + (1 - 2 * ρ) := by ring
    rw [he, add_div, div_self (ne_of_gt h2ρ)]
  -- per-candidate bounds
  have hlist : ∀ i ∈ L, val (poolResp L ρ) (probeIdx (M := M) n a)
      (fun h => ((state n a h).N i : ℝ)) T [] ≤ CL := by
    intro i hi
    have h := sieve_listed_cost (a := a) ρ hρ0 hρ1 L hL hnM ha0 i hi T
    have : (1 - 2 * ρ) * val (poolResp L ρ) (probeIdx (M := M) n a)
        (fun h => ((state n a h).N i : ℝ)) T [] ≤ (1 - 2 * ρ) * CL := by
      rw [hCLmul]; linarith
    exact le_of_mul_le_mul_left this h2ρ
  have hunl : ∀ j ∈ Lᶜ, val (poolResp L ρ) (probeIdx (M := M) n a)
      (fun h => ((state (M := M) n a h).N j : ℝ)) T [] ≤ CU := by
    intro j hj
    have hj' : j ∉ L := by simpa using hj
    have h := sieve_unlisted_cost (a := a) ρ hρ0 hρ1 L hL hnM ha0 j hj' T
    have : (1 - 2 * ρ) * val (poolResp L ρ) (probeIdx (M := M) n a)
        (fun h => ((state (M := M) n a h).N j : ℝ)) T [] ≤ (1 - 2 * ρ) * CU := by
      rw [hCUmul, ← hsplit2]; linarith
    exact le_of_mul_le_mul_left this h2ρ
  -- assemble
  rw [val_sum (poolResp L ρ) (probeIdx (M := M) n a) Finset.univ
    (fun j h => ((state (M := M) n a h).N j : ℝ)) T []]
  rw [← Finset.sum_add_sum_compl L
    (fun j => val (poolResp L ρ) (probeIdx (M := M) n a)
      (fun h => ((state (M := M) n a h).N j : ℝ)) T [])]
  have hc1 : ∑ i ∈ L, val (poolResp L ρ) (probeIdx (M := M) n a)
      (fun h => ((state n a h).N i : ℝ)) T [] ≤ (n : ℝ) * CL := by
    calc _ ≤ ∑ _i ∈ L, CL := Finset.sum_le_sum hlist
      _ = (n : ℝ) * CL := by rw [Finset.sum_const, hL, nsmul_eq_mul]
  have hc2 : ∑ j ∈ Lᶜ, val (poolResp L ρ) (probeIdx (M := M) n a)
      (fun h => ((state (M := M) n a h).N j : ℝ)) T [] ≤ ((M - n : ℕ) : ℝ) * CU := by
    calc _ ≤ ∑ _j ∈ Lᶜ, CU := Finset.sum_le_sum hunl
      _ = ((M - n : ℕ) : ℝ) * CU := by
          rw [Finset.sum_const, Finset.card_compl, hL, Fintype.card_fin, nsmul_eq_mul]
  rw [costBound]
  linarith

/-! ### Steps (e), (f): error and termination -/

/-- **Step (e).** The probability that some unlisted candidate is ever confirmed is at most
`(M − n)·e^{−aℓ}` — Ville's inequality plus the union bound. -/
theorem sieve_error (ρ ℓ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hexp : Real.exp ℓ = (1 - ρ) / ρ)
    (hℓ0 : 0 < ℓ) (L : Finset (Fin M)) (hL : L.card = n) (T : ℕ) :
    val (poolResp L ρ) (probeIdx (M := M) n a)
        (fun h => if ∃ j ∈ Lᶜ, a ≤ (state n a h).σ j then (1 : ℝ) else 0) T []
      ≤ ((M - n : ℕ) : ℝ) * Real.exp (-((a : ℝ) * ℓ)) := by
  have hp := poolResp_mem_Icc L hρ0 hρ1
  have hdom : ∀ h' : List Bool,
      (if ∃ j ∈ Lᶜ, a ≤ (state n a h').σ j then (1 : ℝ) else 0)
      ≤ ∑ j ∈ Lᶜ, (if a ≤ (state n a h').σ j then (1 : ℝ) else 0) := by
    intro h'
    by_cases hex : ∃ j ∈ Lᶜ, a ≤ (state n a h').σ j
    · rw [if_pos hex]
      obtain ⟨j, hjc, hj⟩ := hex
      calc (1 : ℝ) = (if a ≤ (state n a h').σ j then (1 : ℝ) else 0) := by rw [if_pos hj]
        _ ≤ _ := Finset.single_le_sum
            (f := fun j => if a ≤ (state n a h').σ j then (1 : ℝ) else 0)
            (fun i _ => by split_ifs <;> norm_num) hjc
    · rw [if_neg hex]
      exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  calc val (poolResp L ρ) (probeIdx (M := M) n a)
        (fun h => if ∃ j ∈ Lᶜ, a ≤ (state n a h).σ j then (1 : ℝ) else 0) T []
      ≤ val (poolResp L ρ) (probeIdx (M := M) n a)
          (fun h => ∑ j ∈ Lᶜ, (if a ≤ (state n a h).σ j then (1 : ℝ) else 0)) T [] :=
        val_mono (probeIdx (M := M) n a) hp T [] (fun h' _ => hdom h')
    _ = ∑ j ∈ Lᶜ, val (poolResp L ρ) (probeIdx (M := M) n a)
          (fun h => if a ≤ (state n a h).σ j then (1 : ℝ) else 0) T [] :=
        val_sum (poolResp L ρ) (probeIdx (M := M) n a) Lᶜ
          (fun j h => if a ≤ (state n a h).σ j then (1 : ℝ) else 0) T []
    _ ≤ ∑ _j ∈ Lᶜ, Real.exp (-((a : ℝ) * ℓ)) := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        exact error_tail ρ ℓ hρ0 hρ1 hexp hℓ0 (poolResp L ρ) hp j
          (by rw [poolResp, if_neg (by simpa using hj)]) T
    _ = ((M - n : ℕ) : ℝ) * Real.exp (-((a : ℝ) * ℓ)) := by
        rw [Finset.sum_const, Finset.card_compl, hL, Fintype.card_fin, nsmul_eq_mul]

/-- **Step (f), finitary form.** The sieve has not terminated within `T` probes with probability
at most `costBound/T`; so it terminates almost surely. -/
theorem sieve_not_halted (ρ ℓ A : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hexp : Real.exp ℓ = (1 - ρ) / ρ) (hℓ0 : 0 < ℓ) (L : Finset (Fin M)) (hL : L.card = n)
    (hn : 0 < n) (hnM : n ≤ M) (ha0 : 0 ≤ a) (haA : (a : ℝ) * ℓ ≤ A + ℓ) (T : ℕ) (hT : 0 < T) :
    val (poolResp L ρ) (probeIdx (M := M) n a)
        (fun h => if n ≤ (conf a (state (M := M) n a h)).card then (0 : ℝ) else 1) T []
      ≤ costBound M n ρ ℓ A / T := by
  have hp := poolResp_mem_Icc L hρ0 hρ1
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hdom : ∀ h' : List Bool, h'.length = T →
      (if n ≤ (conf a (state (M := M) n a h')).card then (0 : ℝ) else 1)
      ≤ 0 + (1 / (T : ℝ)) * ∑ j, ((state (M := M) n a h').N j : ℝ) := by
    intro h' hlen
    have hnn : (0 : ℝ) ≤ ∑ j, ((state (M := M) n a h').N j : ℝ) :=
      Finset.sum_nonneg (fun j _ => by positivity)
    by_cases hh : n ≤ (conf a (state (M := M) n a h')).card
    · rw [if_pos hh, zero_add]
      positivity
    · rw [if_neg hh, zero_add]
      have := sumN_eq (M := M) (n := n) (a := a) h' hh
      have hcast : ∑ j, ((state (M := M) n a h').N j : ℝ) = (T : ℝ) := by
        rw [← hlen, ← this]; push_cast; ring
      rw [hcast]
      apply le_of_eq
      field_simp
  have hmono := val_mono (probeIdx (M := M) n a) hp
    (F := fun h => if n ≤ (conf a (state (M := M) n a h)).card then (0 : ℝ) else 1)
    (G := fun h => 0 + (1 / (T : ℝ)) * ∑ j, ((state (M := M) n a h).N j : ℝ)) T []
    (fun h' hl => hdom h' (by simpa using hl))
  rw [val_affine] at hmono
  have hcost := sieve_cost (a := a) ρ ℓ A hρ0 hρ1 hexp hℓ0 L hL hn hnM ha0 haA T
  rw [div_eq_inv_mul, ← one_div]
  have hpos : (0 : ℝ) ≤ 1 / (T : ℝ) := by positivity
  nlinarith [hmono, hcost]

/-- **Proposition 4.4.2, correctness.** The confirmed set differs from the enrolled list with
probability at most `(M−n)e^{−aℓ} + costBound/T`; the second term is the truncation at horizon
`T` and vanishes as `T → ∞`. -/
theorem sieve_correct (ρ ℓ A : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hexp : Real.exp ℓ = (1 - ρ) / ρ) (hℓ0 : 0 < ℓ) (L : Finset (Fin M)) (hL : L.card = n)
    (hn : 0 < n) (hnM : n ≤ M) (ha0 : 0 ≤ a) (haA : (a : ℝ) * ℓ ≤ A + ℓ) (T : ℕ) (hT : 0 < T) :
    val (poolResp L ρ) (probeIdx (M := M) n a)
        (fun h => if conf a (state n a h) = L then (0 : ℝ) else 1) T []
      ≤ ((M - n : ℕ) : ℝ) * Real.exp (-((a : ℝ) * ℓ)) + costBound M n ρ ℓ A / T := by
  have hp := poolResp_mem_Icc L hρ0 hρ1
  have hdom : ∀ h' : List Bool,
      (if conf a (state n a h') = L then (0 : ℝ) else 1)
      ≤ (if ∃ j ∈ Lᶜ, a ≤ (state n a h').σ j then (1 : ℝ) else 0)
        + (if n ≤ (conf a (state (M := M) n a h')).card then (0 : ℝ) else 1) := by
    intro h'
    by_cases heq : conf a (state n a h') = L
    · rw [if_pos heq]
      have h1 : (0 : ℝ) ≤ if ∃ j ∈ Lᶜ, a ≤ (state n a h').σ j then (1 : ℝ) else 0 := by
        split_ifs <;> norm_num
      have h2 : (0 : ℝ) ≤ if n ≤ (conf a (state (M := M) n a h')).card then (0 : ℝ) else 1 := by
        split_ifs <;> norm_num
      linarith
    · rw [if_neg heq]
      by_cases hex : ∃ j ∈ Lᶜ, a ≤ (state n a h').σ j
      · rw [if_pos hex]
        have h2 : (0 : ℝ) ≤ if n ≤ (conf a (state (M := M) n a h')).card then (0 : ℝ) else 1 := by
          split_ifs <;> norm_num
        linarith
      · by_cases hh : n ≤ (conf a (state (M := M) n a h')).card
        · exfalso
          push Not at hex
          have hsub : conf a (state n a h') ⊆ L := by
            intro j hj
            by_contra hjL
            exact absurd (mem_conf.1 hj) (not_le.2 (hex j (by simpa using hjL)))
          exact heq (Finset.eq_of_subset_of_card_le hsub (by rw [hL]; exact hh))
        · rw [if_neg hh, if_neg hex]
          norm_num
  have hmono := val_mono (probeIdx (M := M) n a) hp
    (F := fun h => if conf a (state n a h) = L then (0 : ℝ) else 1)
    (G := fun h => (if ∃ j ∈ Lᶜ, a ≤ (state n a h).σ j then (1 : ℝ) else 0)
      + (if n ≤ (conf a (state (M := M) n a h)).card then (0 : ℝ) else 1)) T []
    (fun h' _ => hdom h')
  rw [val_add] at hmono
  have h1 := sieve_error (a := a) ρ ℓ hρ0 hρ1 hexp hℓ0 L hL T
  have h2 := sieve_not_halted (a := a) ρ ℓ A hρ0 hρ1 hexp hℓ0 L hL hn hnM ha0 haA T hT
  linarith

/-- With the note's `A = log((M−n)/δ)`, the error term of `sieve_error` is exactly `δ`. -/
lemma err_eq_delta (δ : ℝ) (hδ : 0 < δ) (hMn : 0 < (M - n : ℕ)) :
    ((M - n : ℕ) : ℝ) * Real.exp (-(Real.log (((M - n : ℕ) : ℝ) / δ))) = δ := by
  have hM0 : (0 : ℝ) < ((M - n : ℕ) : ℝ) := by exact_mod_cast hMn
  have hpos : (0 : ℝ) < ((M - n : ℕ) : ℝ) / δ := by positivity
  rw [Real.exp_neg, Real.exp_log hpos, inv_div]
  field_simp

/-- **Proposition 4.4.2, as stated.** With `A = log((M−n)/δ)` and the confirmation level
`a = ⌈A/ℓ_ρ⌉`, the sieve outputs the enrolled list except with probability at most
`δ + costBound/T`, and issues at most `costBound` probes in expectation; the `costBound/T` term
is the truncation at horizon `T` and vanishes as `T → ∞`. -/
theorem sieve_prop442 (ρ ℓ δ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hexp : Real.exp ℓ = (1 - ρ) / ρ) (hℓ0 : 0 < ℓ) (hδ : 0 < δ) (L : Finset (Fin M))
    (hL : L.card = n) (hn : 0 < n) (hnM : n ≤ M) (hMn : 0 < (M - n : ℕ))
    (A : ℝ) (hA : A = Real.log (((M - n : ℕ) : ℝ) / δ))
    (ha0 : 0 ≤ a) (haA1 : A ≤ (a : ℝ) * ℓ) (haA2 : (a : ℝ) * ℓ ≤ A + ℓ) (T : ℕ) (hT : 0 < T) :
    val (poolResp L ρ) (probeIdx (M := M) n a) (fun h => ∑ j, ((state (M := M) n a h).N j : ℝ))
        T [] ≤ costBound M n ρ ℓ A ∧
    val (poolResp L ρ) (probeIdx (M := M) n a)
        (fun h => if conf a (state (M := M) n a h) = L then (0 : ℝ) else 1) T []
      ≤ δ + costBound M n ρ ℓ A / T := by
  refine ⟨sieve_cost (a := a) ρ ℓ A hρ0 hρ1 hexp hℓ0 L hL hn hnM ha0 haA2 T, ?_⟩
  have h := sieve_correct (a := a) ρ ℓ A hρ0 hρ1 hexp hℓ0 L hL hn hnM ha0 haA2 T hT
  have hM0 : (0 : ℝ) ≤ ((M - n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmono : ((M - n : ℕ) : ℝ) * Real.exp (-((a : ℝ) * ℓ))
      ≤ ((M - n : ℕ) : ℝ) * Real.exp (-A) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hM0
  have hδ' : ((M - n : ℕ) : ℝ) * Real.exp (-A) = δ := by
    rw [hA]; exact err_eq_delta (n := n) δ hδ hMn
  linarith

end Main

end Process

/-! ### The bridge to the oracle: a `thr`-separated pool under K1(ρ)

The abstract results above are about the process `val pJ (probeIdx n a)`, where `pJ j` is the
probability that probing pool point `j` answers `1`.  Under the K1(ρ) kernel and `thr`-separation
of the pool, that is exactly the oracle's response law (`resp_poolPt`), so the bounds transfer
verbatim to `Gallery.resp` — this is the step the note justifies by "each probe at `h_j` is, given
the past, a fresh Bernoulli whose parameter depends only on whether `j` is listed". -/

section Oracle

open OracleBounds.GeneralPrior

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Pool point `j` as a point of the sphere. -/
def poolPt (G : Gallery E ι (Fin M)) (j : Fin M) : Sph E := ⟨G.g j, G.hg j⟩

/-- Reindexing `val` along a map on probes. -/
lemma val_comp {X Y : Type*} (p : Y → ℝ) (f : X → Y) (probe : List Bool → X)
    (F : List Bool → ℝ) : ∀ (r : ℕ) (h : List Bool),
      val p (fun h' => f (probe h')) F r h = val (fun x => p (f x)) probe F r h := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    rw [val_succ, val_succ, ih, ih]

/-- **The K1(ρ) response law of a `thr`-separated pool**: probing pool point `j` answers `1` with
probability `1 − ρ` if `j` is enrolled and `ρ` otherwise. -/
lemma resp_poolPt (G : Gallery E ι (Fin M)) (ρ : ℝ) (hthr1 : G.thr < 1)
    (hκq : ∀ s ≤ G.thr, G.κ s = ρ) (hκl : ∀ s, G.thr < s → G.κ s = 1 - ρ)
    (hsep : ∀ j j' : Fin M, j ≠ j' → inner ℝ (G.g j) (G.g j') ≤ G.thr)
    (v : ι → Fin M) (j : Fin M) :
    G.resp v (poolPt G j) = poolResp (Finset.univ.image v) ρ j := by
  have key : G.thr < G.score v (poolPt G j) ↔ ∃ i, v i = j := by
    unfold Gallery.score
    rw [Finset.lt_sup'_iff]
    constructor
    · rintro ⟨i, -, hi⟩
      refine ⟨i, ?_⟩
      by_contra hne
      exact absurd hi (not_lt.2 (hsep j (v i) (fun hc => hne hc.symm)))
    · rintro ⟨i, hi⟩
      refine ⟨i, Finset.mem_univ _, ?_⟩
      show G.thr < inner ℝ (G.g j) (G.g (v i))
      rw [hi, real_inner_self_eq_norm_sq, G.hg, one_pow]
      exact hthr1
  have hmem : j ∈ Finset.univ.image v ↔ ∃ i, v i = j := by simp
  unfold Gallery.resp poolResp
  by_cases hj : ∃ i, v i = j
  · rw [hκl _ (key.2 hj), if_pos (hmem.2 hj)]
  · rw [hκq _ (not_lt.1 (fun hc => hj (key.1 hc))), if_neg (fun hc => hj (hmem.1 hc))]

/-- **Proposition 4.4.2 in the oracle model.** The sieve run against the real one-bit oracle with
the K1(ρ) kernel on a `thr`-separated pool whose enrolled list `v` is injective:
(i) the expected number of probes in the first `T` rounds obeys the note's bound; (ii) the
confirmed set is the enrolled list except with probability `≤ (M−n)e^{−aℓ} + costBound/T`. -/
theorem gallery_sieve [NeZero M] (G : Gallery E ι (Fin M)) (v : ι → Fin M)
    (hv : Function.Injective v) (ρ ℓ A : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hexp : Real.exp ℓ = (1 - ρ) / ρ) (hℓ0 : 0 < ℓ) (hthr1 : G.thr < 1)
    (hκq : ∀ s ≤ G.thr, G.κ s = ρ) (hκl : ∀ s, G.thr < s → G.κ s = 1 - ρ)
    (hsep : ∀ j j' : Fin M, j ≠ j' → inner ℝ (G.g j) (G.g j') ≤ G.thr)
    (a : ℤ) (ha0 : 0 ≤ a) (haA : (a : ℝ) * ℓ ≤ A + ℓ) (hnM : Fintype.card ι ≤ M)
    (T : ℕ) (hT : 0 < T) :
    val (G.resp v) (fun h => poolPt G (probeIdx (M := M) (Fintype.card ι) a h))
        (fun h => ∑ j, ((state (M := M) (Fintype.card ι) a h).N j : ℝ)) T []
      ≤ costBound M (Fintype.card ι) ρ ℓ A ∧
    val (G.resp v) (fun h => poolPt G (probeIdx (M := M) (Fintype.card ι) a h))
        (fun h => if conf a (state (M := M) (Fintype.card ι) a h) = Finset.univ.image v
          then (0 : ℝ) else 1) T []
      ≤ ((M - Fintype.card ι : ℕ) : ℝ) * Real.exp (-((a : ℝ) * ℓ))
        + costBound M (Fintype.card ι) ρ ℓ A / T := by
  have hresp : (fun x => G.resp v (poolPt G x)) = poolResp (Finset.univ.image v) ρ := by
    funext j; exact resp_poolPt G ρ hthr1 hκq hκl hsep v j
  have hL : (Finset.univ.image v).card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ hv, Finset.card_univ]
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  constructor
  · rw [val_comp (G.resp v) (poolPt G) (probeIdx (M := M) (Fintype.card ι) a), hresp]
    exact sieve_cost (a := a) ρ ℓ A hρ0 hρ1 hexp hℓ0 (Finset.univ.image v) hL hn hnM ha0 haA T
  · rw [val_comp (G.resp v) (poolPt G) (probeIdx (M := M) (Fintype.card ι) a), hresp]
    exact sieve_correct (a := a) ρ ℓ A hρ0 hρ1 hexp hℓ0 (Finset.univ.image v) hL hn hnM ha0 haA
      T hT

end Oracle

end Sieve

end OracleBounds.Attacks
