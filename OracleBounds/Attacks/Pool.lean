import OracleBounds.GeneralPrior.Pool

/-!
# The pool attack, noiseless kernel (K0)

**Statements reviewed and signed off by the administrator (2026-09-20).**

Setting: the pool prior of `OracleBounds.GeneralPrior.Pool` — the `n` enrolled faces are pool
points, `Fine = Fin M`, embedding `G.g : Fin M → E` (the pool `cust`). Hypotheses:

* **K0**: `κ s = 1{thr < s}` (`hκ`), with `thr < 1` (`hthr1`);
* the pool is **`thr`-separated**: `⟨g j, g j'⟩ ≤ thr` for `j ≠ j'` (`hsep`).

The attack (`poolProbe`/`poolOut`): round `k` probes pool point `k` (independent of the
transcript), budget `Q = M`; the output list has `k_out = M` slots, slot `j` holding pool point
`j` when its answer bit was `1` and a dummy `x₀` otherwise.

Results:

* `resp_custS` — the answer to probing pool point `j` is `1` iff some enrolled face *is* `j`;
* `pathProb_pool` — the transcript law is the point mass at `memInd v`, the membership indicator
  of the enrolled list (`memInd v j = true ↔ ∃ i, v i = j`, i.e. the loud set is *exactly* the
  enrolled set: no false positives, no misses);
* `pool_Ncount` — at that transcript every face is recovered at `ε = 0`: `N₀ = n`;
* `pool_PN` — hence `P[N₀ ≥ n] = 1` for every prior `π` on the pool (i.i.d. or not: the
  statement is per-list, so it also covers sampling without replacement via `pool_PN_list`).

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.Attacks

open Finset OracleBounds.V6 OracleBounds.GeneralPrior

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {M : ℕ} [NeZero M] (G : Gallery E ι (Fin M))

/-- Pool point `j` as a point of the sphere. -/
def custS (j : Fin M) : Sph E := ⟨G.g j, G.hg j⟩

/-- **Probe rule.** Round `k` (history of length `k`) probes pool point `k`, independently of the
answers so far. After `M` rounds (never reached with budget `M`) it probes pool point `0`. -/
def poolProbe (h : List Bool) : Sph E :=
  if hl : h.length < M then custS G ⟨h.length, hl⟩ else custS G 0

/-- **Output rule.** Slot `j` holds pool point `j` if its answer bit was `1`, else the dummy `x₀`. -/
def poolOut (x₀ : Sph E) (e : Fin M → Bool) (j : Fin M) : Sph E :=
  if e j then custS G j else x₀

/-- Membership indicator of the enrolled list `v`, indexed by `ℕ` (used in the induction). -/
def memIndN (v : ι → Fin M) (k : ℕ) : Bool := decide (∃ i, (v i : ℕ) = k)

/-- Membership indicator of the enrolled list `v`: the transcript the attack observes. -/
def memInd (v : ι → Fin M) (j : Fin M) : Bool := decide (∃ i, v i = j)

lemma memInd_iff (v : ι → Fin M) (j : Fin M) : memInd v j = true ↔ ∃ i, v i = j := by
  simp [memInd]

lemma memIndN_val (v : ι → Fin M) (j : Fin M) : memIndN v j = memInd v j := by
  simp [memIndN, memInd, Fin.ext_iff]

lemma bern_ind (p : Prop) [Decidable p] (b : Bool) :
    bern (if p then (1 : ℝ) else 0) b = if b = decide p then 1 else 0 := by
  cases b <;> by_cases hp : p <;> simp [bern, hp]

section K0

variable (hκ : ∀ s, G.κ s = if G.thr < s then 1 else 0) (hthr1 : G.thr < 1)
  (hsep : ∀ j j' : Fin M, j ≠ j' → inner ℝ (G.g j) (G.g j') ≤ G.thr)

include hκ hthr1 hsep

/-- Under K0 and `thr`-separation, probing pool point `j` answers `1` iff some enrolled face is
`j`. -/
lemma resp_custS (v : ι → Fin M) (j : Fin M) :
    G.resp v (custS G j) = if ∃ i, v i = j then 1 else 0 := by
  have key : G.thr < G.score v (custS G j) ↔ ∃ i, v i = j := by
    unfold Gallery.score
    rw [Finset.lt_sup'_iff]
    constructor
    · rintro ⟨i, -, hi⟩
      refine ⟨i, ?_⟩
      by_contra hne
      have := hsep j (v i) (fun h => hne h.symm)
      exact absurd hi (not_lt.2 this)
    · rintro ⟨i, hi⟩
      refine ⟨i, Finset.mem_univ _, ?_⟩
      show G.thr < inner ℝ (G.g j) (G.g (v i))
      rw [hi, real_inner_self_eq_norm_sq, G.hg, one_pow]
      exact hthr1
  unfold Gallery.resp
  rw [hκ]
  by_cases h : ∃ i, v i = j
  · rw [if_pos (key.2 h), if_pos h]
  · rw [if_neg (fun h' => h (key.1 h')), if_neg h]

/-- The transcript law of the pool attack is deterministic: from a history of length `k`, the
next `r` bits are the membership indicators of pool points `k, …, k + r − 1`. -/
lemma pathProb_pool (v : ι → Fin M) : ∀ (r : ℕ) (h : List Bool), h.length + r ≤ M →
    ∀ e : Fin r → Bool, pathProb (G.resp v) (poolProbe G) r h e =
      if (∀ t : Fin r, e t = memIndN v (h.length + t)) then 1 else 0
  | 0, h, _, e => by simp [pathProb]
  | r + 1, h, hr, e => by
    have hl : h.length < M := by omega
    rw [pathProb, pathProb_pool v r (h ++ [e 0]) (by simp; omega) (Fin.tail e)]
    have hp : poolProbe G h = custS G ⟨h.length, hl⟩ := by
      unfold poolProbe; rw [dif_pos hl]
    rw [hp, resp_custS G hκ hthr1 hsep v, bern_ind]
    have hm : decide (∃ i, v i = (⟨h.length, hl⟩ : Fin M)) = memIndN v h.length := by
      simp [memIndN, Fin.ext_iff]
    rw [hm]
    simp only [Fin.forall_fin_succ, List.length_append, List.length_singleton, Fin.tail,
      Fin.val_succ, Fin.val_zero, add_zero]
    have harith : ∀ t : Fin r, h.length + 1 + (t : ℕ) = h.length + ((t : ℕ) + 1) := fun t => by
      ring
    simp only [harith]
    by_cases h0 : e 0 = memIndN v h.length <;>
      by_cases h1 : ∀ t : Fin r, e t.succ = memIndN v (h.length + ((t : ℕ) + 1)) <;>
      simp [h0, h1]

/-- **Transcript.** With budget `M` from the empty history, the transcript is `memInd v` with
probability one. -/
theorem pathProb_pool_full (v : ι → Fin M) (e : Fin M → Bool) :
    pathProb (G.resp v) (poolProbe G) M [] e = if e = memInd v then 1 else 0 := by
  rw [pathProb_pool G hκ hthr1 hsep v M [] (by simp)]
  have : (∀ t : Fin M, e t = memIndN v (([] : List Bool).length + t)) ↔ e = memInd v := by
    simp only [List.length_nil, zero_add]
    constructor
    · intro h; funext t; rw [h t, memIndN_val]
    · intro h t; rw [h, memIndN_val]
  by_cases h : e = memInd v
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h]

end K0

/-- At the transcript `memInd v`, every enrolled face is recovered exactly (`ε = 0`): `N₀ = n`.
(This needs no hypothesis on the kernel: it is a statement about the output rule.) -/
theorem pool_Ncount (x₀ : Sph E) (v : ι → Fin M) :
    G.Ncount (poolOut G x₀) 0 v (memInd v) = Fintype.card ι := by
  classical
  unfold Gallery.Ncount
  rw [Finset.filter_true_of_mem, Finset.card_univ]
  intro i _
  refine ⟨v i, ?_⟩
  have h : memInd v (v i) = true := (memInd_iff v (v i)).2 ⟨i, rfl⟩
  simp [poolOut, h, custS]

section K0

variable (hκ : ∀ s, G.κ s = if G.thr < s then 1 else 0) (hthr1 : G.thr < 1)
  (hsep : ∀ j j' : Fin M, j ≠ j' → inner ℝ (G.g j) (G.g j') ≤ G.thr)

include hκ hthr1 hsep

/-- **Per-list guarantee.** For every enrolled list `v`, the pool attack recovers all `n` faces
exactly with probability one. -/
theorem pool_PN_list (x₀ : Sph E) (v : ι → Fin M) :
    ∑ e, pathProb (G.resp v) (poolProbe G) M [] e *
      (if (Fintype.card ι : ℝ) ≤ G.Ncount (poolOut G x₀) 0 v e then (1 : ℝ) else 0) = 1 := by
  simp_rw [pathProb_pool_full G hκ hthr1 hsep v]
  rw [Finset.sum_eq_single (memInd v)]
  · rw [if_pos rfl, pool_Ncount, if_pos le_rfl, one_mul]
  · intro e _ he; rw [if_neg he, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The pool attack recovers the whole list** (K0, `thr`-separated pool): `P[N₀ ≥ n] = 1`, for
any prior `π` on the pool, with `Q = M` probes and `k_out = M` outputs. -/
theorem pool_PN (x₀ : Sph E) :
    G.PN (poolProbe G) (poolOut G x₀) 0 (Fintype.card ι) = 1 := by
  classical
  unfold Gallery.PN Gallery.wt
  have h : ∀ v : ι → Fin M, ∑ e, G.prior v * pathProb (G.resp v) (poolProbe G) M [] e *
      (if (Fintype.card ι : ℝ) ≤ G.Ncount (poolOut G x₀) 0 v e then (1 : ℝ) else 0) =
      G.prior v := by
    intro v
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [pool_PN_list G hκ hthr1 hsep x₀ v, mul_one]
  simp_rw [h]
  exact G.prior_sum

end K0

end OracleBounds.Attacks
