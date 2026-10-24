import OracleBounds.Attacks.Localise2
import OracleBounds.GeneralPrior.LiveCapture
import OracleBounds.GeneralPrior.BudgetBest

/-!
# Random search + L2 bisection, general prior (scaffold)

**Statements reviewed and signed off by the administrator (2026-10-14)**: the attack `Atk`/`stepA`/`Fof`,
`Bad`, `Neps`, `queries`, `EK` and `thm63_markov` match `briefs/attacks/random-search-general-prior.md` §9
(Theorem 6.3 at `W = E`, kernel K0, finite probe support, Markov branch). Added conditions accepted:
`0 ≤ γ`, `0 < K`, `εL ≤ ε`, `εL < 1`.

Source: `briefs/attacks/random-search-general-prior.md` (locked paper statement). This file holds
only the parts that do not depend on the failure accounting of §3:

1. **Transcript coupling** (`resp_eq_one_of_reach`, `resp_eq_zero_of_noReach`,
   `resp_eq_oneFace`, `pathProb_eq_oneFace`, `val_clean_eq_oneFace`): under the noiseless kernel
   K0, along any path on which no probe reaches an entry `j ≠ i`, the transcript law under the
   real oracle `G.resp V` equals that under the one-face oracle for entry `i`.
2. **Attribution** (`attribution`): `‖ĝ − g‖ ≤ ε`, `thr < ⟨x,g⟩` ⇒ `thr − ε < ⟨x,ĝ⟩`.
3. **Definitions** of the attack `A(ν, c, ε, K, M)` of §2: `bstate`/`L2probe`/`L2fromAns`
   (L2 rewritten as an answer-driven probe rule), the state machine `St`/`step`/`stateOf`, the
   probe rule `rsProbe` and the output rule `rsOut`. Nothing is proved about them yet except
   `bisect_eq_bstate` (the bisection building block of the L2 correspondence).
4. **L2 correspondence and unit vectors** (§4, proofs by subagent, statements not yet signed off):
   `L2fromAns_L2run` (`L2fromAns … (L2run … orc) = L2 … orc` for every oracle `orc`);
   `norm_L2probe`/`toSph_L2probe` (every L2 probe is a unit vector under an orthonormal frame),
   `norm_L2fromAns`/`toSph_L2fromAns` (the output is a unit vector when `g' = L2raw … ≠ 0`),
   `L2raw_ne_zero` (orthonormal frame and `â ≠ 0` ⇒ `g' ≠ 0`).
5. **Theorem 6.3 at `W = E`, Markov branch** (the brief's §9 target; proof by subagent,
   **statement UNSIGNED**): `thm63_markov`. The attack is defined directly as a deterministic
   run over search rounds (`stepA`/`Fof`, L2 run against the real K0 oracle `orcK0` per launch;
   output made a unit vector by `toSph dflt`, convention (A2)), *not* through `rsProbe`/`rsOut`;
   `resp_eq_orcK0` ties `orcK0` to `Gallery.resp` under K0. Expectations are finite sums
   (`EK` over `xs : Fin K → X` with weights `∏ ν`, `Gallery.prior` over `V`). Lemma list of §9:
   `lemma4'`, `lemma5`, `lemma6_rate`/`lemma6_Delta`/`lemma6_Z`, `lemma7_stage`/`lemma7`,
   `lemma8`, `Neps_ge` + assembly; `queries_le` (at most `K + M·Q_loc` queries).
   Hypotheses beyond the brief's (H1)–(H5): `0 ≤ γ`, `0 < K`, L2 accuracy `εL ∈ (0, min(ε,1))`.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.Attacks.RandomSearch

open Finset OracleBounds.V6 OracleBounds.GeneralPrior OracleBounds.Attacks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## 1. Transcript coupling under K0 -/

section Coupling

variable {ι Fine : Type*} [Fintype ι] [Fintype Fine] [Nonempty ι] (G : Gallery E ι Fine)

/-- The one-face noiseless oracle for entry `i` of `V`. -/
noncomputable def oneFace (V : ι → Fine) (i : ι) (y : Sph E) : ℝ :=
  if G.thr < inner ℝ y.1 (G.g (V i)) then 1 else 0

lemma thr_lt_score_iff (V : ι → Fine) (x : Sph E) :
    G.thr < G.score V x ↔ ∃ j, G.thr < inner ℝ x.1 (G.g (V j)) := by
  unfold Gallery.score
  rw [Finset.lt_sup'_iff]
  simp

variable (hκ : ∀ s, G.κ s = if G.thr < s then 1 else 0)
include hκ

/-- K0: a probe reaching entry `i` is answered `1` (whatever the other entries do). -/
theorem resp_eq_one_of_reach (V : ι → Fine) (i : ι) (x : Sph E)
    (hi : G.thr < inner ℝ x.1 (G.g (V i))) : G.resp V x = 1 := by
  unfold Gallery.resp
  rw [hκ, if_pos ((thr_lt_score_iff G V x).2 ⟨i, hi⟩)]

/-- K0: a probe reaching no entry is answered `0`. -/
theorem resp_eq_zero_of_noReach (V : ι → Fine) (x : Sph E)
    (h : ∀ j, inner ℝ x.1 (G.g (V j)) ≤ G.thr) : G.resp V x = 0 := by
  unfold Gallery.resp
  rw [hκ, if_neg (fun hc => by
    obtain ⟨j, hj⟩ := (thr_lt_score_iff G V x).1 hc
    exact absurd hj (not_lt.2 (h j)))]

/-- K0: a probe reaching no entry other than `i` gets the one-face answer for `i`. -/
theorem resp_eq_oneFace (V : ι → Fine) (i : ι) (x : Sph E)
    (h : ∀ j, j ≠ i → inner ℝ x.1 (G.g (V j)) ≤ G.thr) :
    G.resp V x = oneFace G V i x := by
  unfold oneFace
  by_cases hi : G.thr < inner ℝ x.1 (G.g (V i))
  · rw [if_pos hi, resp_eq_one_of_reach G hκ V i x hi]
  · rw [if_neg hi]
    refine resp_eq_zero_of_noReach G hκ V x (fun j => ?_)
    by_cases hj : j = i
    · subst hj; exact not_lt.1 hi
    · exact h j hj

/-- **Transcript coupling, pathwise.** From history `h`, if none of the `r` probes issued along
the continuation `e` reaches an entry `j ≠ i`, then `e` has the same probability under the real
oracle and under the one-face oracle for `i`. -/
theorem pathProb_eq_oneFace (V : ι → Fine) (i : ι) (probe : List Bool → Sph E) :
    ∀ (r : ℕ) (h : List Bool) (e : Fin r → Bool),
      (∀ k < r, ∀ j, j ≠ i →
        inner ℝ (probe ((h ++ List.ofFn e).take (h.length + k))).1 (G.g (V j)) ≤ G.thr) →
      pathProb (G.resp V) probe r h e = pathProb (oneFace G V i) probe r h e := by
  intro r
  induction r with
  | zero => intro h e _; rfl
  | succ r ih =>
    intro h e hni
    have hsplit : h ++ List.ofFn e = (h ++ [e 0]) ++ List.ofFn (Fin.tail e) := by
      rw [List.ofFn_succ]; simp; rfl
    have h0 : G.resp V (probe h) = oneFace G V i (probe h) := by
      refine resp_eq_oneFace G hκ V i (probe h) (fun j hj => ?_)
      have := hni 0 (Nat.succ_pos r) j hj
      rwa [add_zero, List.take_left'] at this
      rfl
    have ht := ih (h ++ [e 0]) (Fin.tail e) (fun k hk j hj => by
      have := hni (k + 1) (by omega) j hj
      rw [hsplit] at this
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)
    simp only [pathProb, h0, ht]

/-- The no-interference event for entry `i` along a full history `h'`: no probe issued along
`h'` reaches an entry `j ≠ i`. -/
def Clean (V : ι → Fine) (i : ι) (probe : List Bool → Sph E) (h' : List Bool) : Prop :=
  ∀ k < h'.length, ∀ j, j ≠ i → inner ℝ (probe (h'.take k)).1 (G.g (V j)) ≤ G.thr

omit hκ in
lemma pathProb_eq_oneFace_of_clean (V : ι → Fine) (i : ι) (probe : List Bool → Sph E)
    (hκ : ∀ s, G.κ s = if G.thr < s then 1 else 0)
    (r : ℕ) (e : Fin r → Bool) (hc : Clean G V i probe (List.ofFn e)) :
    pathProb (G.resp V) probe r [] e = pathProb (oneFace G V i) probe r [] e :=
  pathProb_eq_oneFace G hκ V i probe r [] e (fun k hk j hj => by
    simpa using hc k (by simpa using hk) j hj)

open Classical in
/-- **Transcript coupling, expectations.** For any transcript functional `F`, its expectation
restricted to the no-interference event is the same under the real oracle and under the
one-face oracle for `i`. -/
theorem val_clean_eq_oneFace (V : ι → Fine) (i : ι) (probe : List Bool → Sph E)
    (F : List Bool → ℝ) (r : ℕ) :
    val (G.resp V) probe (fun h' => if Clean G V i probe h' then F h' else 0) r [] =
      val (oneFace G V i) probe (fun h' => if Clean G V i probe h' then F h' else 0) r [] := by
  rw [val_eq_sum, val_eq_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases hc : Clean G V i probe ([] ++ List.ofFn e)
  · rw [pathProb_eq_oneFace_of_clean G V i probe hκ r e (by simpa using hc)]
  · simp only [if_neg hc, mul_zero]

end Coupling

/-! ## 2. Attribution (Thm 4.3.9(ii)) -/

/-- If `‖ĝ − g‖ ≤ ε`, `‖x‖ = 1` and `x` reaches `g` (`thr < ⟨x,g⟩`), then `⟨x,ĝ⟩ > thr − ε`:
a re-contact of a correctly found entry is attributed to its output. -/
theorem attribution (x g ĝ : E) (hx : ‖x‖ = 1) (thr ε : ℝ) (hgg : ‖ĝ - g‖ ≤ ε)
    (hreach : thr < inner ℝ x g) : thr - ε < inner ℝ x ĝ := by
  have hcs : |inner ℝ x (ĝ - g)| ≤ ‖x‖ * ‖ĝ - g‖ := abs_real_inner_le_norm x (ĝ - g)
  rw [hx, one_mul] at hcs
  have hsplit : inner ℝ x ĝ = inner ℝ x g + inner ℝ x (ĝ - g) := by
    rw [inner_sub_right]; ring
  have := neg_abs_le (inner ℝ x (ĝ - g))
  linarith

/-! ## 3. The attack of §2 -/

/-- Unit vector with a fallback (used only to land L2's points in `Sph E`; every point L2 forms
from an orthonormal frame is already a unit vector, so the fallback is never used there). -/
noncomputable def toSph (dflt : Sph E) (v : E) : Sph E :=
  if h : ‖v‖ = 1 then ⟨v, h⟩ else dflt

/-- Bisection state after a list of answers: starting from bracket `(a, b)`, an answer `true` at
the midpoint moves `a` there, `false` moves `b` there (exactly `bisect`'s update). -/
noncomputable def bstate : ℝ → ℝ → List Bool → ℝ × ℝ
  | a, b, [] => (a, b)
  | a, b, true :: r => bstate ((a + b) / 2) b r
  | a, b, false :: r => bstate a ((a + b) / 2) r

/-- Midpoint of a bracket: the next bisection query. -/
noncomputable def mid (p : ℝ × ℝ) : ℝ := (p.1 + p.2) / 2

/-- The answers `bisect f k a b` receives. -/
noncomputable def bisectAns (f : ℝ → Bool) : ℕ → ℝ → ℝ → List Bool
  | 0, _, _ => []
  | k + 1, a, b =>
      f ((a + b) / 2) ::
        (if f ((a + b) / 2) then bisectAns f k ((a + b) / 2) b else bisectAns f k a ((a + b) / 2))

/-- `bisect` is `bstate` fed with its own answers. -/
theorem bisect_eq_bstate (f : ℝ → Bool) :
    ∀ (k : ℕ) (a b : ℝ), bisect f k a b = bstate a b (bisectAns f k a b) := by
  intro k
  induction k with
  | zero => intro a b; rfl
  | succ k ih =>
    intro a b
    simp only [bisect, bisectAns]
    by_cases hf : f ((a + b) / 2) = true
    · simp only [hf, if_true, bstate, ih]
    · simp only [Bool.not_eq_true] at hf
      simp only [hf, bstate, ih, Bool.false_eq_true, if_false]

/-! ### L2's constants (copied verbatim from the `let`s of `Attacks.L2`) -/

section L2consts

variable (m : ℕ) (t ε c : ℝ)

noncomputable def w₀ : ℝ := Real.arccos (t / (t + c))
noncomputable def Θ₀ : ℝ := Real.arccos (t + c) + Real.arccos t
noncomputable def Θ : ℝ := 2 * Real.arccos t
noncomputable def kb : ℕ :=
  let s₀ := min (Real.sin (w₀ t c)) (Real.sin (Θ₀ t c))
  let e := ε / ((1 + ε) * Real.sqrt (m + 2))
  let η := (m + 1) * s₀ * e / (m + 2)
  ⌈Real.logb 2 ((Θ₀ t c - w₀ t c) / η)⌉₊
noncomputable def ka : ℕ :=
  let s₀ := min (Real.sin (w₀ t c)) (Real.sin (Θ₀ t c))
  let e := ε / ((1 + ε) * Real.sqrt (m + 2))
  let δ := s₀ * e / (m + 2)
  let ηa := t * δ / 4
  ⌈Real.logb 2 (Θ t / ηa)⌉₊

/-- `Q_loc = 2 k_a + m (1 + k)` (`m = d′ − 2`). -/
noncomputable def Qloc : ℕ := 2 * ka m t ε c + m * (kb m t ε c + 1)

end L2consts

/-! ### L2 as an answer-driven probe rule -/

section L2rule

variable (m : ℕ) (t ε c : ℝ) (x0 : E) (u : Fin (m + 1) → E)

/-- Point at angle `θ` on circle `j`: `cos θ · x0 + sin θ · u j`. -/
noncomputable def circ (j : Fin (m + 1)) (θ : ℝ) : E := Real.cos θ • x0 + Real.sin θ • u j

/-- **The next L2 probe**, given the answers `ans` received so far in this launch
(`ans.length < Qloc`). Layout of the `Qloc` rounds:
* rounds `[0, ka)`: circle `0`, bisection of `[0, Θ]`;
* rounds `[ka, 2ka)`: circle `0`, bisection of `[0, −Θ]`;
* for `j < m`, rounds `2ka + j(kb+1) + s`: circle `j.succ`; `s = 0` is the side query at `w₀`,
  `s ≥ 1` bisects `[w₀, Θ₀]` if that answer was `true`, else `[−w₀, −Θ₀]`.
Past `Qloc` (never used by the attack) it returns `x0`. -/
noncomputable def L2probe (ans : List Bool) : E :=
  let KA := ka m t ε c
  let KB := kb m t ε c
  let n := ans.length
  if n < KA then circ m x0 u 0 (mid (bstate 0 (Θ t) ans))
  else if n < 2 * KA then circ m x0 u 0 (mid (bstate 0 (-Θ t) (ans.drop KA)))
  else
    let r := n - 2 * KA
    let j := r / (KB + 1)
    let s := r % (KB + 1)
    if hj : j < m then
      let blk := ans.drop (2 * KA + j * (KB + 1))
      if s = 0 then circ m x0 u (Fin.succ ⟨j, hj⟩) (w₀ t c)
      else if blk.headD false then
        circ m x0 u (Fin.succ ⟨j, hj⟩) (mid (bstate (w₀ t c) (Θ₀ t c) (blk.drop 1)))
      else circ m x0 u (Fin.succ ⟨j, hj⟩) (mid (bstate (-w₀ t c) (-Θ₀ t c) (blk.drop 1)))
    else x0

/-- **L2's output** from its `Qloc` answers: `Attacks.L2`'s read-off with every `bisect … .1`
replaced by the `bstate … .1` of the corresponding answer block. -/
noncomputable def L2fromAns (ans : List Bool) : E :=
  let KA := ka m t ε c
  let KB := kb m t ε c
  let θp := (bstate 0 (Θ t) (ans.take KA)).1
  let θm := (bstate 0 (-Θ t) ((ans.drop KA).take KA)).1
  let â := t / Real.cos ((θp - θm) / 2) * Real.cos ((θp + θm) / 2)
  let b₀ := t / Real.cos ((θp - θm) / 2) * Real.sin ((θp + θm) / 2)
  let θh : Fin m → ℝ := fun j =>
    let blk := (ans.drop (2 * KA + (j : ℕ) * (KB + 1))).take (KB + 1)
    if blk.headD false then (bstate (w₀ t c) (Θ₀ t c) (blk.drop 1)).1
    else (bstate (-w₀ t c) (-Θ₀ t c) (blk.drop 1)).1
  let b : Fin (m + 1) → ℝ :=
    Fin.cases b₀ (fun j => (t - â * Real.cos (θh j)) / Real.sin (θh j))
  let g' : E := â • x0 + ∑ j, b j • u j
  ‖g'‖⁻¹ • g'

end L2rule

/-! ### The search-then-launch state machine -/

/-- State after a prefix of the transcript. -/
structure St (E : Type*) where
  /-- search rounds used so far (index of the next search point) -/
  s : ℕ
  /-- outputs so far (`F` of the brief), in launch order -/
  F : List E
  /-- `some (x0, ans)`: a launch from `x0` is in progress with answers `ans` so far -/
  launch : Option (E × List Bool)
  /-- stopped (`|F| = M`, or search budget `K` spent with no launch in progress) -/
  done : Bool

section Machine

/-- Parameters of `A(ν, c, ε, K, M)` with the coins fixed: L2 dimension parameter `m = d′ − 2`,
threshold `t`, attribution slack `εA` (the brief's `ε`), L2 accuracy `εL` (`ε`, or `ε/2` under
(H6)), margin `c`, search budget `K`, launch cap `M`, search sequence `xs`, frame rule `fr`
(launch index ↦ launch point ↦ frame), and a dummy point. -/
structure Params (E : Type*) [NormedAddCommGroup E] where
  m : ℕ
  t : ℝ
  εA : ℝ
  εL : ℝ
  c : ℝ
  K : ℕ
  M : ℕ
  xs : ℕ → Sph E
  fr : ℕ → E → Fin (m + 1) → E
  dflt : Sph E

variable (P : Params E)

noncomputable def Params.qloc : ℕ := RandomSearch.Qloc P.m P.t P.εL P.c

/-- Close a finished launch: once it has `Qloc` answers, append L2's output to `F`; stop if
`|F| = M` or the search budget is spent. -/
noncomputable def settle (st : St E) : St E :=
  match st.launch with
  | none => st
  | some (x0, ans) =>
    if P.qloc ≤ ans.length then
      let F' := st.F ++ [L2fromAns P.m P.t P.εL P.c x0 (P.fr st.F.length x0) ans]
      { s := st.s, F := F', launch := none, done := decide (P.M ≤ F'.length ∨ P.K ≤ st.s) }
    else st

open Classical in
/-- One round: update the state with the answer `b` to the probe `next st`. -/
noncomputable def step (st : St E) (b : Bool) : St E :=
  if st.done then st else
  match st.launch with
  | some (x0, ans) => settle P { st with launch := some (x0, ans ++ [b]) }
  | none =>
    let x := (P.xs st.s).1
    -- launch on an unattributed match: `b(x_s) = 1` and `⟨x_s, ĝ⟩ ≤ t − ε` for all `ĝ ∈ F`
    if b = true ∧ ∀ gh ∈ st.F, inner ℝ x gh ≤ P.t - P.εA then
      settle P { s := st.s + 1, F := st.F, launch := some (x, []), done := false }
    else { s := st.s + 1, F := st.F, launch := none, done := decide (P.K ≤ st.s + 1) }

/-- Initial state (stopped at once if `K = 0` or `M = 0`). -/
def init : St E := { s := 0, F := [], launch := none, done := decide (P.K = 0 ∨ P.M = 0) }

/-- State after transcript `h`. -/
noncomputable def stateOf (h : List Bool) : St E := h.foldl (step P) (init P)

/-- The point probed in state `st`: the next search point, the next L2 probe of the current
launch, or (once stopped) the dummy. -/
noncomputable def next (st : St E) : Sph E :=
  if st.done then P.dflt else
  match st.launch with
  | none => P.xs st.s
  | some (x0, ans) =>
      toSph P.dflt (L2probe P.m P.t P.εL P.c x0 (P.fr st.F.length x0) ans)

/-- **Probe rule** of the attack. -/
noncomputable def rsProbe (h : List Bool) : Sph E := next P (stateOf P h)

/-- Total horizon `K + M·Qloc` (the deterministic query bound of §2). -/
noncomputable def horizon : ℕ := P.K + P.M * P.qloc

/-- **Output rule**: slot `j` holds the `j`-th output of `F` (made a unit vector; L2's output
already is one), padded with the dummy. -/
noncomputable def rsOut (e : Fin (horizon P) → Bool) (j : Fin P.M) : Sph E :=
  let F := (stateOf P (List.ofFn e)).F
  if hj : (j : ℕ) < F.length then toSph P.dflt (F.get ⟨j, hj⟩) else P.dflt

end Machine


/-! ## 4. L2 correspondence and unit vectors -/

section L2corr

/-- Answers received by an answer-driven probe rule `pr` against the oracle `orc` in `n` rounds:
`runP 0 = []`, `runP (n+1) = runP n ++ [orc (pr (runP n))]`. -/
def runP {α : Type*} (pr : List Bool → α) (orc : α → Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => runP pr orc n ++ [orc (pr (runP pr orc n))]

lemma runP_length {α : Type*} (pr : List Bool → α) (orc : α → Bool) :
    ∀ n, (runP pr orc n).length = n
  | 0 => rfl
  | n + 1 => by simp [runP, runP_length pr orc n]

lemma runP_prefix {α : Type*} (pr : List Bool → α) (orc : α → Bool) (n : ℕ) :
    ∀ k, ∃ l, runP pr orc (n + k) = runP pr orc n ++ l
  | 0 => ⟨[], by simp⟩
  | k + 1 => by
    obtain ⟨l, hl⟩ := runP_prefix pr orc n k
    exact ⟨l ++ [orc (pr (runP pr orc (n + k)))], by
      rw [← Nat.add_assoc, runP, ← List.append_assoc, ← hl]⟩

/-- Block lemma: if on the `k` rounds after round `s` the rule `pr` asks (through `orc`) exactly
what `q` asks (through `orc'`) of the answers received since round `s`, the answers of those
rounds are `q`'s. -/
lemma runP_block {α β : Type*} (pr : List Bool → α) (orc : α → Bool) (q : List Bool → β)
    (orc' : β → Bool) (s k : ℕ)
    (h : ∀ l : List Bool, l.length < k → orc (pr (runP pr orc s ++ l)) = orc' (q l)) :
    ∀ i ≤ k, runP pr orc (s + i) = runP pr orc s ++ runP q orc' i := by
  intro i
  induction i with
  | zero => intro _; simp [runP]
  | succ i ih =>
    intro hi
    rw [← Nat.add_assoc, runP, ih (by omega), h _ (by rw [runP_length]; omega), runP,
      List.append_assoc]

/-- First answer peeled off. -/
lemma runP_succ_cons {α : Type*} (q q' : List Bool → α) (orc : α → Bool)
    (h0 : ∀ l, q (orc (q []) :: l) = q' l) :
    ∀ n, runP q orc (n + 1) = orc (q []) :: runP q' orc n
  | 0 => by simp [runP]
  | n + 1 => by
    have ih := runP_succ_cons q q' orc h0 n
    show runP q orc (n + 1) ++ [orc (q (runP q orc (n + 1)))] =
      orc (q []) :: (runP q' orc n ++ [orc (q' (runP q' orc n))])
    rw [ih, h0]; rfl

/-- `bisectAns` is the run of the midpoint probe rule. -/
lemma bisectAns_eq_runP (f : ℝ → Bool) :
    ∀ (k : ℕ) (a b : ℝ), bisectAns f k a b = runP (fun l => mid (bstate a b l)) f k := by
  intro k
  induction k with
  | zero => intro a b; rfl
  | succ k ih =>
    intro a b
    by_cases hf : f ((a + b) / 2) = true
    · rw [runP_succ_cons _ (fun l => mid (bstate ((a + b) / 2) b l)) f
        (fun l => by
          show mid (bstate a b (f ((a + b) / 2) :: l)) = _
          rw [hf]; rfl) k]
      simp only [bisectAns, hf, if_true, ih]
      show _ = f ((a + b) / 2) :: _
      rw [hf]
    · simp only [Bool.not_eq_true] at hf
      rw [runP_succ_cons _ (fun l => mid (bstate a ((a + b) / 2) l)) f
        (fun l => by
          show mid (bstate a b (f ((a + b) / 2) :: l)) = _
          rw [hf]; rfl) k]
      simp only [bisectAns, hf, Bool.false_eq_true, if_false, ih]
      show _ = f ((a + b) / 2) :: _
      rw [hf]

lemma bisect_eq_runP (f : ℝ → Bool) (k : ℕ) (a b : ℝ) :
    bisect f k a b = bstate a b (runP (fun l => mid (bstate a b l)) f k) := by
  rw [bisect_eq_bstate, bisectAns_eq_runP]

variable (m : ℕ) (t ε c : ℝ) (x0 : E) (u : Fin (m + 1) → E)

/-- **L2's answers** against an oracle `orc`: the `Qloc` answers obtained by running `L2probe`
against `orc`. -/
noncomputable def L2run (orc : E → Bool) : List Bool := runP (L2probe m t ε c x0 u) orc (Qloc m t ε c)

/-- Angle asked on circle `j.succ` within its block, as a function of the block's answers so far:
the side query at `w₀`, then the bisection of the selected bracket. -/
noncomputable def blkAngle (l : List Bool) : ℝ :=
  if l.length = 0 then w₀ t c
  else if l.headD false then mid (bstate (w₀ t c) (Θ₀ t c) (l.drop 1))
  else mid (bstate (-w₀ t c) (-Θ₀ t c) (l.drop 1))

lemma L2probe_A0 (l : List Bool) (hl : l.length < ka m t ε c) :
    L2probe m t ε c x0 u l = circ m x0 u 0 (mid (bstate 0 (Θ t) l)) := by
  simp only [L2probe, if_pos hl]

lemma L2probe_A1 (p l : List Bool) (hp : p.length = ka m t ε c) (hl : l.length < ka m t ε c) :
    L2probe m t ε c x0 u (p ++ l) = circ m x0 u 0 (mid (bstate 0 (-Θ t) l)) := by
  have h1 : ¬ (p ++ l).length < ka m t ε c := by simp [hp]
  have h2 : (p ++ l).length < 2 * ka m t ε c := by simp [hp]; omega
  simp only [L2probe, if_neg h1, if_pos h2, List.drop_left' hp]

lemma L2probe_B (j : Fin m) (p l : List Bool)
    (hp : p.length = 2 * ka m t ε c + (j : ℕ) * (kb m t ε c + 1))
    (hl : l.length < kb m t ε c + 1) :
    L2probe m t ε c x0 u (p ++ l) = circ m x0 u j.succ (blkAngle t c l) := by
  set KA := ka m t ε c
  set KB := kb m t ε c
  have hlen : (p ++ l).length = 2 * KA + (j : ℕ) * (KB + 1) + l.length := by simp [hp]
  have h1 : ¬ (p ++ l).length < KA := by rw [hlen]; omega
  have h2 : ¬ (p ++ l).length < 2 * KA := by rw [hlen]; omega
  have hr : (p ++ l).length - 2 * KA = l.length + (KB + 1) * (j : ℕ) := by
    rw [hlen, Nat.mul_comm (j : ℕ)]; omega
  have hdiv : ((p ++ l).length - 2 * KA) / (KB + 1) = j := by
    rw [hr, Nat.add_mul_div_left _ _ (Nat.succ_pos _), Nat.div_eq_of_lt hl, zero_add]
  have hmod : ((p ++ l).length - 2 * KA) % (KB + 1) = l.length := by
    rw [hr, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  have hdrop : (p ++ l).drop (2 * KA + (j : ℕ) * (KB + 1)) = l := List.drop_left' hp
  unfold L2probe
  dsimp only
  rw [if_neg h1, if_neg h2]
  rw [dif_pos (by rw [hdiv]; exact j.2)]
  have hj : (⟨((p ++ l).length - 2 * KA) / (KB + 1), by rw [hdiv]; exact j.2⟩ : Fin m) = j :=
    Fin.ext hdiv
  rw [hj]
  have hmod' : ((p ++ l).length - 2 * ka m t ε c) % (kb m t ε c + 1) = l.length := hmod
  have hdrop' : (p ++ l).drop (2 * ka m t ε c + (j : ℕ) * (kb m t ε c + 1)) = l := hdrop
  have hdiv' : ((p ++ l).length - 2 * ka m t ε c) / (kb m t ε c + 1) = j := hdiv
  simp only [hmod', hdiv', hdrop', blkAngle]
  split_ifs <;> rfl

/-- Reading a block back off a longer run. -/
lemma runP_take_drop {α β : Type*} (pr : List Bool → α) (orc : α → Bool) (q : List Bool → β)
    (orc' : β → Bool) (s k N : ℕ) (hN : s + k ≤ N)
    (h : runP pr orc (s + k) = runP pr orc s ++ runP q orc' k) :
    ((runP pr orc N).drop s).take k = runP q orc' k := by
  obtain ⟨l, hl⟩ := runP_prefix pr orc (s + k) (N - (s + k))
  rw [show N = s + k + (N - (s + k)) by omega, hl, h, List.append_assoc,
    List.drop_left' (runP_length pr orc s), List.take_left' (runP_length q orc' k)]

/-- **L2 correspondence.** Running the answer-driven rule `L2probe` against any oracle `orc` for
`Qloc` rounds and reading off with `L2fromAns` gives exactly `Attacks.L2`'s output. -/
theorem L2fromAns_L2run (orc : E → Bool) :
    L2fromAns m t ε c x0 u (L2run m t ε c x0 u orc) = L2 m t ε c x0 u orc := by
  set KA := ka m t ε c with hKA
  set KB := kb m t ε c with hKB
  set R := runP (L2probe m t ε c x0 u) orc with hR
  have hN : Qloc m t ε c = 2 * KA + m * (KB + 1) := rfl
  let f : Fin (m + 1) → ℝ → Bool := fun j θ => orc (circ m x0 u j θ)
  -- circle 0, first end
  have hA0 : R (0 + KA) = R 0 ++ runP (fun l => mid (bstate 0 (Θ t) l)) (f 0) KA :=
    runP_block _ orc _ (f 0) 0 KA (fun l hl => by
      simp only [runP, List.nil_append]
      rw [L2probe_A0 m t ε c x0 u l hl]) KA le_rfl
  have hθp : (bstate 0 (Θ t) ((L2run m t ε c x0 u orc).take KA)).1 = (bisect (f 0) KA 0 (Θ t)).1 := by
    have := runP_take_drop _ orc _ (f 0) 0 KA (Qloc m t ε c) (by rw [hN]; omega) hA0
    rw [List.drop_zero] at this
    rw [bisect_eq_runP, L2run, ← hR, this]
  -- circle 0, second end
  have hA1 : R (KA + KA) = R KA ++ runP (fun l => mid (bstate 0 (-Θ t) l)) (f 0) KA :=
    runP_block _ orc _ (f 0) KA KA (fun l hl => by
      rw [L2probe_A1 m t ε c x0 u _ l (runP_length _ _ _) hl]) KA le_rfl
  have hθm : (bstate 0 (-Θ t) (((L2run m t ε c x0 u orc).drop KA).take KA)).1 =
      (bisect (f 0) KA 0 (-Θ t)).1 := by
    have := runP_take_drop _ orc _ (f 0) KA KA (Qloc m t ε c) (by rw [hN]; omega) hA1
    rw [bisect_eq_runP, L2run, ← hR, this]
  -- circles 1 … m
  have hθh : ∀ j : Fin m,
      (if (((L2run m t ε c x0 u orc).drop (2 * KA + (j : ℕ) * (KB + 1))).take (KB + 1)).headD false
        then (bstate (w₀ t c) (Θ₀ t c)
          ((((L2run m t ε c x0 u orc).drop (2 * KA + (j : ℕ) * (KB + 1))).take (KB + 1)).drop 1)).1
        else (bstate (-w₀ t c) (-Θ₀ t c)
          ((((L2run m t ε c x0 u orc).drop (2 * KA + (j : ℕ) * (KB + 1))).take (KB + 1)).drop 1)).1)
      = (if f j.succ (w₀ t c) then (bisect (f j.succ) KB (w₀ t c) (Θ₀ t c)).1
          else (bisect (f j.succ) KB (-w₀ t c) (-Θ₀ t c)).1) := by
    intro j
    have hB : R (2 * KA + (j : ℕ) * (KB + 1) + (KB + 1)) =
        R (2 * KA + (j : ℕ) * (KB + 1)) ++ runP (blkAngle t c) (f j.succ) (KB + 1) :=
      runP_block _ orc _ (f j.succ) _ (KB + 1) (fun l hl => by
          rw [L2probe_B m t ε c x0 u j _ l (runP_length _ _ _) hl]) (KB + 1) le_rfl
    have hle : 2 * KA + (j : ℕ) * (KB + 1) + (KB + 1) ≤ Qloc m t ε c := by
      rw [hN]
      have : ((j : ℕ) + 1) * (KB + 1) ≤ m * (KB + 1) := Nat.mul_le_mul_right _ j.2
      nlinarith
    have hblk := runP_take_drop _ orc _ (f j.succ) _ (KB + 1) (Qloc m t ε c) hle hB
    rw [L2run, ← hR, hblk]
    have h0 : blkAngle t c [] = w₀ t c := by simp [blkAngle]
    by_cases hb : f j.succ (w₀ t c) = true
    · rw [runP_succ_cons (blkAngle t c) (fun l => mid (bstate (w₀ t c) (Θ₀ t c) l)) (f j.succ)
        (fun l => by rw [h0, hb]; simp [blkAngle]) KB, h0, hb]
      simp [bisect_eq_runP]
    · simp only [Bool.not_eq_true] at hb
      rw [runP_succ_cons (blkAngle t c) (fun l => mid (bstate (-w₀ t c) (-Θ₀ t c) l)) (f j.succ)
        (fun l => by rw [h0, hb]; simp [blkAngle]) KB, h0, hb]
      simp [bisect_eq_runP]
  unfold L2fromAns
  dsimp only
  rw [← hKA, ← hKB]
  simp only [hθp, hθm, hθh]
  rfl

end L2corr

/-! ### Unit vectors: `toSph` never falls back on L2's probes or output -/

section L2unit

lemma toSph_of_norm (dflt : Sph E) {v : E} (h : ‖v‖ = 1) : toSph dflt v = ⟨v, h⟩ := by
  rw [toSph, dif_pos h]

variable {m : ℕ} {x0 : E} {u : Fin (m + 1) → E}

/-- Under an orthonormal frame `(x0, u₀, …, u_m)`, every circle point is a unit vector. -/
lemma norm_circ (hon : Orthonormal ℝ (Fin.cons x0 u : Fin (m + 2) → E)) (j : Fin (m + 1))
    (θ : ℝ) : ‖circ m x0 u j θ‖ = 1 := by
  have hx0 : ‖x0‖ = 1 := by simpa using hon.1 0
  have huj : ‖u j‖ = 1 := by simpa using hon.1 j.succ
  have hin : inner ℝ x0 (u j) = 0 := by simpa using hon.2 (Fin.succ_ne_zero j).symm
  have hsq : ‖circ m x0 u j θ‖ ^ 2 = 1 := by
    rw [circ, norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hin,
      hx0, huj]
    simp only [Real.norm_eq_abs, conj_trivial, mul_zero, mul_one, add_zero]
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_abs (Real.sin θ), sq_abs (Real.cos θ)]
  have := norm_nonneg (circ m x0 u j θ)
  nlinarith

/-- Every L2 probe is a unit vector under an orthonormal frame. -/
lemma norm_L2probe (hon : Orthonormal ℝ (Fin.cons x0 u : Fin (m + 2) → E)) (t ε c : ℝ)
    (ans : List Bool) : ‖L2probe m t ε c x0 u ans‖ = 1 := by
  have hx0 : ‖x0‖ = 1 := by simpa using hon.1 0
  unfold L2probe
  dsimp only
  split_ifs <;> first | exact norm_circ hon _ _ | exact hx0

/-- Hence the probe rule's `toSph` never falls back to the dummy on an L2 probe. -/
lemma toSph_L2probe (hon : Orthonormal ℝ (Fin.cons x0 u : Fin (m + 2) → E)) (t ε c : ℝ)
    (dflt : Sph E) (ans : List Bool) :
    (toSph dflt (L2probe m t ε c x0 u ans)).1 = L2probe m t ε c x0 u ans := by
  rw [toSph_of_norm dflt (norm_L2probe hon t ε c ans)]

end L2unit

section L2unit2

variable (m : ℕ) (t ε c : ℝ) (x0 : E) (u : Fin (m + 1) → E)

/-- `â` of `L2fromAns`. -/
noncomputable def L2aHat (ans : List Bool) : ℝ :=
  let KA := ka m t ε c
  let θp := (bstate 0 (Θ t) (ans.take KA)).1
  let θm := (bstate 0 (-Θ t) ((ans.drop KA).take KA)).1
  t / Real.cos ((θp - θm) / 2) * Real.cos ((θp + θm) / 2)

/-- The un-normalised L2 output `g'` of `L2fromAns` (its body up to the final normalisation). -/
noncomputable def L2raw (ans : List Bool) : E :=
  let KA := ka m t ε c
  let KB := kb m t ε c
  let θp := (bstate 0 (Θ t) (ans.take KA)).1
  let θm := (bstate 0 (-Θ t) ((ans.drop KA).take KA)).1
  let â := t / Real.cos ((θp - θm) / 2) * Real.cos ((θp + θm) / 2)
  let b₀ := t / Real.cos ((θp - θm) / 2) * Real.sin ((θp + θm) / 2)
  let θh : Fin m → ℝ := fun j =>
    let blk := (ans.drop (2 * KA + (j : ℕ) * (KB + 1))).take (KB + 1)
    if blk.headD false then (bstate (w₀ t c) (Θ₀ t c) (blk.drop 1)).1
    else (bstate (-w₀ t c) (-Θ₀ t c) (blk.drop 1)).1
  let b : Fin (m + 1) → ℝ :=
    Fin.cases b₀ (fun j => (t - â * Real.cos (θh j)) / Real.sin (θh j))
  â • x0 + ∑ j, b j • u j

lemma L2fromAns_eq (ans : List Bool) :
    L2fromAns m t ε c x0 u ans = ‖L2raw m t ε c x0 u ans‖⁻¹ • L2raw m t ε c x0 u ans := rfl

variable {m t ε c x0 u}

/-- **L2's output is a unit vector** whenever `g' ≠ 0` (no orthonormality needed). -/
lemma norm_L2fromAns (ans : List Bool) (h : L2raw m t ε c x0 u ans ≠ 0) :
    ‖L2fromAns m t ε c x0 u ans‖ = 1 := by
  rw [L2fromAns_eq, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

lemma toSph_L2fromAns (dflt : Sph E) (ans : List Bool) (h : L2raw m t ε c x0 u ans ≠ 0) :
    (toSph dflt (L2fromAns m t ε c x0 u ans)).1 = L2fromAns m t ε c x0 u ans := by
  rw [toSph_of_norm dflt (norm_L2fromAns ans h)]

/-- Under an orthonormal frame, `⟨x0, g'⟩ = â`. -/
lemma inner_x0_L2raw (hon : Orthonormal ℝ (Fin.cons x0 u : Fin (m + 2) → E)) (ans : List Bool) :
    inner ℝ x0 (L2raw m t ε c x0 u ans) = L2aHat m t ε c ans := by
  have hx0 : inner ℝ x0 x0 = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq]; simp [by simpa using hon.1 0]
  have hin : ∀ j, inner ℝ x0 (u j) = (0 : ℝ) := fun j => by
    simpa using hon.2 (Fin.succ_ne_zero j).symm
  unfold L2raw L2aHat
  dsimp only
  rw [inner_add_right, inner_smul_right, hx0, inner_sum]
  simp [inner_smul_right, hin]

/-- Under an orthonormal frame, `â ≠ 0` (e.g. `â > 0`, as at L2's operating point
`â ≈ ⟨x0, g⟩ ≥ t + c`) forces `g' ≠ 0`. -/
lemma L2raw_ne_zero (hon : Orthonormal ℝ (Fin.cons x0 u : Fin (m + 2) → E)) (ans : List Bool)
    (ha : L2aHat m t ε c ans ≠ 0) : L2raw m t ε c x0 u ans ≠ 0 := by
  intro h0
  apply ha
  rw [← inner_x0_L2raw hon ans, h0, inner_zero_right]

/-- Combined: orthonormal frame and `â ≠ 0` ⇒ L2's output is a unit vector. -/
lemma norm_L2fromAns_of_aHat (hon : Orthonormal ℝ (Fin.cons x0 u : Fin (m + 2) → E))
    (ans : List Bool) (ha : L2aHat m t ε c ans ≠ 0) : ‖L2fromAns m t ε c x0 u ans‖ = 1 :=
  norm_L2fromAns ans (L2raw_ne_zero hon ans ha)

/-- L2 itself (via the correspondence) outputs a unit vector when `g' ≠ 0`. -/
lemma norm_L2 (orc : E → Bool) (h : L2raw m t ε c x0 u (L2run m t ε c x0 u orc) ≠ 0) :
    ‖L2 m t ε c x0 u orc‖ = 1 := by
  rw [← L2fromAns_L2run]; exact norm_L2fromAns _ h

end L2unit2

/-! ## 5. Theorem 6.3 at `W = E`, K0, finite probe support, Markov branch (§9 of the brief) -/

section Expect

variable {X : Type*} [Fintype X] (ν : X → ℝ)

/-- Expectation over an i.i.d. `ν`-sequence of length `K`, of a functional of the list. -/
noncomputable def EK (K : ℕ) (f : List X → ℝ) : ℝ :=
  ∑ xs : Fin K → X, (∏ s, ν (xs s)) * f (List.ofFn xs)

lemma EK_zero (f : List X → ℝ) : EK ν 0 f = f [] := by
  simp [EK]

lemma EK_succ (K : ℕ) (f : List X → ℝ) :
    EK ν (K + 1) f = EK ν K (fun l => ∑ x, ν x * f (l ++ [x])) := by
  unfold EK
  rw [← (Fin.snocEquiv (fun _ : Fin (K + 1) => X)).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Fin.snocEquiv_apply, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  rw [List.ofFn_succ']
  simp only [Fin.snocEquiv_apply, Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
  ring

lemma EK_add (K : ℕ) (f g : List X → ℝ) : EK ν K (fun l => f l + g l) = EK ν K f + EK ν K g := by
  unfold EK; rw [← Finset.sum_add_distrib]; simp only [mul_add]

lemma EK_mul (K : ℕ) (a : ℝ) (f : List X → ℝ) : EK ν K (fun l => a * f l) = a * EK ν K f := by
  unfold EK; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring

lemma EK_sum {β : Type*} (s : Finset β) (K : ℕ) (f : β → List X → ℝ) :
    EK ν K (fun l => ∑ b ∈ s, f b l) = ∑ b ∈ s, EK ν K (f b) := by
  unfold EK; simp only [Finset.mul_sum]; rw [Finset.sum_comm]

variable {ν}

lemma EK_const (hν1 : ∑ x, ν x = 1) (K : ℕ) (a : ℝ) : EK ν K (fun _ => a) = a := by
  induction K with
  | zero => simp [EK_zero]
  | succ K ih => rw [EK_succ]; simp only [← Finset.sum_mul, hν1, one_mul]; exact ih

lemma EK_affine (hν1 : ∑ x, ν x = 1) (K : ℕ) (a b c : ℝ) (f g : List X → ℝ) :
    EK ν K (fun l => a + b * f l + c * g l) = a + b * EK ν K f + c * EK ν K g := by
  calc EK ν K (fun l => a + b * f l + c * g l)
      = EK ν K (fun _ => a) + EK ν K (fun l => b * f l) + EK ν K (fun l => c * g l) := by
        unfold EK; rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun xs _ => by ring
    _ = a + b * EK ν K f + c * EK ν K g := by rw [EK_const hν1, EK_mul, EK_mul]

lemma EK_mono (hν0 : ∀ x, 0 ≤ ν x) (K : ℕ) {f g : List X → ℝ}
    (h : ∀ xs : Fin K → X, f (List.ofFn xs) ≤ g (List.ofFn xs)) : EK ν K f ≤ EK ν K g :=
  Finset.sum_le_sum fun xs _ =>
    mul_le_mul_of_nonneg_left (h xs) (Finset.prod_nonneg fun _ _ => hν0 _)

lemma EK_le_const (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (K : ℕ) {f : List X → ℝ} {a : ℝ}
    (h : ∀ l : List X, l.length = K → f l ≤ a) : EK ν K f ≤ a := by
  rw [← EK_const hν1 K a]
  exact EK_mono hν0 K fun _ => h _ (List.length_ofFn)

lemma EK_nonneg (hν0 : ∀ x, 0 ≤ ν x) (K : ℕ) {f : List X → ℝ} (h : ∀ l, 0 ≤ f l) :
    0 ≤ EK ν K f :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Finset.prod_nonneg fun _ _ => hν0 _) (h _)

/-! Generic deterministic run and round counters. -/

variable {σ : Type*}

/-- State after processing the list `l` of search points with step `st` from `s0`. -/
def runSt (st : σ → X → σ) (s0 : σ) (l : List X) : σ := l.foldl st s0

/-- `∑_{rounds} inc(state before the round, point of the round)`. -/
def cnt (st : σ → X → σ) (s0 : σ) (inc : σ → X → ℝ) (l : List X) : ℝ :=
  (l.foldl (fun p x => (st p.1 x, p.2 + inc p.1 x)) (s0, 0)).2

lemma foldl_pair_fst (st : σ → X → σ) (inc : σ → X → ℝ) :
    ∀ (l : List X) (a : σ) (r : ℝ),
      (l.foldl (fun p x => (st p.1 x, p.2 + inc p.1 x)) (a, r)).1 = l.foldl st a
  | [], _, _ => rfl
  | x :: l, a, r => by simp only [List.foldl_cons]; exact foldl_pair_fst st inc l _ _

lemma runSt_nil (st : σ → X → σ) (s0 : σ) : runSt st s0 [] = s0 := rfl

lemma runSt_snoc (st : σ → X → σ) (s0 : σ) (l : List X) (x : X) :
    runSt st s0 (l ++ [x]) = st (runSt st s0 l) x := by
  simp [runSt, List.foldl_append]

lemma cnt_nil (st : σ → X → σ) (s0 : σ) (inc : σ → X → ℝ) : cnt st s0 inc [] = 0 := rfl

lemma cnt_snoc (st : σ → X → σ) (s0 : σ) (inc : σ → X → ℝ) (l : List X) (x : X) :
    cnt st s0 inc (l ++ [x]) = cnt st s0 inc l + inc (runSt st s0 l) x := by
  simp only [cnt, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [foldl_pair_fst]; rfl

lemma cnt_sum {β : Type*} (s : Finset β) (st : σ → X → σ) (s0 : σ) (inc : β → σ → X → ℝ)
    (l : List X) : cnt st s0 (fun a x => ∑ b ∈ s, inc b a x) l = ∑ b ∈ s, cnt st s0 (inc b) l := by
  induction l using List.reverseRecOn with
  | nil => simp [cnt_nil]
  | append_singleton l x ih => simp only [cnt_snoc, ih, Finset.sum_add_distrib]

lemma cnt_mono (st : σ → X → σ) (s0 : σ) {inc inc' : σ → X → ℝ} (h : ∀ a x, inc a x ≤ inc' a x)
    (l : List X) : cnt st s0 inc l ≤ cnt st s0 inc' l := by
  induction l using List.reverseRecOn with
  | nil => simp [cnt_nil]
  | append_singleton l x ih => rw [cnt_snoc, cnt_snoc]; linarith [h (runSt st s0 l) x]

lemma cnt_nonneg (st : σ → X → σ) (s0 : σ) {inc : σ → X → ℝ} (h : ∀ a x, 0 ≤ inc a x)
    (l : List X) : 0 ≤ cnt st s0 inc l := by
  have h0 : cnt st s0 (fun _ _ => (0:ℝ)) l = 0 := by
    induction l using List.reverseRecOn with
    | nil => rfl
    | append_singleton l x ih => rw [cnt_snoc, ih]; simp
  have := cnt_mono st s0 (inc := fun _ _ => 0) h l
  linarith

lemma cnt_le_length (st : σ → X → σ) (s0 : σ) {inc : σ → X → ℝ} (h : ∀ a x, inc a x ≤ 1)
    (l : List X) : cnt st s0 inc l ≤ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [cnt_nil]
  | append_singleton l x ih =>
    rw [cnt_snoc]; simp only [List.length_append, List.length_singleton, Nat.cast_add,
      Nat.cast_one]; linarith [h (runSt st s0 l) x]

/-- **Expectation of a round counter** = sum over rounds of the expected one-round increment
(the one-step "conditioning on `F_{s−1}`": sum over `x_s` with the prefix fixed). -/
lemma EK_cnt (hν1 : ∑ x, ν x = 1) (st : σ → X → σ) (s0 : σ) (inc : σ → X → ℝ) (K : ℕ) :
    EK ν K (cnt st s0 inc) =
      ∑ s ∈ range K, EK ν s (fun l => ∑ x, ν x * inc (runSt st s0 l) x) := by
  induction K with
  | zero => simp [EK_zero, cnt_nil]
  | succ K ih =>
    rw [EK_succ, Finset.sum_range_succ, ← ih, ← EK_add]
    congr 1; funext l
    simp only [cnt_snoc, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hν1, one_mul]

end Expect


/-! #### Indicators -/

open Classical in
/-- Real indicator of a proposition. -/
noncomputable def ind (p : Prop) : ℝ := if p then 1 else 0

lemma ind_nonneg (p : Prop) : 0 ≤ ind p := by unfold ind; split_ifs <;> norm_num
lemma ind_le_one (p : Prop) : ind p ≤ 1 := by unfold ind; split_ifs <;> norm_num
lemma ind_pos {p : Prop} (h : p) : ind p = 1 := by unfold ind; rw [if_pos h]
lemma ind_neg {p : Prop} (h : ¬ p) : ind p = 0 := by unfold ind; rw [if_neg h]
lemma ind_and (p q : Prop) : ind (p ∧ q) = ind p * ind q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [ind_pos, ind_neg, hp, hq]
lemma ind_mono {p q : Prop} (h : p → q) : ind p ≤ ind q := by
  by_cases hp : p
  · rw [ind_pos hp, ind_pos (h hp)]
  · rw [ind_neg hp]; exact ind_nonneg q
lemma mul_ind (a : ℝ) (p : Prop) [Decidable p] : a * ind p = if p then a else 0 := by
  by_cases hp : p <;> simp [ind_pos, ind_neg, hp]
lemma ite_one_zero (p : Prop) [Decidable p] : (if p then (1:ℝ) else 0) = ind p := by
  by_cases hp : p <;> simp [ind_pos, ind_neg, hp]

/-- Bonferroni and the double count, pointwise: for indicators `a i ∈ {0,1}`,
`1{∃ i, a i = 1} ≥ Σ a − ½ Σ_{i≠i'} a a'`, and the pair sum is `≥ 2` when two of them are on. -/
lemma pair_sum_eq {κ : Type*} [Fintype κ] [DecidableEq κ] (p : κ → Prop) :
    ∑ i, ∑ i', (if i ≠ i' then ind (p i) * ind (p i') else 0) =
      (∑ i, ind (p i)) * (∑ i, ind (p i)) - ∑ i, ind (p i) := by
  have hsq : ∀ i, ind (p i) * ind (p i) = ind (p i) := fun i => by
    by_cases h : p i <;> simp [ind_pos, ind_neg, h]
  have : ∀ i, ∑ i', (if i ≠ i' then ind (p i) * ind (p i') else 0) =
      ind (p i) * (∑ i', ind (p i')) - ind (p i) := by
    intro i
    have h1 : ∀ i', (if i ≠ i' then ind (p i) * ind (p i') else 0) =
        ind (p i) * ind (p i') - (if i = i' then ind (p i) * ind (p i') else 0) := by
      intro i'; by_cases h : i = i' <;> simp [h]
    simp only [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, hsq]
  simp only [this, Finset.sum_sub_distrib, ← Finset.sum_mul]

lemma sum_ind_eq_card {κ : Type*} [Fintype κ] (p : κ → Prop) :
    ∃ N : ℕ, ∑ i, ind (p i) = N ∧ (N = 0 ↔ ¬ ∃ i, p i) ∧ (∀ i i', i ≠ i' → p i → p i' → 2 ≤ N) := by
  classical
  refine ⟨(univ.filter p).card, ?_, ?_, ?_⟩
  · simp only [ind]; rw [Finset.sum_boole]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; simp
  · intro i i' hii hi hi'
    have : ({i, i'} : Finset κ) ⊆ univ.filter p := by
      intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> simp [hi, hi']
    have := Finset.card_le_card this
    rwa [Finset.card_pair hii] at this

lemma bonferroni {κ : Type*} [Fintype κ] [DecidableEq κ] (p : κ → Prop) :
    ∑ i, ind (p i) - (1 / 2) * ∑ i, ∑ i', (if i ≠ i' then ind (p i) * ind (p i') else 0)
      ≤ ind (∃ i, p i) := by
  rw [pair_sum_eq]
  obtain ⟨N, hN, hN0, -⟩ := sum_ind_eq_card p
  rw [hN]
  by_cases h : ∃ i, p i
  · rw [ind_pos h]
    have hN1 : 1 ≤ N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · exact absurd (hN0.1 h0) (not_not.2 h)
      · exact h0
    rcases Nat.lt_or_ge N 2 with h2 | h2
    · have : N = 1 := by omega
      subst this; norm_num
    · have : (2:ℝ) ≤ N := by exact_mod_cast h2
      nlinarith
  · rw [ind_neg h, hN0.2 h]; norm_num

lemma pair_sum_ge_two {κ : Type*} [Fintype κ] [DecidableEq κ] (p : κ → Prop) (i i' : κ)
    (hii : i ≠ i') (hi : p i) (hi' : p i') :
    1 ≤ (1 / 2) * ∑ i, ∑ i', (if i ≠ i' then ind (p i) * ind (p i') else 0) := by
  rw [pair_sum_eq]
  obtain ⟨N, hN, -, h2⟩ := sum_ind_eq_card p
  rw [hN]
  have : (2:ℝ) ≤ N := by exact_mod_cast h2 i i' hii hi hi'
  nlinarith

lemma pair_sum_nonneg {κ : Type*} [Fintype κ] [DecidableEq κ] (p : κ → Prop) :
    0 ≤ ∑ i, ∑ i', (if i ≠ i' then ind (p i) * ind (p i') else 0) := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ => ?_
  split_ifs
  · exact mul_nonneg (ind_nonneg _) (ind_nonneg _)
  · exact le_rfl

/-! ### The attack at `W = E`, K0, fixed frames, as a deterministic run -/

section Attack

variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [Nonempty ι]
variable {X : Type*} [Fintype X]

/-- Parameters of `A(ν, c, ε, K, M)` at `W = E` (search points `pt : X → S`, fixed frame rule
`Φ`, attribution/recovery accuracy `ε`, L2 accuracy `εL`, margin `c`, launch cap `M`, and the
fixed unit vector `dflt` of convention (A2)). -/
structure Atk (E X : Type*) [NormedAddCommGroup E] where
  m : ℕ
  ε : ℝ
  εL : ℝ
  c : ℝ
  M : ℕ
  pt : X → Sph E
  Φ : X → Fin (m + 1) → E
  dflt : Sph E

variable (G : Gallery E ι Fine) (A : Atk E X)

open Classical in
/-- The K0 oracle of the list `V`: `b(y) = 1{maxᵢ ⟨y, gᵢ⟩ > t}`. -/
noncomputable def orcK0 (V : ι → Fine) (y : E) : Bool :=
  decide (∃ i, G.thr < inner ℝ y (G.g (V i)))

/-- The one-face K0 oracle of a template `gl`. -/
noncomputable def oneOrc (gl : E) (y : E) : Bool := decide (G.thr < inner ℝ y gl)

/-- `x` launches given outputs `F`: an unattributed match. -/
def launches (V : ι → Fine) (F : List (Sph E)) (x : X) : Prop :=
  (∃ i, G.thr < inner ℝ (A.pt x).1 (G.g (V i))) ∧ ∀ gh ∈ F, inner ℝ (A.pt x).1 gh.1 ≤ G.thr - A.ε

/-- `Q_loc`. -/
noncomputable def qL : ℕ := Qloc A.m G.thr A.εL A.c

/-- Output of a launch from `x` (L2 against the real oracle, frame `Φ x`; (A2) unit output). -/
noncomputable def outp (V : ι → Fine) (x : X) : Sph E :=
  toSph A.dflt (L2 A.m G.thr A.εL A.c (A.pt x).1 (A.Φ x) (orcK0 G V))

open Classical in
/-- One search round (stopped once `|F| = M`). -/
noncomputable def stepA (V : ι → Fine) (F : List (Sph E)) (x : X) : List (Sph E) :=
  if F.length < A.M ∧ launches G A V F x then F ++ [outp G A V x] else F

/-- Outputs after the search rounds `l`. -/
noncomputable def Fof (V : ι → Fine) (l : List X) : List (Sph E) := runSt (stepA G A V) [] l

open Classical in
/-- `P(x, g)`: the query points of the ideal run (L2 from `x`, frame `Φ x`, one-face oracle). -/
noncomputable def Pset (x : X) (gl : E) : Finset E :=
  (range (qL G A)).image fun k => L2probe A.m G.thr A.εL A.c (A.pt x).1 (A.Φ x)
    (runP (L2probe A.m G.thr A.εL A.c (A.pt x).1 (A.Φ x)) (oneOrc G gl) k)

/-- `Bad(V)` (§6.4): margin (F1), collision (F2), interference of the ideal run (F3). -/
def Bad (V : ι → Fine) (x : X) : Prop :=
  (∃ i, G.thr < inner ℝ (A.pt x).1 (G.g (V i)) ∧ inner ℝ (A.pt x).1 (G.g (V i)) < G.thr + A.c) ∨
  (∃ i i', i ≠ i' ∧ G.thr < inner ℝ (A.pt x).1 (G.g (V i)) ∧
      G.thr < inner ℝ (A.pt x).1 (G.g (V i'))) ∨
  (∃ i i', i ≠ i' ∧ G.thr < inner ℝ (A.pt x).1 (G.g (V i)) ∧
      ∃ y ∈ Pset G A x (G.g (V i)), G.thr < inner ℝ y (G.g (V i')))

open Classical in
/-- `τ`: active search rounds. -/
noncomputable def tau (V : ι → Fine) : List X → ℝ :=
  cnt (stepA G A V) [] (fun F _ => ind (F.length < A.M))

open Classical in
/-- `τ_j`: search rounds in stage `j` (`|F| = j`). -/
noncomputable def tauj (V : ι → Fine) (j : ℕ) : List X → ℝ :=
  cnt (stepA G A V) [] (fun F _ => ind (F.length = j))

open Classical in
/-- `B_d`: bad launches. -/
noncomputable def Bd (V : ι → Fine) : List X → ℝ :=
  cnt (stepA G A V) [] (fun F x => ind (F.length < A.M ∧ launches G A V F x ∧ Bad G A V x))

open Classical in
/-- Number of entries `ε`-recovered by a list of outputs. -/
noncomputable def NF (V : ι → Fine) (F : List (Sph E)) : ℕ :=
  (univ.filter fun i => ∃ gh ∈ F, ‖gh.1 - G.g (V i)‖ ≤ A.ε).card

/-- `N_ε` of the run. -/
noncomputable def Neps (V : ι → Fine) (l : List X) : ℕ := NF G A V (Fof G A V l)

open Classical in
/-- Queries issued: one per active search round, `Q_loc` per launch. -/
noncomputable def queries (V : ι → Fine) : List X → ℝ :=
  cnt (stepA G A V) []
    (fun F x => ind (F.length < A.M) * (1 + (qL G A : ℝ) * ind (launches G A V F x)))

/-- K0 bridge: on unit vectors the oracle `orcK0` is the gallery's noiseless response. -/
lemma resp_eq_orcK0 (hκ : ∀ s, G.κ s = if G.thr < s then 1 else 0) (V : ι → Fine) (y : Sph E) :
    G.resp V y = if orcK0 G V y.1 = true then 1 else 0 := by
  unfold Gallery.resp orcK0
  rw [hκ]
  by_cases h : ∃ i, G.thr < inner ℝ y.1 (G.g (V i))
  · rw [if_pos ((thr_lt_score_iff G V y).2 h)]; simp [h]
  · rw [if_neg (fun hc => h ((thr_lt_score_iff G V y).1 hc))]; simp [h]

/-! #### Lemma 3 (transcript agreement) -/

lemma runP_congr {α : Type*} (pr : List Bool → α) (o o' : α → Bool) :
    ∀ n, (∀ k < n, o (pr (runP pr o' k)) = o' (pr (runP pr o' k))) → runP pr o n = runP pr o' n
  | 0, _ => rfl
  | n + 1, h => by
    rw [runP, runP, runP_congr pr o o' n (fun k hk => h k (by omega)), h n (by omega)]

omit [Fintype ι] [DecidableEq ι] [Fintype Fine] [Nonempty ι] [Fintype X] in
lemma L2_norm_or (m : ℕ) (t ε c : ℝ)
    (x0 : E) (u : Fin (m + 1) → E) (orc : E → Bool) :
    ‖L2 m t ε c x0 u orc‖ = 1 ∨ L2 m t ε c x0 u orc = 0 := by
  rw [← L2fromAns_L2run]
  by_cases h : L2raw m t ε c x0 u (L2run m t ε c x0 u orc) = 0
  · right; rw [L2fromAns_eq, h, smul_zero]
  · left; exact norm_L2fromAns _ h

/-! #### Lemma 4′ -/

/-- **Good launch** (Lemma 4′, success half): a launch at a round outside `Bad(V)` reaches an entry
`i` not `ε`-recovered by `F`, and outputs `ĝ` with `‖ĝ − gᵢ‖ ≤ ε`. -/
lemma good_launch (hdim : Module.finrank ℝ E = A.m + 2)
    (hΦ : ∀ x, Orthonormal ℝ (Fin.cons (A.pt x).1 (A.Φ x) : Fin (A.m + 2) → E))
    (ht0 : 0 < G.thr) (ht1 : G.thr < 1) (hc : 0 < A.c) (hc1 : G.thr + A.c < 1)
    (hεL : 0 < A.εL) (hεLε : A.εL ≤ A.ε) (hεL1 : A.εL < 1)
    (V : ι → Fine) (F : List (Sph E)) (x : X) (hl : launches G A V F x) (hb : ¬ Bad G A V x) :
    ∃ i, (∀ gh ∈ F, ¬ ‖gh.1 - G.g (V i)‖ ≤ A.ε) ∧ ‖(outp G A V x).1 - G.g (V i)‖ ≤ A.ε := by
  classical
  obtain ⟨⟨i, hi⟩, hattr⟩ := hl
  simp only [Bad, not_or, not_exists, not_and] at hb
  obtain ⟨h1, -, h3⟩ := hb
  refine ⟨i, fun gh hgh hle => ?_, ?_⟩
  · have := attribution (A.pt x).1 (G.g (V i)) gh.1 (A.pt x).2 G.thr A.ε hle hi
    linarith [hattr gh hgh]
  · have hm : G.thr + A.c ≤ inner ℝ (A.pt x).1 (G.g (V i)) := not_lt.1 (h1 i hi)
    set pr := L2probe A.m G.thr A.εL A.c (A.pt x).1 (A.Φ x) with hpr
    have hagree : ∀ k < qL G A, orcK0 G V (pr (runP pr (oneOrc G (G.g (V i))) k)) =
        oneOrc G (G.g (V i)) (pr (runP pr (oneOrc G (G.g (V i))) k)) := by
      intro k hk
      have hy : pr (runP pr (oneOrc G (G.g (V i))) k) ∈ Pset G A x (G.g (V i)) :=
        Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, rfl⟩
      unfold orcK0 oneOrc
      rw [decide_eq_decide]
      constructor
      · rintro ⟨j, hj⟩
        by_cases hji : j = i
        · subst hji; exact hj
        · exact absurd hj (h3 i j (Ne.symm hji) hi _ hy)
      · intro h; exact ⟨i, h⟩
    have heq : L2 A.m G.thr A.εL A.c (A.pt x).1 (A.Φ x) (orcK0 G V) =
        L2 A.m G.thr A.εL A.c (A.pt x).1 (A.Φ x) (oneOrc G (G.g (V i))) := by
      rw [← L2fromAns_L2run, ← L2fromAns_L2run]
      unfold L2run
      exact congrArg _ (runP_congr _ _ _ (qL G A) hagree)
    have hcor := L2_correct A.m (by rw [hdim]) (A.pt x).1 (A.Φ x) (hΦ x) (G.g (V i)) (G.hg _)
      G.thr ht0 ht1 A.c hc hc1 hm A.εL hεL
    have hcor' : ‖L2 A.m G.thr A.εL A.c (A.pt x).1 (A.Φ x) (orcK0 G V) - G.g (V i)‖ ≤ A.εL := by
      rw [heq]; exact hcor
    have hunit : ‖L2 A.m G.thr A.εL A.c (A.pt x).1 (A.Φ x) (orcK0 G V)‖ = 1 := by
      rcases L2_norm_or A.m G.thr A.εL A.c (A.pt x).1 (A.Φ x) (orcK0 G V) with h | h
      · exact h
      · rw [h, zero_sub, norm_neg, G.hg] at hcor'; linarith
    unfold outp
    rw [toSph_of_norm A.dflt hunit]
    exact hcor'.trans hεLε

lemma NF_le_append (V : ι → Fine) (F : List (Sph E)) (a : Sph E) :
    NF G A V F ≤ NF G A V (F ++ [a]) := by
  classical
  unfold NF
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  obtain ⟨gh, hgh, h⟩ := hi
  exact ⟨gh, List.mem_append_left _ hgh, h⟩

lemma NF_succ (V : ι → Fine) (F : List (Sph E)) (a : Sph E) (i : ι)
    (hnot : ∀ gh ∈ F, ¬ ‖gh.1 - G.g (V i)‖ ≤ A.ε) (ha : ‖a.1 - G.g (V i)‖ ≤ A.ε) :
    NF G A V F + 1 ≤ NF G A V (F ++ [a]) := by
  classical
  unfold NF
  have hi : i ∉ univ.filter fun i => ∃ gh ∈ F, ‖gh.1 - G.g (V i)‖ ≤ A.ε := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    exact hnot
  rw [← Finset.card_insert_of_notMem hi]
  refine Finset.card_le_card fun j hj => ?_
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  rcases hj with rfl | ⟨gh, hgh, h⟩
  · exact ⟨a, by simp, ha⟩
  · exact ⟨gh, List.mem_append_left _ hgh, h⟩

/-- **Lemma 4′.** For every search sequence and every `V`: `L ≤ N_ε + B_d`. -/
theorem lemma4' (hdim : Module.finrank ℝ E = A.m + 2)
    (hΦ : ∀ x, Orthonormal ℝ (Fin.cons (A.pt x).1 (A.Φ x) : Fin (A.m + 2) → E))
    (ht0 : 0 < G.thr) (ht1 : G.thr < 1) (hc : 0 < A.c) (hc1 : G.thr + A.c < 1)
    (hεL : 0 < A.εL) (hεLε : A.εL ≤ A.ε) (hεL1 : A.εL < 1) (V : ι → Fine) (l : List X) :
    ((Fof G A V l).length : ℝ) ≤ Neps G A V l + Bd G A V l := by
  classical
  induction l using List.reverseRecOn with
  | nil => simp [Fof, runSt_nil, Bd, cnt_nil]
  | append_singleton l x ih =>
    unfold Neps Bd at *
    unfold Fof at *
    rw [runSt_snoc, cnt_snoc]
    set F := runSt (stepA G A V) [] l
    by_cases hcond : F.length < A.M ∧ launches G A V F x
    · have hst : stepA G A V F x = F ++ [outp G A V x] := by unfold stepA; rw [if_pos hcond]
      rw [hst]
      simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      by_cases hb : Bad G A V x
      · rw [ind_pos ⟨hcond.1, hcond.2, hb⟩]
        have := NF_le_append G A V F (outp G A V x)
        have : (NF G A V F : ℝ) ≤ NF G A V (F ++ [outp G A V x]) := by exact_mod_cast this
        linarith
      · rw [ind_neg (fun h => hb h.2.2)]
        obtain ⟨i, hnot, hrec⟩ := good_launch G A hdim hΦ ht0 ht1 hc hc1 hεL hεLε hεL1 V F x
          hcond.2 hb
        have := NF_succ G A V F (outp G A V x) i hnot hrec
        have : (NF G A V F : ℝ) + 1 ≤ NF G A V (F ++ [outp G A V x]) := by exact_mod_cast this
        linarith
    · have hst : stepA G A V F x = F := by unfold stepA; rw [if_neg hcond]
      rw [hst, ind_neg (fun h => hcond ⟨h.1, h.2.1⟩)]
      linarith


/-! #### Masses -/

/-- `x` reaches entry `i` of `V`. -/
def rch (V : ι → Fine) (x : X) (i : ι) : Prop := G.thr < inner ℝ (A.pt x).1 (G.g (V i))

/-- `Δ(V) = Σ_{i<i'} ν(Cᵢ ∩ Cᵢ')`, written as `½ Σ_{i≠i'}`. -/
noncomputable def Delta (ν : X → ℝ) (V : ι → Fine) : ℝ :=
  (1 / 2) * ∑ i, ∑ i', if i ≠ i' then ∑ x, ν x * ind (rch G A V x i ∧ rch G A V x i') else 0

/-- `I_{ii'}(V) = ν{x : x ∈ Cᵢ, P(x, gᵢ) ∩ C_{i'} ≠ ∅}`. -/
noncomputable def Iint (ν : X → ℝ) (V : ι → Fine) (i i' : ι) : ℝ :=
  ∑ x, ν x * ind (rch G A V x i ∧ ∃ y ∈ Pset G A x (G.g (V i)), G.thr < inner ℝ y (G.g (V i')))

/-- `Z(V) = Δ(V) + Σ_{i≠i'} I_{ii'}(V)`. -/
noncomputable def Zf (ν : X → ℝ) (V : ι → Fine) : ℝ :=
  Delta G A ν V + ∑ i, ∑ i', if i ≠ i' then Iint G A ν V i i' else 0

variable {G A} {ν : X → ℝ}

lemma Delta_pointwise (V : ι → Fine) :
    Delta G A ν V = ∑ x, ν x * ((1 / 2) *
      ∑ i, ∑ i', if i ≠ i' then ind (rch G A V x i) * ind (rch G A V x i') else 0) := by
  unfold Delta
  have hswap : ∑ x, ν x * ∑ i, ∑ i', (if i ≠ i' then ind (rch G A V x i) * ind (rch G A V x i')
      else 0) = ∑ i, ∑ i', ∑ x, ν x * (if i ≠ i' then ind (rch G A V x i) *
        ind (rch G A V x i') else 0) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  calc (1 / 2) * ∑ i, ∑ i', (if i ≠ i' then ∑ x, ν x * ind (rch G A V x i ∧ rch G A V x i')
        else 0)
      = (1 / 2) * ∑ i, ∑ i', ∑ x, ν x * (if i ≠ i' then ind (rch G A V x i) *
        ind (rch G A V x i') else 0) := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
        split_ifs
        · simp only [ind_and]
        · simp
    _ = _ := by
        rw [← hswap, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring

lemma Delta_nonneg (hν0 : ∀ x, 0 ≤ ν x) (V : ι → Fine) : 0 ≤ Delta G A ν V := by
  rw [Delta_pointwise]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hν0 x)
    (mul_nonneg (by norm_num) (pair_sum_nonneg _))

lemma Iint_nonneg (hν0 : ∀ x, 0 ≤ ν x) (V : ι → Fine) (i i' : ι) : 0 ≤ Iint G A ν V i i' :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hν0 x) (ind_nonneg _)

lemma Zf_nonneg (hν0 : ∀ x, 0 ≤ ν x) (V : ι → Fine) : 0 ≤ Zf G A ν V :=
  add_nonneg (Delta_nonneg hν0 V) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ => by
    split_ifs
    · exact Iint_nonneg hν0 V i i'
    · exact le_rfl)

/-- Pushing a list sum through the `ν`-sum. -/
lemma sum_mul_listSum (F : List (Sph E)) (f : Sph E → X → ℝ) :
    ∑ x, ν x * (F.map fun gh => f gh x).sum = (F.map fun gh => ∑ x, ν x * f gh x).sum := by
  induction F with
  | nil => simp
  | cons a F ih => simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih]

/-! #### Lemma 5 (launch rate) -/

/-- **Lemma 5.** For `V` in the support of the prior and any list `F` of (unit) outputs,
`ν{x launches} ≥ nq − |F|ν₁ − Δ(V)`. -/
theorem lemma5 (hν0 : ∀ x, 0 ≤ ν x) (hε : 0 ≤ A.ε) (q ν₁ : ℝ)
    (H1 : ∀ i l, G.π i l ≠ 0 → q ≤ ∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0)
    (H5 : ∀ y : Sph E,
      (∑ x, if G.thr - 2 * A.ε < inner ℝ (A.pt x).1 y.1 then ν x else 0) ≤ ν₁)
    (V : ι → Fine) (hV : ∀ i, G.π i (V i) ≠ 0) (F : List (Sph E)) :
    (Fintype.card ι : ℝ) * q - F.length * ν₁ - Delta G A ν V ≤
      ∑ x, ν x * ind (launches G A V F x) := by
  classical
  -- pointwise: 1{launch} ≥ 1{∃ reach} − Σ_{ĝ∈F} 1{t−ε < ⟨x,ĝ⟩}
  have hpt : ∀ x, ind (∃ i, rch G A V x i) -
      (F.map fun gh => ind (G.thr - A.ε < inner ℝ (A.pt x).1 gh.1)).sum
        ≤ ind (launches G A V F x) := by
    intro x
    have hnn : ∀ y ∈ F.map (fun gh => ind (G.thr - A.ε < inner ℝ (A.pt x).1 gh.1)), 0 ≤ y := by
      intro y hy; obtain ⟨gh, -, rfl⟩ := List.mem_map.1 hy; exact ind_nonneg _
    by_cases hl : launches G A V F x
    · rw [ind_pos hl]; linarith [ind_le_one (∃ i, rch G A V x i), List.sum_nonneg hnn]
    · by_cases hr : ∃ i, rch G A V x i
      · have : ∃ gh ∈ F, G.thr - A.ε < inner ℝ (A.pt x).1 gh.1 := by
          by_contra hc; push Not at hc; exact hl ⟨hr, hc⟩
        obtain ⟨gh, hgh, hlt⟩ := this
        have h1 : ind (G.thr - A.ε < inner ℝ (A.pt x).1 gh.1) ≤
            (F.map fun gh => ind (G.thr - A.ε < inner ℝ (A.pt x).1 gh.1)).sum :=
          List.single_le_sum hnn _ (List.mem_map.2 ⟨gh, hgh, rfl⟩)
        rw [ind_pos hlt] at h1
        rw [ind_pos hr, ind_neg hl]; linarith
      · rw [ind_neg hr, ind_neg hl]; linarith [List.sum_nonneg hnn]
  -- Bonferroni
  have hbon : ∀ x, ∑ i, ind (rch G A V x i) - (1 / 2) * ∑ i, ∑ i',
      (if i ≠ i' then ind (rch G A V x i) * ind (rch G A V x i') else 0)
        ≤ ind (∃ i, rch G A V x i) := fun x => bonferroni (rch G A V x)
  -- each attribution cap has mass ≤ ν₁
  have hcap : ∀ gh : Sph E, ∑ x, ν x * ind (G.thr - A.ε < inner ℝ (A.pt x).1 gh.1) ≤ ν₁ := by
    intro gh
    refine le_trans (Finset.sum_le_sum fun x _ => ?_) (H5 gh)
    rw [mul_ind]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (by linarith) h2
    · exact hν0 x
    · exact le_rfl
  have hcaps : (F.map fun gh => ∑ x, ν x * ind (G.thr - A.ε < inner ℝ (A.pt x).1 gh.1)).sum
      ≤ F.length * ν₁ := by
    have := List.sum_le_card_nsmul (F.map fun gh => ∑ x, ν x *
      ind (G.thr - A.ε < inner ℝ (A.pt x).1 gh.1)) ν₁ (by
        intro y hy; obtain ⟨gh, -, rfl⟩ := List.mem_map.1 hy; exact hcap gh)
    simpa [nsmul_eq_mul] using this
  have hreach : (Fintype.card ι : ℝ) * q ≤ ∑ i, ∑ x, ν x * ind (rch G A V x i) := by
    have : ∀ i, q ≤ ∑ x, ν x * ind (rch G A V x i) := by
      intro i
      refine le_of_le_of_eq (H1 i (V i) (hV i)) (Finset.sum_congr rfl fun x _ => ?_)
      rw [mul_ind]; rfl
    have := Finset.sum_le_sum fun i (_ : i ∈ univ) => this i
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  -- assemble
  have key : ∀ x, ν x * (∑ i, ind (rch G A V x i)) - ν x * ((1 / 2) * ∑ i, ∑ i',
      (if i ≠ i' then ind (rch G A V x i) * ind (rch G A V x i') else 0)) -
      ν x * (F.map fun gh => ind (G.thr - A.ε < inner ℝ (A.pt x).1 gh.1)).sum
        ≤ ν x * ind (launches G A V F x) := by
    intro x
    have h := mul_le_mul_of_nonneg_left (show (∑ i, ind (rch G A V x i) - (1 / 2) * ∑ i, ∑ i',
      (if i ≠ i' then ind (rch G A V x i) * ind (rch G A V x i') else 0)) -
      (F.map fun gh => ind (G.thr - A.ε < inner ℝ (A.pt x).1 gh.1)).sum
        ≤ ind (launches G A V F x) by linarith [hbon x, hpt x]) (hν0 x)
    linarith [h]
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ univ) => key x
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_mul_listSum, ← Delta_pointwise] at hsum
  have hswap : ∑ x, ν x * ∑ i, ind (rch G A V x i) = ∑ i, ∑ x, ν x * ind (rch G A V x i) := by
    simp only [Finset.mul_sum]; rw [Finset.sum_comm]
  rw [hswap] at hsum
  linarith


/-! #### Lemma 6 (bad rate) -/

omit [Fintype ι] [Nonempty ι] in
lemma sum_mul_pairs [Fintype ι] {T : Type*} [Fintype T] (w : T → ℝ) (a : T → ι → ι → ℝ) :
    ∑ v, w v * ∑ i, ∑ i', (if i ≠ i' then a v i i' else 0) =
      ∑ i, ∑ i', if i ≠ i' then ∑ v, w v * a v i i' else 0 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => ?_
  split_ifs <;> simp

omit [Nonempty ι] in
lemma pair_count (c : ℝ) :
    ∑ i : ι, ∑ i' : ι, (if i ≠ i' then c else 0) =
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * c := by
  have : ∀ i : ι, ∑ i' : ι, (if i ≠ i' then c else 0) = (Fintype.card ι : ℝ) * c - c := by
    intro i
    have h1 : ∀ i' : ι, (if i ≠ i' then c else 0) = c - (if i = i' then c else 0) := by
      intro i'; by_cases h : i = i' <;> simp [h]
    simp only [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

omit [Nonempty ι] in
lemma pair_le (b : ι → ι → ℝ) (c : ℝ) (h : ∀ i i', i ≠ i' → b i i' ≤ c) :
    ∑ i : ι, ∑ i' : ι, (if i ≠ i' then b i i' else 0) ≤
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * c := by
  rw [← pair_count]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => ?_
  split_ifs with hh
  · exact h i i' hh
  · exact le_rfl

/-- **Lemma 6 (rate).** For `V` in the support: `ν(Bad(V)) ≤ γ n qbar + Z(V)`. -/
theorem lemma6_rate (hν0 : ∀ x, 0 ≤ ν x) (hc : 0 < A.c) (γ qbar : ℝ) (hγ0 : 0 ≤ γ)
    (H2 : ∀ i l, G.π i l ≠ 0 →
      (1 - γ) * (∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0) ≤
        ∑ x, if G.thr + A.c ≤ inner ℝ (A.pt x).1 (G.g l) then ν x else 0)
    (H4 : ∀ i l, G.π i l ≠ 0 →
      (∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0) ≤ qbar)
    (V : ι → Fine) (hV : ∀ i, G.π i (V i) ≠ 0) :
    ∑ x, ν x * ind (Bad G A V x) ≤ γ * Fintype.card ι * qbar + Zf G A ν V := by
  classical
  set F1 : X → ι → Prop := fun x i =>
    rch G A V x i ∧ inner ℝ (A.pt x).1 (G.g (V i)) < G.thr + A.c with hF1
  set F3 : X → ι → ι → Prop := fun x i i' =>
    rch G A V x i ∧ ∃ y ∈ Pset G A x (G.g (V i)), G.thr < inner ℝ y (G.g (V i')) with hF3
  have hpt : ∀ x, ind (Bad G A V x) ≤ ∑ i, ind (F1 x i) + (1 / 2) * ∑ i, ∑ i',
      (if i ≠ i' then ind (rch G A V x i) * ind (rch G A V x i') else 0) +
      ∑ i, ∑ i', (if i ≠ i' then ind (F3 x i i') else 0) := by
    intro x
    have n1 : 0 ≤ ∑ i, ind (F1 x i) := Finset.sum_nonneg fun i _ => ind_nonneg _
    have n2 := pair_sum_nonneg (rch G A V x)
    have n3 : 0 ≤ ∑ i, ∑ i', (if i ≠ i' then ind (F3 x i i') else 0) := by
      refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ => ?_
      split_ifs
      · exact ind_nonneg _
      · exact le_rfl
    by_cases hb : Bad G A V x
    · rw [ind_pos hb]
      rcases hb with ⟨i, hi⟩ | ⟨i, i', hii, hi, hi'⟩ | ⟨i, i', hii, hi, y, hy, hy'⟩
      · have := Finset.single_le_sum (f := fun i => ind (F1 x i)) (fun i _ => ind_nonneg _)
          (Finset.mem_univ i)
        rw [ind_pos (show F1 x i from hi)] at this
        nlinarith
      · have := pair_sum_ge_two (rch G A V x) i i' hii hi hi'
        nlinarith
      · have h1 := Finset.single_le_sum (f := fun i' => (if i ≠ i' then ind (F3 x i i') else 0))
          (fun i' _ => by split_ifs; exacts [ind_nonneg _, le_rfl]) (Finset.mem_univ i')
        have h2 := Finset.single_le_sum
          (f := fun i => ∑ i', (if i ≠ i' then ind (F3 x i i') else 0))
          (fun i _ => Finset.sum_nonneg fun i' _ => by split_ifs; exacts [ind_nonneg _, le_rfl])
          (Finset.mem_univ i)
        simp only [if_pos hii, ind_pos (show F3 x i i' from ⟨hi, y, hy, hy'⟩)] at h1 h2
        nlinarith
    · rw [ind_neg hb]; nlinarith
  -- F1 mass
  have hF1m : ∀ i, ∑ x, ν x * ind (F1 x i) ≤ γ * qbar := by
    intro i
    have hsplit : ∀ x, ν x * ind (F1 x i) = (if G.thr < inner ℝ (A.pt x).1 (G.g (V i)) then ν x
        else 0) - (if G.thr + A.c ≤ inner ℝ (A.pt x).1 (G.g (V i)) then ν x else 0) := by
      intro x
      simp only [hF1, rch]
      by_cases h1 : G.thr < inner ℝ (A.pt x).1 (G.g (V i)) <;>
        by_cases h2 : G.thr + A.c ≤ inner ℝ (A.pt x).1 (G.g (V i))
      · rw [ind_neg (fun h => absurd h.2 (not_lt.2 h2)), if_pos h1, if_pos h2]; ring
      · rw [ind_pos ⟨h1, not_le.1 h2⟩, if_pos h1, if_neg h2]; ring
      · exact absurd (by linarith) h1
      · rw [ind_neg (fun h => h1 h.1), if_neg h1, if_neg h2]; ring
    rw [Finset.sum_congr rfl fun x _ => hsplit x, Finset.sum_sub_distrib]
    have h2 := H2 i (V i) (hV i)
    have h4 := H4 i (V i) (hV i)
    nlinarith
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ univ) =>
    mul_le_mul_of_nonneg_left (hpt x) (hν0 x)
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  have e1 : ∑ x, ν x * ∑ i, ind (F1 x i) = ∑ i, ∑ x, ν x * ind (F1 x i) := by
    simp only [Finset.mul_sum]; rw [Finset.sum_comm]
  have e2 : ∑ x, ν x * ((1 / 2) * ∑ i, ∑ i',
      (if i ≠ i' then ind (rch G A V x i) * ind (rch G A V x i') else 0)) = Delta G A ν V :=
    (Delta_pointwise V).symm
  have e3 : ∑ x, ν x * ∑ i, ∑ i', (if i ≠ i' then ind (F3 x i i') else 0) =
      ∑ i, ∑ i', (if i ≠ i' then Iint G A ν V i i' else 0) := by
    rw [sum_mul_pairs]; rfl
  rw [e1, e2, e3] at hsum
  have hF1s : ∑ i, ∑ x, ν x * ind (F1 x i) ≤ Fintype.card ι * (γ * qbar) := by
    have := Finset.sum_le_sum fun i (_ : i ∈ univ) => hF1m i
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  unfold Zf
  nlinarith

omit [Nonempty ι] in
/-- Two-coordinate marginal of the product prior, product form. -/
lemma prior_two (i i' : ι) (hii : i ≠ i') (F H : Fine → ℝ) :
    ∑ V, G.prior V * (F (V i) * H (V i')) = (∑ l, G.π i l * F l) * (∑ l, G.π i' l * H l) := by
  classical
  set w : ι → Fine → ℝ := fun j l =>
    G.π j l * (if j = i then F l else 1) * (if j = i' then H l else 1) with hw
  have h1 : ∀ V : ι → Fine, G.prior V * (F (V i) * H (V i')) = ∏ j, w j (V j) := by
    intro V
    simp only [hw, Finset.prod_mul_distrib, Gallery.prior]
    rw [Finset.prod_ite_eq' Finset.univ i (fun j => F (V j)),
      Finset.prod_ite_eq' Finset.univ i' (fun j => H (V j))]
    simp only [Finset.mem_univ, if_true]
    ring
  rw [Finset.sum_congr rfl fun V _ => h1 V, ← Fintype.prod_sum]
  have h2 : ∀ j, ∑ l, w j l = (if j = i then ∑ l, G.π i l * F l else 1) *
      (if j = i' then ∑ l, G.π i' l * H l else 1) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [hw, hii]
    · by_cases hj' : j = i'
      · subst hj'; simp [hw, hj]
      · simp [hw, hj, hj', G.hπ1 j]
  rw [Finset.prod_congr rfl fun j _ => h2 j, Finset.prod_mul_distrib, Finset.prod_ite_eq',
    Finset.prod_ite_eq']
  simp

omit [Nonempty ι] in
/-- Two-coordinate marginal of the product prior, general form. -/
lemma prior_two' (i i' : ι) (hii : i ≠ i') (f : Fine → Fine → ℝ) :
    ∑ V, G.prior V * f (V i) (V i') = ∑ l, ∑ l', G.π i l * G.π i' l' * f l l' := by
  classical
  have hdec : ∀ V : ι → Fine, f (V i) (V i') = ∑ l, ∑ l',
      f l l' * ((if V i = l then 1 else 0) * (if V i' = l' then 1 else 0)) := by
    intro V
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (V i) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    rw [Finset.sum_eq_single (V i') (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  simp only [hdec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' _ => ?_
  have := prior_two (G := G) i i' hii (fun m => if m = l then 1 else 0) (fun m => if m = l' then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  calc ∑ V, G.prior V * (f l l' * ((if V i = l then 1 else 0) * (if V i' = l' then 1 else 0)))
      = f l l' * ∑ V, G.prior V * ((if V i = l then 1 else 0) * (if V i' = l' then 1 else 0)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun V _ => by ring
    _ = _ := by
        have h' : ∑ V, G.prior V * ((if V i = l then (1:ℝ) else 0) * (if V i' = l' then 1 else 0))
            = G.π i l * G.π i' l' := by
          rw [← this]; refine Finset.sum_congr rfl fun V _ => ?_
          split_ifs <;> simp
        rw [h']; ring

lemma mu_nonneg (y0 : Sph E) (μ₁ : ℝ)
    (H3 : ∀ i (y : Sph E), (∑ l, if G.thr < inner ℝ y.1 (G.g l) then G.π i l else 0) ≤ μ₁) :
    0 ≤ μ₁ := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  refine le_trans (Finset.sum_nonneg fun l _ => ?_) (H3 i y0)
  split_ifs
  · exact G.hπ0 i l
  · exact le_rfl

lemma support_mass (qbar : ℝ)
    (H4 : ∀ i l, G.π i l ≠ 0 →
      (∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0) ≤ qbar) (i : ι) :
    ∑ l, G.π i l * ∑ x, ν x * ind (G.thr < inner ℝ (A.pt x).1 (G.g l)) ≤ qbar := by
  have : ∀ l, G.π i l * ∑ x, ν x * ind (G.thr < inner ℝ (A.pt x).1 (G.g l)) ≤ G.π i l * qbar := by
    intro l
    by_cases hl : G.π i l = 0
    · rw [hl]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (G.hπ0 i l)
      refine le_of_eq_of_le (Finset.sum_congr rfl fun x _ => ?_) (H4 i l hl)
      rw [mul_ind]
  refine le_of_le_of_eq (Finset.sum_le_sum fun l _ => this l) ?_
  rw [← Finset.sum_mul, G.hπ1 i, one_mul]

/-- **Lemma 6 (Δ).** `E Δ ≤ D = n(n−1)μ₁qbar/2`. -/
theorem lemma6_Delta (hν0 : ∀ x, 0 ≤ ν x) (μ₁ qbar : ℝ)
    (H3 : ∀ i (y : Sph E), (∑ l, if G.thr < inner ℝ y.1 (G.g l) then G.π i l else 0) ≤ μ₁)
    (H4 : ∀ i l, G.π i l ≠ 0 →
      (∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0) ≤ qbar) :
    ∑ V, G.prior V * Delta G A ν V ≤
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * μ₁ * qbar / 2 := by
  classical
  have hμ := mu_nonneg A.dflt μ₁ H3
  unfold Delta
  have e : ∑ V, G.prior V * ((1 / 2) * ∑ i, ∑ i',
      (if i ≠ i' then ∑ x, ν x * ind (rch G A V x i ∧ rch G A V x i') else 0)) =
      (1 / 2) * ∑ i, ∑ i', (if i ≠ i' then ∑ V, G.prior V *
        ∑ x, ν x * ind (rch G A V x i ∧ rch G A V x i') else 0) := by
    rw [← sum_mul_pairs, Finset.mul_sum]
    exact Finset.sum_congr rfl fun V _ => by ring
  rw [e]
  have hb : ∀ i i', i ≠ i' → ∑ V, G.prior V *
      ∑ x, ν x * ind (rch G A V x i ∧ rch G A V x i') ≤ μ₁ * qbar := by
    intro i i' hii
    have e1 : ∑ V, G.prior V * ∑ x, ν x * ind (rch G A V x i ∧ rch G A V x i') =
        ∑ x, ν x * ((∑ l, G.π i l * ind (G.thr < inner ℝ (A.pt x).1 (G.g l))) *
          (∑ l, G.π i' l * ind (G.thr < inner ℝ (A.pt x).1 (G.g l)))) := by
      calc ∑ V, G.prior V * ∑ x, ν x * ind (rch G A V x i ∧ rch G A V x i')
          = ∑ V, ∑ x, G.prior V * (ν x * ind (rch G A V x i ∧ rch G A V x i')) := by
            simp only [Finset.mul_sum]
        _ = ∑ x, ∑ V, G.prior V * (ν x * ind (rch G A V x i ∧ rch G A V x i')) :=
            Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [← prior_two (G := G) i i' hii, Finset.mul_sum]
            refine Finset.sum_congr rfl fun V _ => ?_
            simp only [rch, ind_and]; ring
    rw [e1]
    have hx : ∀ x, ν x * ((∑ l, G.π i l * ind (G.thr < inner ℝ (A.pt x).1 (G.g l))) *
          (∑ l, G.π i' l * ind (G.thr < inner ℝ (A.pt x).1 (G.g l)))) ≤
        μ₁ * ∑ l, G.π i' l * (ν x * ind (G.thr < inner ℝ (A.pt x).1 (G.g l))) := by
      intro x
      have hm : ∑ l, G.π i l * ind (G.thr < inner ℝ (A.pt x).1 (G.g l)) ≤ μ₁ := by
        refine le_of_eq_of_le (Finset.sum_congr rfl fun l _ => ?_) (H3 i (A.pt x))
        rw [mul_ind]
      have hn : 0 ≤ ∑ l, G.π i' l * ind (G.thr < inner ℝ (A.pt x).1 (G.g l)) :=
        Finset.sum_nonneg fun l _ => mul_nonneg (G.hπ0 _ _) (ind_nonneg _)
      have : ∑ l, G.π i' l * (ν x * ind (G.thr < inner ℝ (A.pt x).1 (G.g l))) =
          ν x * ∑ l, G.π i' l * ind (G.thr < inner ℝ (A.pt x).1 (G.g l)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
      rw [this]
      have := mul_le_mul_of_nonneg_right hm hn
      have := mul_le_mul_of_nonneg_left this (hν0 x)
      linarith
    refine le_trans (Finset.sum_le_sum fun x _ => hx x) ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    have : ∑ l, ∑ x, G.π i' l * (ν x * ind (G.thr < inner ℝ (A.pt x).1 (G.g l))) =
        ∑ l, G.π i' l * ∑ x, ν x * ind (G.thr < inner ℝ (A.pt x).1 (G.g l)) := by
      simp only [Finset.mul_sum]
    rw [this]
    exact mul_le_mul_of_nonneg_left (support_mass qbar H4 i') hμ
  have := pair_le _ (μ₁ * qbar) hb
  nlinarith

lemma Pset_unit (hΦ : ∀ x, Orthonormal ℝ (Fin.cons (A.pt x).1 (A.Φ x) : Fin (A.m + 2) → E))
    (x : X) (gl : E) (y : E) (hy : y ∈ Pset G A x gl) : ‖y‖ = 1 := by
  classical
  unfold Pset at hy
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hy
  exact norm_L2probe (hΦ x) _ _ _ _

lemma Pset_card (x : X) (gl : E) : (Pset G A x gl).card ≤ qL G A := by
  classical
  unfold Pset
  exact (Finset.card_image_le).trans (Finset.card_range _).le

/-- **Lemma 6 (Z).** `E Z ≤ Z̄ = n(n−1)qbarμ₁(½ + Q_loc)`. -/
theorem lemma6_Z (hν0 : ∀ x, 0 ≤ ν x)
    (hΦ : ∀ x, Orthonormal ℝ (Fin.cons (A.pt x).1 (A.Φ x) : Fin (A.m + 2) → E)) (μ₁ qbar : ℝ)
    (H3 : ∀ i (y : Sph E), (∑ l, if G.thr < inner ℝ y.1 (G.g l) then G.π i l else 0) ≤ μ₁)
    (H4 : ∀ i l, G.π i l ≠ 0 →
      (∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0) ≤ qbar) :
    ∑ V, G.prior V * Zf G A ν V ≤
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * qbar * μ₁ * (1 / 2 + qL G A) := by
  classical
  have hμ := mu_nonneg A.dflt μ₁ H3
  have hD := lemma6_Delta hν0 μ₁ qbar H3 H4
  unfold Zf
  simp only [mul_add, Finset.sum_add_distrib]
  rw [sum_mul_pairs]
  have hb : ∀ i i', i ≠ i' → ∑ V, G.prior V * Iint G A ν V i i' ≤ qL G A * μ₁ * qbar := by
    intro i i' hii
    -- the per-`(x, l)` bound
    have hxl : ∀ x l, ∑ l', G.π i' l' * ind (G.thr < inner ℝ (A.pt x).1 (G.g l) ∧
        ∃ y ∈ Pset G A x (G.g l), G.thr < inner ℝ y (G.g l')) ≤
          ind (G.thr < inner ℝ (A.pt x).1 (G.g l)) * (qL G A * μ₁) := by
      intro x l
      by_cases hr : G.thr < inner ℝ (A.pt x).1 (G.g l)
      · rw [ind_pos hr, one_mul]
        have h1 : ∀ l', G.π i' l' * ind (G.thr < inner ℝ (A.pt x).1 (G.g l) ∧
            ∃ y ∈ Pset G A x (G.g l), G.thr < inner ℝ y (G.g l')) ≤
              ∑ y ∈ Pset G A x (G.g l), G.π i' l' * ind (G.thr < inner ℝ y (G.g l')) := by
          intro l'
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (G.hπ0 _ _)
          by_cases he : ∃ y ∈ Pset G A x (G.g l), G.thr < inner ℝ y (G.g l')
          · obtain ⟨y, hy, hy'⟩ := he
            rw [ind_pos ⟨hr, y, hy, hy'⟩]
            have := Finset.single_le_sum (f := fun y => ind (G.thr < inner ℝ y (G.g l')))
              (fun y _ => ind_nonneg _) hy
            simp only [ind_pos hy'] at this
            exact this
          · rw [ind_neg (fun h => he h.2)]
            exact Finset.sum_nonneg fun y _ => ind_nonneg _
        refine le_trans (Finset.sum_le_sum fun l' _ => h1 l') ?_
        rw [Finset.sum_comm]
        have h2 : ∀ y ∈ Pset G A x (G.g l),
            ∑ l', G.π i' l' * ind (G.thr < inner ℝ y (G.g l')) ≤ μ₁ := by
          intro y hy
          refine le_of_eq_of_le (Finset.sum_congr rfl fun l' _ => ?_)
            (H3 i' ⟨y, Pset_unit hΦ x _ y hy⟩)
          rw [mul_ind]
        refine le_trans (Finset.sum_le_sum h2) ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Pset G A x (G.g l)).card : ℝ) ≤ (qL G A : ℝ) :=
          Nat.cast_le.2 (Pset_card (G := G) (A := A) x (G.g l))
        exact mul_le_mul_of_nonneg_right hcard hμ
      · rw [ind_neg hr, zero_mul]
        exact le_of_eq (Finset.sum_eq_zero fun l' _ => by rw [ind_neg (fun h => hr h.1), mul_zero])
    have e1 : ∑ V, G.prior V * Iint G A ν V i i' = ∑ x, ν x * ∑ l, ∑ l', G.π i l * G.π i' l' *
        ind (G.thr < inner ℝ (A.pt x).1 (G.g l) ∧
          ∃ y ∈ Pset G A x (G.g l), G.thr < inner ℝ y (G.g l')) := by
      unfold Iint
      calc ∑ V, G.prior V * ∑ x, ν x * ind (rch G A V x i ∧ ∃ y ∈ Pset G A x (G.g (V i)),
            G.thr < inner ℝ y (G.g (V i')))
          = ∑ V, ∑ x, G.prior V * (ν x * ind (rch G A V x i ∧ ∃ y ∈ Pset G A x (G.g (V i)),
            G.thr < inner ℝ y (G.g (V i')))) := by simp only [Finset.mul_sum]
        _ = ∑ x, ∑ V, G.prior V * (ν x * ind (rch G A V x i ∧ ∃ y ∈ Pset G A x (G.g (V i)),
            G.thr < inner ℝ y (G.g (V i')))) := Finset.sum_comm
        _ = _ := by
          refine Finset.sum_congr rfl fun x _ => ?_
          have := prior_two' (G := G) i i' hii (fun l l' => ν x *
            ind (G.thr < inner ℝ (A.pt x).1 (G.g l) ∧
              ∃ y ∈ Pset G A x (G.g l), G.thr < inner ℝ y (G.g l')))
          rw [show ∑ V, G.prior V * (ν x * ind (rch G A V x i ∧ ∃ y ∈ Pset G A x (G.g (V i)),
              G.thr < inner ℝ y (G.g (V i')))) = _ from this, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l' _ => by ring
    rw [e1]
    have hx : ∀ x, ν x * ∑ l, ∑ l', G.π i l * G.π i' l' *
        ind (G.thr < inner ℝ (A.pt x).1 (G.g l) ∧
          ∃ y ∈ Pset G A x (G.g l), G.thr < inner ℝ y (G.g l')) ≤
        qL G A * μ₁ * ∑ l, G.π i l * (ν x * ind (G.thr < inner ℝ (A.pt x).1 (G.g l))) := by
      intro x
      have : ∀ l, ∑ l', G.π i l * G.π i' l' *
          ind (G.thr < inner ℝ (A.pt x).1 (G.g l) ∧
            ∃ y ∈ Pset G A x (G.g l), G.thr < inner ℝ y (G.g l')) ≤
          G.π i l * (ind (G.thr < inner ℝ (A.pt x).1 (G.g l)) * (qL G A * μ₁)) := by
        intro l
        rw [← mul_le_mul_iff_of_pos_left (show (0:ℝ) < 1 by norm_num), one_mul, one_mul]
        have := mul_le_mul_of_nonneg_left (hxl x l) (G.hπ0 i l)
        refine le_of_eq_of_le ?_ this
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l' _ => by ring
      have := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l (_ : l ∈ univ) => this l) (hν0 x)
      refine this.trans (le_of_eq ?_)
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    refine le_trans (Finset.sum_le_sum fun x _ => hx x) ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    have : ∑ l, ∑ x, G.π i l * (ν x * ind (G.thr < inner ℝ (A.pt x).1 (G.g l))) =
        ∑ l, G.π i l * ∑ x, ν x * ind (G.thr < inner ℝ (A.pt x).1 (G.g l)) := by
      simp only [Finset.mul_sum]
    rw [this]
    have := mul_le_mul_of_nonneg_left (support_mass qbar H4 i)
      (mul_nonneg (Nat.cast_nonneg (qL G A)) hμ)
    linarith
  have := pair_le _ _ hb
  nlinarith


/-! #### Run bookkeeping -/

open Classical in
lemma stepA_length (V : ι → Fine) (F : List (Sph E)) (x : X) :
    (stepA G A V F x).length = F.length + if F.length < A.M ∧ launches G A V F x then 1 else 0 := by
  classical
  unfold stepA
  split_ifs <;> simp

lemma runSt_eq_Fof (V : ι → Fine) (l : List X) :
    runSt (stepA G A V) [] l = Fof G A V l := rfl

lemma Fof_snoc (V : ι → Fine) (l : List X) (x : X) :
    Fof G A V (l ++ [x]) = stepA G A V (Fof G A V l) x := runSt_snoc _ _ _ _

lemma Fof_length_mono (V : ι → Fine) (l : List X) (x : X) :
    (Fof G A V l).length ≤ (Fof G A V (l ++ [x])).length := by
  rw [Fof_snoc, stepA_length]; omega

lemma Fof_length_le (V : ι → Fine) (l : List X) : (Fof G A V l).length ≤ A.M := by
  induction l using List.reverseRecOn with
  | nil => simp [Fof, runSt_nil]
  | append_singleton l x ih =>
    rw [Fof_snoc, stepA_length]
    split_ifs with h
    · omega
    · omega

/-- Unfinished ⇒ every search round was active (`τ = K`). -/
lemma tau_eq_length (V : ι → Fine) (l : List X) (h : (Fof G A V l).length < A.M) :
    tau G A V l = l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [tau, cnt_nil]
  | append_singleton l x ih =>
    have hl : (Fof G A V l).length < A.M := lt_of_le_of_lt (Fof_length_mono V l x) h
    unfold tau at *
    rw [cnt_snoc, ih hl]
    rw [runSt_eq_Fof]
    rw [ind_pos hl]; simp

lemma tau_le_length (V : ι → Fine) (l : List X) : tau G A V l ≤ l.length :=
  cnt_le_length _ _ (fun _ _ => ind_le_one _) l

lemma tau_nonneg (V : ι → Fine) (l : List X) : 0 ≤ tau G A V l :=
  cnt_nonneg _ _ (fun _ _ => ind_nonneg _) l

/-- Queries: `τ + Q_loc·L`. -/
lemma queries_eq (V : ι → Fine) (l : List X) :
    queries G A V l = tau G A V l + qL G A * (Fof G A V l).length := by
  induction l using List.reverseRecOn with
  | nil => simp [queries, tau, cnt_nil, Fof, runSt_nil]
  | append_singleton l x ih =>
    unfold queries tau at *
    rw [cnt_snoc, cnt_snoc, ih, Fof_snoc, stepA_length]
    rw [runSt_eq_Fof]
    by_cases h1 : (Fof G A V l).length < A.M <;> by_cases h2 : launches G A V (Fof G A V l) x
    · rw [if_pos ⟨h1, h2⟩, ind_pos h1, ind_pos h2]; push_cast; ring
    · rw [if_neg (fun h => h2 h.2), ind_pos h1, ind_neg h2]; push_cast; ring
    · rw [if_neg (fun h => h1 h.1), ind_neg h1]; push_cast; ring
    · rw [if_neg (fun h => h1 h.1), ind_neg h1]; push_cast; ring

/-- **Deterministic query count**: at most `K + M·Q_loc`. -/
theorem queries_le (V : ι → Fine) (l : List X) :
    queries G A V l ≤ l.length + A.M * qL G A := by
  rw [queries_eq]
  have h1 := tau_le_length (G := G) (A := A) V l
  have h2 : ((Fof G A V l).length : ℝ) ≤ A.M := by exact_mod_cast Fof_length_le V l
  have h3 : (0:ℝ) ≤ qL G A := Nat.cast_nonneg _
  nlinarith

/-! #### Lemma 7 (Wald per stage) -/

/-- Stage `j` (`j < M`) contains at most one launch. -/
lemma stage_launch_le (V : ι → Fine) (j : ℕ) (hj : j < A.M) (l : List X) :
    cnt (stepA G A V) [] (fun F x => ind (F.length = j ∧ launches G A V F x)) l ≤
      ind (j < (Fof G A V l).length) := by
  induction l using List.reverseRecOn with
  | nil => rw [cnt_nil]; exact ind_nonneg _
  | append_singleton l x ih =>
    rw [cnt_snoc]
    rw [runSt_eq_Fof]
    by_cases h : (Fof G A V l).length = j ∧ launches G A V (Fof G A V l) x
    · rw [ind_pos h]
      have h0 : ¬ j < (Fof G A V l).length := by omega
      rw [ind_neg h0] at ih
      have hlen : j < (Fof G A V (l ++ [x])).length := by
        rw [Fof_snoc, stepA_length, if_pos ⟨by omega, h.2⟩]; omega
      rw [ind_pos hlen]; linarith
    · rw [ind_neg h, add_zero]
      exact ih.trans (ind_mono fun h' => lt_of_lt_of_le h' (Fof_length_mono V l x))

lemma nu1_nonneg (hν0 : ∀ x, 0 ≤ ν x) (ν₁ : ℝ)
    (H5 : ∀ y : Sph E,
      (∑ x, if G.thr - 2 * A.ε < inner ℝ (A.pt x).1 y.1 then ν x else 0) ≤ ν₁) : 0 ≤ ν₁ :=
  le_trans (Finset.sum_nonneg fun x _ => by split_ifs; exacts [hν0 x, le_rfl]) (H5 A.dflt)

lemma EK_ind_round (hν1 : ∑ x, ν x = 1) (p : List X → Prop) (s : ℕ) :
    EK ν s (fun l => ∑ x, ν x * ind (p l)) = EK ν s (fun l => ind (p l)) := by
  congr 1; funext l; rw [← Finset.sum_mul, hν1, one_mul]

/-- **Lemma 7, per stage**: `(a_j − Δ(V))·E[τ_j] ≤ 1`. -/
theorem lemma7_stage (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (hε : 0 ≤ A.ε) (q ν₁ : ℝ)
    (H1 : ∀ i l, G.π i l ≠ 0 → q ≤ ∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0)
    (H5 : ∀ y : Sph E,
      (∑ x, if G.thr - 2 * A.ε < inner ℝ (A.pt x).1 y.1 then ν x else 0) ≤ ν₁)
    (V : ι → Fine) (hV : ∀ i, G.π i (V i) ≠ 0) (K j : ℕ) (hj : j < A.M) :
    ((Fintype.card ι : ℝ) * q - j * ν₁ - Delta G A ν V) * EK ν K (tauj G A V j) ≤ 1 := by
  have hcnt := EK_cnt hν1 (stepA G A V) [] (fun F x => ind (F.length = j ∧ launches G A V F x)) K
  have hle : EK ν K (cnt (stepA G A V) [] (fun F x => ind (F.length = j ∧ launches G A V F x)))
      ≤ 1 := EK_le_const hν0 hν1 K fun l _ =>
        (stage_launch_le V j hj l).trans (ind_le_one _)
  have htau : EK ν K (tauj G A V j) =
      ∑ s ∈ range K, EK ν s (fun l => ind ((runSt (stepA G A V) [] l).length = j)) := by
    unfold tauj; rw [EK_cnt hν1]
    exact Finset.sum_congr rfl fun s _ => EK_ind_round hν1 _ s
  rw [htau, Finset.mul_sum]
  refine le_trans ?_ (hcnt ▸ hle)
  refine Finset.sum_le_sum fun s _ => ?_
  rw [← EK_mul]
  refine EK_mono hν0 s fun xs => ?_
  set F := runSt (stepA G A V) [] (List.ofFn xs)
  by_cases hF : F.length = j
  · rw [ind_pos hF, mul_one]
    have h5 := lemma5 hν0 hε q ν₁ H1 H5 V hV F
    rw [hF] at h5
    refine h5.trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
    congr 1
    by_cases hl : launches G A V F x
    · rw [ind_pos hl, ind_pos ⟨hF, hl⟩]
    · rw [ind_neg hl, ind_neg (fun h => hl h.2)]
  · rw [ind_neg hF, mul_zero]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hν0 x) (ind_nonneg _)

lemma tau_eq_sum (V : ι → Fine) (l : List X) :
    tau G A V l = ∑ j ∈ range A.M, tauj G A V j l := by
  unfold tau tauj
  rw [← cnt_sum]
  congr 1
  funext F x
  by_cases h : F.length < A.M
  · rw [ind_pos h, Finset.sum_eq_single F.length (fun b _ hb => ind_neg (Ne.symm hb))
      (fun hn => absurd (Finset.mem_range.2 h) hn), ind_pos rfl]
  · rw [ind_neg h]
    exact (Finset.sum_eq_zero fun j hj => ind_neg fun (he : F.length = j) =>
      h (by rw [he]; exact Finset.mem_range.1 hj)).symm

/-- **Lemma 7.** `E[τ | V] ≤ S + K·Δ(V)/a_{M−1}`. -/
theorem lemma7 (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (hε : 0 ≤ A.ε) (q ν₁ : ℝ)
    (H1 : ∀ i l, G.π i l ≠ 0 → q ≤ ∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0)
    (H5 : ∀ y : Sph E,
      (∑ x, if G.thr - 2 * A.ε < inner ℝ (A.pt x).1 y.1 then ν x else 0) ≤ ν₁)
    (ha : 0 < (Fintype.card ι : ℝ) * q - ((A.M : ℝ) - 1) * ν₁)
    (V : ι → Fine) (hV : ∀ i, G.π i (V i) ≠ 0) (K : ℕ) :
    EK ν K (tau G A V) ≤
      ∑ j ∈ range A.M, 1 / ((Fintype.card ι : ℝ) * q - j * ν₁) +
        K * Delta G A ν V / ((Fintype.card ι : ℝ) * q - ((A.M : ℝ) - 1) * ν₁) := by
  set n := (Fintype.card ι : ℝ)
  set aM := n * q - ((A.M : ℝ) - 1) * ν₁
  set Δ := Delta G A ν V
  have hν₁ := nu1_nonneg hν0 ν₁ H5
  have hΔ : 0 ≤ Δ := Delta_nonneg hν0 V
  have hsum : EK ν K (tau G A V) = ∑ j ∈ range A.M, EK ν K (tauj G A V j) := by
    rw [← EK_sum]; congr 1; funext l; exact tau_eq_sum V l
  have hK : EK ν K (tau G A V) ≤ K :=
    EK_le_const hν0 hν1 K fun l hl => hl ▸ tau_le_length V l
  have hj : ∀ j ∈ range A.M, EK ν K (tauj G A V j) ≤
      1 / (n * q - j * ν₁) + Δ * EK ν K (tauj G A V j) / aM := by
    intro j hjm
    have hjM := Finset.mem_range.1 hjm
    have haj : aM ≤ n * q - j * ν₁ := by
      have : (j : ℝ) ≤ (A.M : ℝ) - 1 := by
        have : (j : ℝ) + 1 ≤ A.M := by exact_mod_cast hjM
        linarith
      nlinarith
    have haj0 : 0 < n * q - j * ν₁ := lt_of_lt_of_le ha haj
    have hT0 : 0 ≤ EK ν K (tauj G A V j) :=
      EK_nonneg hν0 K fun l => cnt_nonneg _ _ (fun _ _ => ind_nonneg _) l
    have h7 := lemma7_stage hν0 hν1 hε q ν₁ H1 H5 V hV K j hjM
    have h1 : EK ν K (tauj G A V j) ≤ 1 / (n * q - j * ν₁) +
        Δ * EK ν K (tauj G A V j) / (n * q - j * ν₁) := by
      rw [← add_div, le_div_iff₀ haj0]; nlinarith
    have h2 : Δ * EK ν K (tauj G A V j) / (n * q - j * ν₁) ≤ Δ * EK ν K (tauj G A V j) / aM :=
      div_le_div_of_nonneg_left (mul_nonneg hΔ hT0) ha haj
    linarith
  have hs := Finset.sum_le_sum hj
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← hsum] at hs
  have : Δ * EK ν K (tau G A V) / aM ≤ K * Δ / aM := by
    apply div_le_div_of_nonneg_right _ ha.le
    nlinarith
  linarith

/-! #### Lemma 8 (bad launches) -/

/-- **Lemma 8.** `E[B_d | V] ≤ γ n q̄ E[τ | V] + K·Z(V)`. -/
theorem lemma8 (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (hc : 0 < A.c) (γ qbar : ℝ)
    (hγ0 : 0 ≤ γ)
    (H2 : ∀ i l, G.π i l ≠ 0 →
      (1 - γ) * (∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0) ≤
        ∑ x, if G.thr + A.c ≤ inner ℝ (A.pt x).1 (G.g l) then ν x else 0)
    (H4 : ∀ i l, G.π i l ≠ 0 →
      (∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0) ≤ qbar)
    (V : ι → Fine) (hV : ∀ i, G.π i (V i) ≠ 0) (K : ℕ) :
    EK ν K (Bd G A V) ≤
      γ * Fintype.card ι * qbar * EK ν K (tau G A V) + K * Zf G A ν V := by
  set r := ∑ x, ν x * ind (Bad G A V x)
  have hr := lemma6_rate hν0 hc γ qbar hγ0 H2 H4 V hV
  have hZ := Zf_nonneg (G := G) (A := A) hν0 V
  have hK : EK ν K (tau G A V) ≤ K :=
    EK_le_const hν0 hν1 K fun l hl => hl ▸ tau_le_length V l
  have hT0 : 0 ≤ EK ν K (tau G A V) := EK_nonneg hν0 K fun l => tau_nonneg V l
  have h1 : EK ν K (Bd G A V) ≤
      EK ν K (cnt (stepA G A V) [] (fun F x => ind (F.length < A.M ∧ Bad G A V x))) :=
    EK_mono hν0 K fun xs => cnt_mono _ _ (fun F x => ind_mono fun h => ⟨h.1, h.2.2⟩) _
  have h2 : EK ν K (cnt (stepA G A V) [] (fun F x => ind (F.length < A.M ∧ Bad G A V x))) =
      r * EK ν K (tau G A V) := by
    rw [EK_cnt hν1]
    unfold tau
    rw [EK_cnt hν1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← EK_mul]
    congr 1; funext l
    simp only [ind_and]
    rw [← Finset.sum_mul, hν1, one_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h2] at h1
  have h3 : r * EK ν K (tau G A V) ≤ (γ * Fintype.card ι * qbar + Zf G A ν V) * EK ν K (tau G A V) :=
    mul_le_mul_of_nonneg_right hr hT0
  nlinarith

/-! #### Assembly -/

/-- Pathwise: `N_ε ≥ M·(1 − τ/K) − B_d` on a run of `K > 0` search rounds. -/
lemma Neps_ge (hdim : Module.finrank ℝ E = A.m + 2)
    (hΦ : ∀ x, Orthonormal ℝ (Fin.cons (A.pt x).1 (A.Φ x) : Fin (A.m + 2) → E))
    (ht0 : 0 < G.thr) (ht1 : G.thr < 1) (hc : 0 < A.c) (hc1 : G.thr + A.c < 1)
    (hεL : 0 < A.εL) (hεLε : A.εL ≤ A.ε) (hεL1 : A.εL < 1) (V : ι → Fine) (K : ℕ) (hK : 0 < K)
    (l : List X) (hl : l.length = K) :
    (A.M : ℝ) * (1 - tau G A V l / K) - Bd G A V l ≤ Neps G A V l := by
  have h4 := lemma4' G A hdim hΦ ht0 ht1 hc hc1 hεL hεLε hεL1 V l
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  have : (A.M : ℝ) * (1 - tau G A V l / K) ≤ (Fof G A V l).length := by
    by_cases hf : (Fof G A V l).length < A.M
    · rw [tau_eq_length V l hf, hl, div_self hKr.ne']; simp
    · have h0 : 0 ≤ tau G A V l / K := div_nonneg (tau_nonneg V l) hKr.le
      have : (A.M : ℝ) ≤ (Fof G A V l).length := by exact_mod_cast not_lt.1 hf
      nlinarith
  linarith


/-! #### Theorem 6.3 (`W = E`, K0, finite support, Markov branch) -/

/-- **Theorem 6.3, Markov branch, at `W = E`** (§9 of
`briefs/attacks/random-search-general-prior.md`). Search points `x ∈ X` (finite) with law `ν`,
launch points `pt x ∈ S`, fixed frames `Φ x`; entries `V ∼ ∏ πᵢ`; K0 oracle; L2 accuracy
`εL ≤ ε`. With `n = |ι|`, `a_j = nq − jν₁`, `a_{M−1} = nq − (M−1)ν₁ > 0`,
`S = Σ_{j<M} 1/a_j`, `D = n(n−1)μ₁q̄/2`, `Z̄ = n(n−1)q̄μ₁(½ + Q_loc)`:
the attack makes at most `K + M·Q_loc` queries on every run, and
`E[N_ε] ≥ M(1 − (S + K D/a_{M−1})/K) − γ n q̄ (S + K D/a_{M−1}) − K Z̄`. -/
theorem thm63_markov (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (hdim : Module.finrank ℝ E = A.m + 2)
    (hΦ : ∀ x, Orthonormal ℝ (Fin.cons (A.pt x).1 (A.Φ x) : Fin (A.m + 2) → E))
    (ht0 : 0 < G.thr) (ht1 : G.thr < 1) (hc : 0 < A.c) (hc1 : G.thr + A.c < 1)
    (hεL : 0 < A.εL) (hεLε : A.εL ≤ A.ε) (hεL1 : A.εL < 1)
    (q γ μ₁ qbar ν₁ : ℝ) (hγ0 : 0 ≤ γ)
    -- (H1) reach rate
    (H1 : ∀ i l, G.π i l ≠ 0 → q ≤ ∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0)
    -- (H2) margin mass
    (H2 : ∀ i l, G.π i l ≠ 0 →
      (1 - γ) * (∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0) ≤
        ∑ x, if G.thr + A.c ≤ inner ℝ (A.pt x).1 (G.g l) then ν x else 0)
    -- (H3) wolf bound at threshold `t`
    (H3 : ∀ i (y : Sph E), (∑ l, if G.thr < inner ℝ y.1 (G.g l) then G.π i l else 0) ≤ μ₁)
    -- (H4) max reach rate
    (H4 : ∀ i l, G.π i l ≠ 0 →
      (∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0) ≤ qbar)
    -- (H5) ν-cap bound at `t − 2ε`
    (H5 : ∀ y : Sph E,
      (∑ x, if G.thr - 2 * A.ε < inner ℝ (A.pt x).1 y.1 then ν x else 0) ≤ ν₁)
    (K : ℕ) (hK : 0 < K)
    (ha : 0 < (Fintype.card ι : ℝ) * q - ((A.M : ℝ) - 1) * ν₁) :
    (∀ (V : ι → Fine) (xs : Fin K → X),
        queries G A V (List.ofFn xs) ≤ K + A.M * qL G A) ∧
    (A.M : ℝ) * (1 - ((∑ j ∈ range A.M, 1 / ((Fintype.card ι : ℝ) * q - j * ν₁)) +
          K * ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * μ₁ * qbar / 2) /
            ((Fintype.card ι : ℝ) * q - ((A.M : ℝ) - 1) * ν₁)) / K)
      - γ * Fintype.card ι * qbar * ((∑ j ∈ range A.M, 1 / ((Fintype.card ι : ℝ) * q - j * ν₁)) +
          K * ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * μ₁ * qbar / 2) /
            ((Fintype.card ι : ℝ) * q - ((A.M : ℝ) - 1) * ν₁))
      - K * ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * qbar * μ₁ * (1 / 2 + qL G A))
      ≤ ∑ V, G.prior V * EK ν K (fun l => (Neps G A V l : ℝ)) := by
  refine ⟨fun V xs => by simpa using queries_le (G := G) (A := A) V (List.ofFn xs), ?_⟩
  set n := (Fintype.card ι : ℝ)
  set aM := n * q - ((A.M : ℝ) - 1) * ν₁
  set S := ∑ j ∈ range A.M, 1 / (n * q - j * ν₁)
  set D := n * (n - 1) * μ₁ * qbar / 2
  set Zb := n * (n - 1) * qbar * μ₁ * (1 / 2 + qL G A)
  have hε : 0 ≤ A.ε := by linarith
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  have hD : ∑ V, G.prior V * Delta G A ν V ≤ D := lemma6_Delta hν0 μ₁ qbar H3 H4
  have hZ : ∑ V, G.prior V * Zf G A ν V ≤ Zb := lemma6_Z hν0 hΦ μ₁ qbar H3 H4
  have hqbar : 0 ≤ qbar := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have := support_mass (G := G) (A := A) (ν := ν) qbar H4 i
    refine le_trans (Finset.sum_nonneg fun l _ => mul_nonneg (G.hπ0 i l)
      (Finset.sum_nonneg fun x _ => mul_nonneg (hν0 x) (ind_nonneg _))) this
  set cc := (A.M : ℝ) / K + γ * n * qbar
  have hcc : 0 ≤ cc := add_nonneg (div_nonneg (Nat.cast_nonneg _) hKr.le)
    (mul_nonneg (mul_nonneg hγ0 (Nat.cast_nonneg _)) hqbar)
  have hper : ∀ V, G.prior V * (A.M - cc * (S + K * Delta G A ν V / aM) - K * Zf G A ν V) ≤
      G.prior V * EK ν K (fun l => (Neps G A V l : ℝ)) := by
    intro V
    by_cases hp : G.prior V = 0
    · rw [hp, zero_mul, zero_mul]
    have hV : ∀ i, G.π i (V i) ≠ 0 := fun i =>
      Finset.prod_ne_zero_iff.1 hp i (Finset.mem_univ i)
    refine mul_le_mul_of_nonneg_left ?_ (G.prior_nonneg V)
    have h1 : EK ν K (fun l => (A.M : ℝ) + (-((A.M : ℝ) / K)) * tau G A V l + (-1) * Bd G A V l)
        ≤ EK ν K (fun l => (Neps G A V l : ℝ)) := by
      refine EK_mono hν0 K fun xs => ?_
      have := Neps_ge hdim hΦ ht0 ht1 hc hc1 hεL hεLε hεL1 V K hK (List.ofFn xs)
        (List.length_ofFn)
      have e : (A.M : ℝ) * (1 - tau G A V (List.ofFn xs) / K) - Bd G A V (List.ofFn xs) =
          (A.M : ℝ) + (-((A.M : ℝ) / K)) * tau G A V (List.ofFn xs) +
            (-1) * Bd G A V (List.ofFn xs) := by ring
      linarith
    rw [EK_affine hν1] at h1
    have h7 := lemma7 hν0 hν1 hε q ν₁ H1 H5 ha V hV K
    have h8 := lemma8 hν0 hν1 hc γ qbar hγ0 H2 H4 V hV K
    have hT0 : 0 ≤ EK ν K (tau G A V) := EK_nonneg hν0 K fun l => tau_nonneg V l
    have : cc * EK ν K (tau G A V) ≤ cc * (S + K * Delta G A ν V / aM) :=
      mul_le_mul_of_nonneg_left h7 hcc
    have e2 : cc * EK ν K (tau G A V) = (A.M : ℝ) / K * EK ν K (tau G A V) +
        γ * n * qbar * EK ν K (tau G A V) := by ring
    linarith
  have hsum := Finset.sum_le_sum fun V (_ : V ∈ univ) => hper V
  clear_value S
  have e3 : ∑ V, G.prior V * (A.M - cc * (S + K * Delta G A ν V / aM) - K * Zf G A ν V) =
      (A.M - cc * S) * ∑ V, G.prior V - (cc * K / aM) * ∑ V, G.prior V * Delta G A ν V -
        K * ∑ V, G.prior V * Zf G A ν V := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun V _ => by ring
  rw [e3, G.prior_sum, mul_one] at hsum
  have hcK : 0 ≤ cc * K / aM := div_nonneg (mul_nonneg hcc hKr.le) ha.le
  have := mul_le_mul_of_nonneg_left hD hcK
  have := mul_le_mul_of_nonneg_left hZ hKr.le
  have e4 : (A.M : ℝ) * (1 - (S + K * D / aM) / K) - γ * n * qbar * (S + K * D / aM) - K * Zb =
      A.M - cc * S - (cc * K / aM) * D - K * Zb := by
    simp only [cc]; field_simp; ring
  rw [e4]
  linarith

end Attack

end OracleBounds.Attacks.RandomSearch

#print axioms OracleBounds.Attacks.RandomSearch.resp_eq_one_of_reach
#print axioms OracleBounds.Attacks.RandomSearch.resp_eq_zero_of_noReach
#print axioms OracleBounds.Attacks.RandomSearch.resp_eq_oneFace
#print axioms OracleBounds.Attacks.RandomSearch.pathProb_eq_oneFace
#print axioms OracleBounds.Attacks.RandomSearch.val_clean_eq_oneFace
#print axioms OracleBounds.Attacks.RandomSearch.attribution
#print axioms OracleBounds.Attacks.RandomSearch.bisect_eq_bstate
#print axioms OracleBounds.Attacks.RandomSearch.runP_block
#print axioms OracleBounds.Attacks.RandomSearch.runP_succ_cons
#print axioms OracleBounds.Attacks.RandomSearch.bisectAns_eq_runP
#print axioms OracleBounds.Attacks.RandomSearch.bisect_eq_runP
#print axioms OracleBounds.Attacks.RandomSearch.L2probe_A0
#print axioms OracleBounds.Attacks.RandomSearch.L2probe_A1
#print axioms OracleBounds.Attacks.RandomSearch.L2probe_B
#print axioms OracleBounds.Attacks.RandomSearch.runP_take_drop
#print axioms OracleBounds.Attacks.RandomSearch.L2fromAns_L2run
#print axioms OracleBounds.Attacks.RandomSearch.norm_circ
#print axioms OracleBounds.Attacks.RandomSearch.norm_L2probe
#print axioms OracleBounds.Attacks.RandomSearch.toSph_L2probe
#print axioms OracleBounds.Attacks.RandomSearch.norm_L2fromAns
#print axioms OracleBounds.Attacks.RandomSearch.toSph_L2fromAns
#print axioms OracleBounds.Attacks.RandomSearch.inner_x0_L2raw
#print axioms OracleBounds.Attacks.RandomSearch.L2raw_ne_zero
#print axioms OracleBounds.Attacks.RandomSearch.norm_L2fromAns_of_aHat
#print axioms OracleBounds.Attacks.RandomSearch.norm_L2
#print axioms OracleBounds.Attacks.RandomSearch.EK_succ
#print axioms OracleBounds.Attacks.RandomSearch.EK_cnt
#print axioms OracleBounds.Attacks.RandomSearch.cnt_snoc
#print axioms OracleBounds.Attacks.RandomSearch.resp_eq_orcK0
#print axioms OracleBounds.Attacks.RandomSearch.runP_congr
#print axioms OracleBounds.Attacks.RandomSearch.L2_norm_or
#print axioms OracleBounds.Attacks.RandomSearch.good_launch
#print axioms OracleBounds.Attacks.RandomSearch.lemma4'
#print axioms OracleBounds.Attacks.RandomSearch.bonferroni
#print axioms OracleBounds.Attacks.RandomSearch.lemma5
#print axioms OracleBounds.Attacks.RandomSearch.lemma6_rate
#print axioms OracleBounds.Attacks.RandomSearch.prior_two
#print axioms OracleBounds.Attacks.RandomSearch.prior_two'
#print axioms OracleBounds.Attacks.RandomSearch.lemma6_Delta
#print axioms OracleBounds.Attacks.RandomSearch.lemma6_Z
#print axioms OracleBounds.Attacks.RandomSearch.queries_eq
#print axioms OracleBounds.Attacks.RandomSearch.queries_le
#print axioms OracleBounds.Attacks.RandomSearch.stage_launch_le
#print axioms OracleBounds.Attacks.RandomSearch.lemma7_stage
#print axioms OracleBounds.Attacks.RandomSearch.tau_eq_sum
#print axioms OracleBounds.Attacks.RandomSearch.lemma7
#print axioms OracleBounds.Attacks.RandomSearch.lemma8
#print axioms OracleBounds.Attacks.RandomSearch.Neps_ge
#print axioms OracleBounds.Attacks.RandomSearch.thm63_markov
