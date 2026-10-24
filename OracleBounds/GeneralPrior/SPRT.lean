import OracleBounds.GeneralPrior.Membership

/-!
# The sequential membership test (upper-bounds note, Theorem 2.3)

Wald's SPRT at the candidate `c`, in the fixed-budget process model: while the log-likelihood
ratio `Λ` is inside `(−A, A)` the attacker probes `c` and updates `Λ` by `±ℓ`
(`ℓ = log((1−ρ)/ρ)`); once it leaves, the remaining queries go to a far point `x_f` that does not
reach `c` (so they do not count in `S_c` and carry no information about membership). Decision:
"member" iff `Λ ≥ A`.

Against the symmetric-flip kernel (`κ = ρ` at or below `thr`, `1−ρ` above), for every fixed rest of
the list `V`:

* `E₀[S_c] ≤ (A + ℓ)/KL_ρ` and `E₁[S_c] ≤ (A + ℓ)/KL_ρ` (Wald's identity + overshoot `≤ ℓ`);
* `δI ≤ e^{−A}` when no other face collides with `c` (change of measure);
* `δII ≤ e^{−A} + (A + ℓ)/(KL_ρ·Q)` (the second term is the truncation at budget `Q`; it vanishes
  as `Q → ∞`, recovering the note's untruncated statement).

With `A = log(2/δ)`: `E₀[S_c] ≤ (log(2/δ) + ℓ)/KL_ρ`, against the lower bound
`(log(1/(2δ)))/KL_ρ` of `Gallery.membership_reach_needed` — tight including the constant.

**Definitions and the statement of `sprt_membership` are locked by the administrator.**
-/

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

/-- One SPRT step on the state `(Λ, S)`: update only while `|Λ| < A`. -/
noncomputable def sprtStep (ℓ A : ℝ) (st : ℝ × ℕ) (b : Bool) : ℝ × ℕ :=
  if |st.1| < A then (st.1 + (if b then ℓ else -ℓ), st.2 + 1) else st

/-- SPRT state after history `h`. -/
noncomputable def sprtState (ℓ A : ℝ) (h : List Bool) : ℝ × ℕ :=
  h.foldl (sprtStep ℓ A) (0, 0)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- SPRT probe rule: `c` while undecided, then the far point `x_f`. -/
noncomputable def sprtProbe (ℓ A : ℝ) (c xf : Sph E) (h : List Bool) : Sph E :=
  if |(sprtState ℓ A h).1| < A then c else xf

/-- SPRT decision: "member" iff `Λ ≥ A`. -/
noncomputable def sprtDecide (ℓ A : ℝ) (h : List Bool) : ℝ :=
  if A ≤ (sprtState ℓ A h).1 then 1 else 0

/-! ### Helper lemmas for the SPRT -/

lemma sprtState_nil (ℓ A : ℝ) : sprtState ℓ A [] = (0, 0) := rfl

lemma sprtState_append (ℓ A : ℝ) (h : List Bool) (b : Bool) :
    sprtState ℓ A (h ++ [b]) = sprtStep ℓ A (sprtState ℓ A h) b := by
  simp [sprtState, List.foldl_append]

/-- Once `|Λ| ≥ A` the state is frozen. -/
lemma sprt_foldl_frozen (ℓ A : ℝ) (l : List Bool) (st : ℝ × ℕ) (hst : ¬ |st.1| < A) :
    l.foldl (sprtStep ℓ A) st = st := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    rw [List.foldl_cons, show sprtStep ℓ A st b = st from if_neg hst]; exact ih

/-- If the final `|Λ| < A`, every step updated, so the count grew by the length. -/
lemma sprt_foldl_count (ℓ A : ℝ) (l : List Bool) : ∀ st : ℝ × ℕ,
    |(l.foldl (sprtStep ℓ A) st).1| < A → (l.foldl (sprtStep ℓ A) st).2 = st.2 + l.length := by
  induction l with
  | nil => intro st _; simp
  | cons b t ih =>
    intro st hlt
    rw [List.foldl_cons] at hlt ⊢
    by_cases hst : |st.1| < A
    · rw [ih _ hlt]; simp [sprtStep, hst]; omega
    · exfalso
      rw [show sprtStep ℓ A st b = st from if_neg hst, sprt_foldl_frozen ℓ A t st hst] at hlt
      exact hst hlt

/-- Overshoot: `|Λ| < A + ℓ` is invariant. -/
lemma sprt_foldl_bound (ℓ A : ℝ) (hℓ : 0 ≤ ℓ) (l : List Bool) : ∀ st : ℝ × ℕ,
    |st.1| < A + ℓ → |(l.foldl (sprtStep ℓ A) st).1| < A + ℓ := by
  induction l with
  | nil => intro st h; simpa using h
  | cons b t ih =>
    intro st hst
    rw [List.foldl_cons]
    apply ih
    by_cases h1 : |st.1| < A
    · rw [sprtStep, if_pos h1]
      have : |(if b then ℓ else -ℓ)| = ℓ := by cases b <;> simp [abs_of_nonneg hℓ]
      calc |st.1 + (if b then ℓ else -ℓ)| ≤ |st.1| + |(if b then ℓ else -ℓ)| := abs_add_le _ _
        _ < A + ℓ := by rw [this]; linarith
    · rw [sprtStep, if_neg h1]; exact hst

lemma sprtState_bound (ℓ A : ℝ) (hℓ : 0 ≤ ℓ) (hA : 0 < A) (h : List Bool) :
    |(sprtState ℓ A h).1| < A + ℓ :=
  sprt_foldl_bound ℓ A hℓ h (0, 0) (by simp; linarith)

lemma sprtState_count (ℓ A : ℝ) (h : List Bool) (hlt : |(sprtState ℓ A h).1| < A) :
    (sprtState ℓ A h).2 = h.length := by
  exact (sprt_foldl_count ℓ A h (0, 0) hlt).trans (by simp)

omit [InnerProductSpace ℝ E] in
/-- Wald's identity (finite horizon): `Λ − d·S` is a martingale when the kernel at `c` is fixed. -/
lemma sprt_wald (ℓ A : ℝ) (c xf : Sph E) (p : Sph E → ℝ) (d : ℝ)
    (hd : d = p c * ℓ - (1 - p c) * ℓ) :
    ∀ r h, val p (sprtProbe ℓ A c xf)
      (fun h' => (sprtState ℓ A h').1 - d * (sprtState ℓ A h').2) r h
      = (sprtState ℓ A h).1 - d * (sprtState ℓ A h).2 := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    rw [val_succ, ih, ih, sprtState_append, sprtState_append]
    unfold sprtProbe sprtStep
    by_cases hA : |(sprtState ℓ A h).1| < A
    · simp only [if_pos hA, if_true, Bool.false_eq_true, if_false, Nat.cast_add, Nat.cast_one]
      rw [hd]; ring
    · simp only [if_neg hA]; ring

omit [InnerProductSpace ℝ E] in
/-- `accCount` of the reaching probes is the expected increment of `S`. -/
lemma sprt_accCount (ℓ A : ℝ) (c xf : Sph E) (p : Sph E → ℝ) (act : Sph E → Prop)
    [DecidablePred act] (hc : act c) (hxf : ¬ act xf) :
    ∀ r h, accCount p (sprtProbe ℓ A c xf) act r h + ((sprtState ℓ A h).2 : ℝ) =
      val p (sprtProbe ℓ A c xf) (fun h' => ((sprtState ℓ A h').2 : ℝ)) r h := by
  intro r
  induction r with
  | zero => intro h; simp [accCount]
  | succ r ih =>
    intro h
    simp only [accCount]
    rw [val_succ, ← ih, ← ih, sprtState_append, sprtState_append]
    unfold sprtProbe sprtStep
    by_cases hA : |(sprtState ℓ A h).1| < A
    · simp only [if_pos hA, if_pos hc]; push_cast; ring
    · simp only [if_neg hA, if_neg hxf]; ring

omit [InnerProductSpace ℝ E] in
/-- Change of measure along the SPRT: the likelihood ratio is `exp(θ·(Λ' − Λ))`. -/
lemma sprt_change (ℓ A θ a0 a1 : ℝ) (c xf : Sph E) (p0 p1 : Sph E → ℝ)
    (h0 : p0 c = a0) (h1 : p1 c = a1) (hxf : p0 xf = p1 xf)
    (ht : a1 * Real.exp (θ * ℓ) = a0) (hf : (1 - a1) * Real.exp (-(θ * ℓ)) = 1 - a0)
    (F : List Bool → ℝ) :
    ∀ r h, val p0 (sprtProbe ℓ A c xf) F r h = val p1 (sprtProbe ℓ A c xf)
      (fun h' => F h' * Real.exp (θ * ((sprtState ℓ A h').1 - (sprtState ℓ A h).1))) r h := by
  intro r
  induction r with
  | zero => intro h; simp
  | succ r ih =>
    intro h
    have key : ∀ (k : ℝ) (h₀ : List Bool),
        val p1 (sprtProbe ℓ A c xf)
          (fun h' => F h' * Real.exp (θ * ((sprtState ℓ A h').1 - k))) r h₀ =
        Real.exp (θ * ((sprtState ℓ A h₀).1 - k)) * val p1 (sprtProbe ℓ A c xf)
          (fun h' => F h' * Real.exp (θ * ((sprtState ℓ A h').1 - (sprtState ℓ A h₀).1))) r h₀ := by
      intro k h₀
      rw [← zero_add (Real.exp _ * _), ← val_affine]
      congr 1
      funext h'
      rw [show θ * ((sprtState ℓ A h').1 - k) = θ * ((sprtState ℓ A h₀).1 - k) +
        θ * ((sprtState ℓ A h').1 - (sprtState ℓ A h₀).1) by ring, Real.exp_add]
      ring
    rw [val_succ, val_succ, ih, ih, key (sprtState ℓ A h).1 (h ++ [true]),
      key (sprtState ℓ A h).1 (h ++ [false])]
    set Vt := val p1 (sprtProbe ℓ A c xf) (fun h' => F h' *
      Real.exp (θ * ((sprtState ℓ A h').1 - (sprtState ℓ A (h ++ [true])).1))) r (h ++ [true])
    set Vf := val p1 (sprtProbe ℓ A c xf) (fun h' => F h' *
      Real.exp (θ * ((sprtState ℓ A h').1 - (sprtState ℓ A (h ++ [false])).1))) r (h ++ [false])
    rw [sprtState_append, sprtState_append]
    unfold sprtProbe sprtStep
    by_cases hA : |(sprtState ℓ A h).1| < A
    · simp only [if_pos hA, if_true, Bool.false_eq_true, if_false]
      rw [show θ * ((sprtState ℓ A h).1 + ℓ - (sprtState ℓ A h).1) = θ * ℓ by ring,
        show θ * ((sprtState ℓ A h).1 + -ℓ - (sprtState ℓ A h).1) = -(θ * ℓ) by ring, h0, h1,
        ← hf, ← ht]
      ring
    · simp only [if_neg hA, sub_self, mul_zero, Real.exp_zero, one_mul, hxf]

variable {ι Fine : Type*} [Fintype ι] [Fintype Fine]

namespace Gallery

open Classical in
/-- **Theorem 2.3 (SPRT), fixed-budget form.** -/
theorem sprt_membership (G : Gallery E ι Fine) [Nonempty ι] (V : ι → Fine) (c : Sph E)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hthr1 : G.thr < 1)
    (hκq : ∀ s ≤ G.thr, G.κ s = ρ) (hκl : ∀ s, G.thr < s → G.κ s = 1 - ρ)
    (xf : Sph E) (hxf : inner ℝ xf.1 c.1 ≤ G.thr) (A : ℝ) (hA : 0 < A) (Q : ℕ) (hQ : 1 ≤ Q) :
    accCount (G.resp V) (sprtProbe (Real.log ((1 - ρ) / ρ)) A c xf) (G.reachC c.1) Q [] ≤
        (A + Real.log ((1 - ρ) / ρ)) / ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ)) ∧
    accCount (G.respWith V c.1) (sprtProbe (Real.log ((1 - ρ) / ρ)) A c xf) (G.reachC c.1) Q [] ≤
        (A + Real.log ((1 - ρ) / ρ)) / ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ)) ∧
    (G.score V c ≤ G.thr →
      val (G.resp V) (sprtProbe (Real.log ((1 - ρ) / ρ)) A c xf)
        (sprtDecide (Real.log ((1 - ρ) / ρ)) A) Q [] ≤ Real.exp (-A)) ∧
    val (G.respWith V c.1) (sprtProbe (Real.log ((1 - ρ) / ρ)) A c xf)
        (fun h => 1 - sprtDecide (Real.log ((1 - ρ) / ρ)) A h) Q [] ≤
      Real.exp (-A) + (A + Real.log ((1 - ρ) / ρ)) /
        ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * Q) := by
  set ℓ := Real.log ((1 - ρ) / ρ) with hℓdef
  have hρ1' : 0 < 1 - ρ := by linarith
  have hratio : 1 < (1 - ρ) / ρ := by rw [lt_div_iff₀ hρ0]; linarith
  have hℓ : 0 < ℓ := Real.log_pos hratio
  have hexp : Real.exp ℓ = (1 - ρ) / ρ := Real.exp_log (by positivity)
  have hexpn : Real.exp (-ℓ) = ρ / (1 - ρ) := by rw [Real.exp_neg, hexp, inv_div]
  have hKL : 0 < (1 - 2 * ρ) * ℓ := mul_pos (by linarith) hℓ
  set probe := sprtProbe ℓ A c xf with hprobe
  have hp0 : ∀ x, 0 ≤ G.resp V x ∧ G.resp V x ≤ 1 := fun x => G.hκ _
  have hp1 : ∀ x, 0 ≤ G.respWith V c.1 x ∧ G.respWith V c.1 x ≤ 1 := fun x => G.hκ _
  have hcc : inner ℝ c.1 c.1 = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, c.2]; norm_num
  have h1c : G.respWith V c.1 c = 1 - ρ := by
    unfold respWith; rw [hcc, max_eq_right (G.score_mem V c).2]; exact hκl 1 hthr1
  have hxfeq : G.resp V xf = G.respWith V c.1 xf := by
    unfold resp respWith
    by_cases hs : G.score V xf ≤ G.thr
    · rw [hκq _ hs, hκq _ (max_le hs hxf)]
    · push Not at hs
      rw [hκl _ hs, hκl _ (lt_of_lt_of_le hs (le_max_left _ _))]
  have hreach_c : G.reachC c.1 c := by unfold reachC; rw [hcc]; exact hthr1
  have hreach_xf : ¬ G.reachC c.1 xf := by unfold reachC; push Not; exact hxf
  -- Wald + overshoot: expected number of `c`-probes
  have hES : ∀ p : Sph E → ℝ, (∀ x, 0 ≤ p x ∧ p x ≤ 1) → (p c = ρ ∨ p c = 1 - ρ) →
      val p probe (fun h => ((sprtState ℓ A h).2 : ℝ)) Q [] ≤
        (A + ℓ) / ((1 - 2 * ρ) * ℓ) := by
    intro p hp hpc
    set d := p c * ℓ - (1 - p c) * ℓ with hd
    have hw := sprt_wald ℓ A c xf p d hd Q []
    rw [sprtState_nil] at hw
    have e := val_add p probe (fun h => (sprtState ℓ A h).1)
      (fun h => 0 + (-d) * ((sprtState ℓ A h).2 : ℝ)) Q []
    rw [val_affine] at e
    have e' : val p probe (fun h => (sprtState ℓ A h).1 - d * ((sprtState ℓ A h).2 : ℝ)) Q [] =
        val p probe (fun h => (sprtState ℓ A h).1 + (0 + (-d) * ((sprtState ℓ A h).2 : ℝ))) Q [] := by
      congr 1; funext h; ring
    rw [e', e] at hw
    have hlo : -(A + ℓ) ≤ val p probe (fun h => (sprtState ℓ A h).1) Q [] := by
      have := val_mono probe hp (F := fun _ => -(A + ℓ)) (G := fun h => (sprtState ℓ A h).1) Q []
        (fun h' _ => (abs_lt.1 (sprtState_bound ℓ A hℓ.le hA h')).1.le)
      rwa [val_const] at this
    have hhi : val p probe (fun h => (sprtState ℓ A h).1) Q [] ≤ A + ℓ := by
      have := val_mono probe hp (G := fun _ => (A + ℓ)) (F := fun h => (sprtState ℓ A h).1) Q []
        (fun h' _ => (abs_lt.1 (sprtState_bound ℓ A hℓ.le hA h')).2.le)
      rwa [val_const] at this
    rw [le_div_iff₀ hKL]
    simp only [Nat.cast_zero, mul_zero, sub_zero] at hw
    rcases hpc with h | h
    · rw [h] at hd; rw [hd] at hw; linarith
    · rw [h] at hd; rw [hd] at hw; linarith
  have hacc : ∀ p : Sph E → ℝ, accCount p probe (G.reachC c.1) Q [] =
      val p probe (fun h => ((sprtState ℓ A h).2 : ℝ)) Q [] := by
    intro p
    have := sprt_accCount ℓ A c xf p (G.reachC c.1) hreach_c hreach_xf Q []
    rw [sprtState_nil] at this
    simpa using this
  have h0cases : G.resp V c = ρ ∨ G.resp V c = 1 - ρ := by
    unfold resp
    by_cases hs : G.score V c ≤ G.thr
    · exact Or.inl (hκq _ hs)
    · push Not at hs; exact Or.inr (hκl _ hs)
  have hES1 := hES _ hp1 (Or.inr h1c)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hacc]; exact hES _ hp0 h0cases
  · rw [hacc]; exact hES1
  · -- type I error by change of measure
    intro hsc
    have h0c : G.resp V c = ρ := hκq _ hsc
    have hcm := sprt_change ℓ A (-1) ρ (1 - ρ) c xf (G.resp V) (G.respWith V c.1) h0c h1c hxfeq
      (by rw [show -1 * ℓ = -ℓ by ring, hexpn]; field_simp)
      (by rw [show -(-1 * ℓ) = ℓ by ring, hexp]; field_simp; ring)
      (sprtDecide ℓ A) Q []
    rw [hcm]
    have := val_mono probe hp1 (G := fun _ => Real.exp (-A))
      (F := fun h' => sprtDecide ℓ A h' *
        Real.exp (-1 * ((sprtState ℓ A h').1 - (sprtState ℓ A []).1))) Q []
      (fun h' _ => by
        rw [sprtState_nil]
        unfold sprtDecide
        split_ifs with hge
        · rw [one_mul]; apply Real.exp_le_exp.2; simp; linarith
        · rw [zero_mul]; exact (Real.exp_pos _).le)
    rwa [val_const] at this
  · -- type II error: `Λ ≤ −A` (change of measure) or truncation (`S = Q`)
    have hne : xf ≠ c := by
      intro h; rw [h, hcc] at hxf; linarith
    set pref : Sph E → ℝ := fun x => if x = c then ρ else G.respWith V c.1 x with hpref
    have hpref01 : ∀ x, 0 ≤ pref x ∧ pref x ≤ 1 := by
      intro x; simp only [hpref]; split_ifs
      · exact ⟨hρ0.le, by linarith⟩
      · exact hp1 x
    have hcm := sprt_change ℓ A 1 (1 - ρ) ρ c xf (G.respWith V c.1) pref h1c
      (by simp [hpref]) (by simp [hpref, hne])
      (by rw [one_mul, hexp]; field_simp)
      (by rw [one_mul, hexpn]; field_simp; ring)
      (fun h => if (sprtState ℓ A h).1 ≤ -A then 1 else 0) Q []
    have hL : val (G.respWith V c.1) probe
        (fun h => if (sprtState ℓ A h).1 ≤ -A then 1 else 0) Q [] ≤ Real.exp (-A) := by
      rw [hcm]
      have := val_mono probe hpref01 (G := fun _ => Real.exp (-A))
        (F := fun h' => (if (sprtState ℓ A h').1 ≤ -A then (1 : ℝ) else 0) *
          Real.exp (1 * ((sprtState ℓ A h').1 - (sprtState ℓ A []).1))) Q []
        (fun h' _ => by
          rw [sprtState_nil]
          split_ifs with hge
          · rw [one_mul]; apply Real.exp_le_exp.2; simp; linarith
          · rw [zero_mul]; exact (Real.exp_pos _).le)
      rwa [val_const] at this
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
    calc val (G.respWith V c.1) probe (fun h => 1 - sprtDecide ℓ A h) Q []
        ≤ val (G.respWith V c.1) probe (fun h => (if (sprtState ℓ A h).1 ≤ -A then 1 else 0) +
            (0 + (1 / (Q : ℝ)) * ((sprtState ℓ A h).2 : ℝ))) Q [] := by
          apply val_mono probe hp1
          intro h' hl
          simp only [List.length_nil, zero_add] at hl
          have hS0 : (0 : ℝ) ≤ (1 / (Q : ℝ)) * ((sprtState ℓ A h').2 : ℝ) := by positivity
          unfold sprtDecide
          by_cases hge : A ≤ (sprtState ℓ A h').1
          · rw [if_pos hge]
            split_ifs <;> linarith
          · rw [if_neg hge]
            by_cases hle : (sprtState ℓ A h').1 ≤ -A
            · rw [if_pos hle]; linarith
            · rw [if_neg hle]
              push Not at hge hle
              have habs : |(sprtState ℓ A h').1| < A := abs_lt.2 ⟨hle, hge⟩
              rw [sprtState_count ℓ A h' habs, hl]
              field_simp; linarith
      _ = val (G.respWith V c.1) probe (fun h => if (sprtState ℓ A h).1 ≤ -A then 1 else 0) Q [] +
            (0 + (1 / (Q : ℝ)) *
              val (G.respWith V c.1) probe (fun h => ((sprtState ℓ A h).2 : ℝ)) Q []) := by
          rw [val_add, val_affine]
      _ ≤ Real.exp (-A) + (0 + (1 / (Q : ℝ)) * ((A + ℓ) / ((1 - 2 * ρ) * ℓ))) := by
          gcongr
      _ = Real.exp (-A) + (A + ℓ) / ((1 - 2 * ρ) * ℓ * Q) := by
          rw [zero_add, one_div_mul_eq_div, div_div]

end Gallery

end OracleBounds.GeneralPrior
