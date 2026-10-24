import OracleBounds.Attacks.PassiveUpper

/-!
# The passive venue on the real gallery process (airlock draft v11.1, Corollary 4.2.5)

**Statements signed off by the administrator, 23 Sep 2026** (proof by subagent). This closes the
faithfulness gap of `PassiveUpper.lean`: the arrival law is derived from the gallery oracle and a
product prior, not posited. Recorded limitations: counts are truncated at the budget `Q` (so
`δ_II` carries `+(A+ℓ)/(KL_ρ·μ·Q)`, the note's form being the `Q → ∞` limit), the population is
finite, and the venue's rule is the fixed SPRT. ERRATUM it establishes: the note's `H₀` arrival
count needs the factor `1/(1−2γ)` (`passive_venue_arrivals_H0`); the note's form is exact under
`H₁` and at `γ = 0` only.

`OracleBounds.Attacks.PassiveUpper` proves Corollary 4.2.5 inside the abstract arrival model
`pval`, in which "each arrival reaches `c` with probability `μ`, independently of the past" is
*built into the definition*. This file closes that gap: it starts from
`OracleBounds.GeneralPrior.Gallery`'s oracle (`Gallery.resp` / `Gallery.respWith`) and
`OracleBounds.V6.val`'s transcript process, draws the arrival sequence i.i.d. from a population
law on a finite arrival alphabet, and *derives* the `pval` law.

The chain is

  `∑_{w : Fin Q → Pop} (∏_k α (w k)) · val (oracle) (passive probe from w) (F ∘ observations)`
      `= vval α arr (oracle) …`            (`iid_bridge`: i.i.d. arrivals, transcript-independent)
      `= qval mf mc pc pf …`               (`vval_eq_qval`: the gallery oracle at the flip kernel)
      `= pval (fun _ ↦ μ) (fun _ ↦ p) …`   (`qval_eq_pval`: collisions do not move the bit law)

and then `PassiveUpper.passive_sprt`'s Wald identities apply verbatim.

`qval` is `pval` refined by a per-arrival *collision flag* (`Obs' = Option (Bool × Bool)`), which
is what Corollary 4.2.5's type-I analysis needs and `pval` cannot express: under `H₀` a reaching
arrival answers `Bern(ρ)` only if it does **not** also reach a face of `G₀`.

## Results

* `iid_bridge` — the product prior `∏ₖ α (w k)` on arrival tuples `w : Fin Q → Pop`, pushed
  through `V6.val`, is the one-arrival-at-a-time law `vval`. This is the independence step.
* `vval_eq_qval`, `qval_eq_pval`, `venue_flag_law`, `venue_plain_law` — the oracle steps.
* `venue_reaching_iid` — off the collision event, the venue's record is i.i.d. `Bern(ρ)` under
  `H₀` and i.i.d. `Bern(1−ρ)` under `H₁`, at reach rate `μ_pop`, both *derived*.
* `qval_coll_wald` (`μ·E[NC] = mc·E[S]`), `qval_drift_wald`, `qval_coupling` — Wald for the
  colliding arrivals, and the coupling of the note's proof.
* `passive_venue_gallery` — Corollary 4.2.5: `E¹[#arrivals] ≤ (A+ℓ)/(KL_ρ·μ)`,
  `δ_I ≤ δ/2 + γ(A+ℓ)/KL_ρ`, `δ_II ≤ δ/2 + (A+ℓ)/(KL_ρ·μ·Q)`.
* `passive_venue_arrivals_H0` — the same arrival bound under `H₀`, where collisions cost a factor
  `1/(1−2γ)`.

## What is assumed, and what is derived

**Derived** (not hypotheses): that the arrivals are i.i.d. and independent of the transcript
(it is the product prior, plus the fact that `Gallery.passiveProbe` reads only `h.length`); that
the arrival tuples carry a probability distribution (first conjunct of `passive_venue_gallery`);
that a reaching arrival answers `Bern(1−ρ)` under `H₁` and `Bern(ρ)` under `H₀` off the collision
event, and `Bern(1−ρ)` on it (from `Gallery.resp`/`Gallery.respWith` and `hκq`/`hκl`); that the
collision events are independent of the answers.

**Assumed**, as explicit hypotheses:

1. The arrival alphabet `Pop` is a finite inhabited type with population law `α ≥ 0`, `∑ α = 1`.
   Everything is finite, so no measurability hypothesis is needed anywhere.
2. The oracle is the symmetric-flip kernel: `hκq : κ = ρ` at or below `thr`, `hκl : κ = 1 − ρ`
   above, with `0 < ρ < 1/2`.
3. The enrolled gallery `V = G₀` is **fixed**: every statement is conditional on `G₀`, as
   `GeneralPrior.Gallery.membership_tv` and the note's §4.2 are.
4. `μ` and `γ` are *defined* by the two mass hypotheses `hmc`, `hmf`; together they force
   `∑_{reaching} α = μ` and make `γ` the conditional probability of a collision given a reach.
   `0 < μ` is assumed (some arrivals reach `c`).
5. The venue's test is the fixed rule `venueDecide`: Wald's SPRT run on `venueObs`, the sequence
   of (reach indicator, answer) pairs. This is a modelling choice, not a hidden assumption — the
   observation map uses nothing the venue cannot see, in particular not the collision flag.

## Residual gaps

* `N` is the *truncated* arrival count: the run has a budget of `Q` arrivals, so the bounds are
  on `E[N ∧ Q]`, uniformly in `Q`. The note's untruncated `E[N]` needs monotone convergence —
  not formalised (inherited from `PassiveUpper`, caveat 3).
* For the same reason `δ_II` carries the truncation term `(A+ℓ)/(KL_ρ·μ·Q)`; the note states
  `δ_II ≤ δ/2`, which is the `Q → ∞` limit.
* The note's `E[#arrivals] ≤ (A+ℓ)/(KL_ρ·μ_pop)` is asserted under `H₀` ("the target never
  visits"). `passive_venue_arrivals_H0` shows the correct `H₀` constant is
  `(A+ℓ)/(KL_ρ·μ(1−2γ))`; the note's form is exact under `H₁`, and under `H₀` only at `γ = 0`.
* Randomised venues (a mixture over coins) and a Borel population law are not covered; `Pop` is
  finite. The lower-bound side (`GeneralPrior.Gallery.passive_population`) takes an arbitrary
  finite coin space `U`, of which `Fin Q → Pop` is an instance.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.Attacks

open Finset OracleBounds.V6 OracleBounds.GeneralPrior

/-! ## 1. Shifting the history of a `val` process -/

section Shift

variable {X : Type*}

/-- Running `val` from the history `h₀ ++ h` is the same as running it from `h` with the probe
rule and the leaf function pre-composed with `h₀ ++ ·`. -/
lemma val_shift (p : X → ℝ) (probe : List Bool → X) (F : List Bool → ℝ) (h₀ : List Bool) :
    ∀ (r : ℕ) (h : List Bool), val p probe F r (h₀ ++ h) =
      val p (fun h' => probe (h₀ ++ h')) (fun h' => F (h₀ ++ h')) r h := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    rw [val_succ, val_succ, List.append_assoc, List.append_assoc, ih, ih]

end Shift

/-! ## 2. The venue's law: i.i.d. arrivals from a finite population -/

section Venue

variable {X Pop : Type*} [Fintype Pop]

/-- The venue's one-round law, written as a process on histories of *(arrival, bit)* pairs: the
arrival is drawn from the population law `α`, and the oracle answers `true` with probability
`p (arr a)`. This is the law that `iid_bridge` *derives* from the gallery process. -/
noncomputable def vval (α : Pop → ℝ) (arr : Pop → X) (p : X → ℝ)
    (F : List (Pop × Bool) → ℝ) : ℕ → List (Pop × Bool) → ℝ
  | 0, h => F h
  | r + 1, h => ∑ a, α a * (p (arr a) * vval α arr p F r (h ++ [(a, true)]) +
      (1 - p (arr a)) * vval α arr p F r (h ++ [(a, false)]))

lemma vval_succ (α : Pop → ℝ) (arr : Pop → X) (p : X → ℝ) (F : List (Pop × Bool) → ℝ)
    (r : ℕ) (h : List (Pop × Bool)) :
    vval α arr p F (r + 1) h = ∑ a, α a * (p (arr a) * vval α arr p F r (h ++ [(a, true)]) +
      (1 - p (arr a)) * vval α arr p F r (h ++ [(a, false)])) := rfl

lemma vval_shift (α : Pop → ℝ) (arr : Pop → X) (p : X → ℝ) (F : List (Pop × Bool) → ℝ)
    (h₀ : List (Pop × Bool)) :
    ∀ (r : ℕ) (h : List (Pop × Bool)), vval α arr p F r (h₀ ++ h) =
      vval α arr p (fun h' => F (h₀ ++ h')) r h := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    rw [vval_succ, vval_succ]
    exact Finset.sum_congr rfl fun a _ => by
      rw [List.append_assoc, List.append_assoc, ih, ih]

lemma vval_cons (α : Pop → ℝ) (arr : Pop → X) (p : X → ℝ) (F : List (Pop × Bool) → ℝ)
    (x : Pop × Bool) (r : ℕ) :
    vval α arr p F r [x] = vval α arr p (fun l => F (x :: l)) r [] := by
  have := vval_shift α arr p F [x] r []
  simpa using this

/-- The record of the first `|h|` arrivals starting at index `j`, paired with the transcript `h`.
This is what the venue sees: the visitor and the oracle's answer. -/
def trace (x : ℕ → Pop) : ℕ → List Bool → List (Pop × Bool)
  | _, [] => []
  | j, b :: t => (x j, b) :: trace x (j + 1) t

@[simp] lemma trace_nil (x : ℕ → Pop) (j : ℕ) : trace x j [] = [] := rfl

lemma trace_cons (x : ℕ → Pop) (j : ℕ) (b : Bool) (t : List Bool) :
    trace x j (b :: t) = (x j, b) :: trace x (j + 1) t := rfl

lemma trace_append_one (x : ℕ → Pop) : ∀ (h : List Bool) (j : ℕ) (b : Bool),
    trace x j (h ++ [b]) = trace x j h ++ [(x (j + h.length), b)] := by
  intro h
  induction h with
  | nil => intro j b; simp [trace_cons]
  | cons b₀ t ih =>
    intro j b
    have hlen : j + 1 + t.length = j + (b₀ :: t).length := by simp; omega
    rw [List.cons_append, trace_cons, ih, trace_cons, List.cons_append, hlen]

lemma trace_reindex (x : ℕ → Pop) : ∀ (h : List Bool) (j k : ℕ),
    trace x (j + k) h = trace (fun i => x (j + i)) k h := by
  intro h
  induction h with
  | nil => intro j k; rfl
  | cons b t ih =>
    intro j k
    rw [trace_cons, trace_cons]
    congr 1
    rw [show j + k + 1 = j + (k + 1) by omega, ih]

/-- The arrival sequence determined by a finite tuple `w : Fin r → Pop` (positions `≥ r` are never
queried by a run of `r` rounds). -/
def extend [Inhabited Pop] {r : ℕ} (w : Fin r → Pop) (i : ℕ) : Pop :=
  if h : i < r then w ⟨i, h⟩ else default

lemma extend_zero [Inhabited Pop] {r : ℕ} (w : Fin (r + 1) → Pop) : extend w 0 = w 0 := by
  simp [extend]

lemma extend_tail [Inhabited Pop] {r : ℕ} (w : Fin (r + 1) → Pop) (i : ℕ) :
    extend w (1 + i) = extend (Fin.tail w) i := by
  unfold extend
  by_cases h : i < r
  · rw [dif_pos (by omega), dif_pos h]
    show w ⟨1 + i, _⟩ = w (Fin.succ ⟨i, h⟩)
    congr 1
    exact Fin.ext (by simp; omega)
  · rw [dif_neg (by omega), dif_neg h]

open Classical in
/-- **The i.i.d. arrival bridge.** For the passive probe rule `x_k = arr (w k)` with the arrival
tuple `w` drawn from the product law `∏_k α (w k)` — i.e. arrivals i.i.d. `α` and *independent of
the transcript*, since the probe rule does not read the transcript — the expected value of any
function of the venue's record is exactly `vval α arr p F Q []`.

This is the step that `OracleBounds.Attacks.PassiveUpper` assumed: there, independence across
arrivals was built into `pval`; here it is derived from the product prior on `Fin Q → Pop`. -/
lemma iid_bridge [Inhabited Pop] (α : Pop → ℝ) (arr : Pop → X) (p : X → ℝ) :
    ∀ (r : ℕ) (F : List (Pop × Bool) → ℝ),
      ∑ w : Fin r → Pop, (∏ k, α (w k)) *
        val p (fun h => arr (extend w h.length)) (fun h => F (trace (extend w) 0 h)) r []
      = vval α arr p F r [] := by
  intro r
  induction r with
  | zero =>
    intro F
    simp [vval]
  | succ r ih =>
    intro F
    have hsplit : ∀ G : (Fin (r + 1) → Pop) → ℝ,
        ∑ w : Fin (r + 1) → Pop, G w = ∑ a : Pop, ∑ w' : Fin r → Pop, G (Fin.cons a w') := by
      intro G
      rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => Pop)).sum_comp G, Fintype.sum_prod_type]
      rfl
    rw [hsplit, vval_succ]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hstep : ∀ w' : Fin r → Pop,
        (∏ k, α ((Fin.cons a w' : Fin (r + 1) → Pop) k)) *
          val p (fun h => arr (extend (Fin.cons a w' : Fin (r + 1) → Pop) h.length))
            (fun h => F (trace (extend (Fin.cons a w' : Fin (r + 1) → Pop)) 0 h)) (r + 1) []
        = α a * ((∏ k, α (w' k)) *
            (p (arr a) * val p (fun h => arr (extend w' h.length))
                (fun h => F ((a, true) :: trace (extend w') 0 h)) r [] +
              (1 - p (arr a)) * val p (fun h => arr (extend w' h.length))
                (fun h => F ((a, false) :: trace (extend w') 0 h)) r [])) := by
      intro w'
      have hprod : (∏ k, α ((Fin.cons a w' : Fin (r + 1) → Pop) k)) = α a * ∏ k, α (w' k) := by
        rw [Fin.prod_univ_succ (f := fun k => α ((Fin.cons a w' : Fin (r + 1) → Pop) k))]
        simp
      have hbranch : ∀ b : Bool,
          val p (fun h => arr (extend (Fin.cons a w') h.length))
              (fun h => F (trace (extend (Fin.cons a w')) 0 h)) r [b]
          = val p (fun h => arr (extend w' h.length))
              (fun h => F ((a, b) :: trace (extend w') 0 h)) r [] := by
        intro b
        have := val_shift p (fun h => arr (extend (Fin.cons a w') h.length))
          (fun h => F (trace (extend (Fin.cons a w')) 0 h)) [b] r []
        rw [List.append_nil] at this
        rw [this]
        congr 1
        · funext h'
          simp only [List.length_cons, List.length_append, List.length_nil]
          rw [show 0 + 1 + h'.length = 1 + h'.length by omega, extend_tail, Fin.tail_cons]
        · funext h'
          rw [show ([b] : List Bool) ++ h' = b :: h' from rfl, trace_cons, extend_zero,
            Fin.cons_zero]
          congr 2
          show trace (extend (Fin.cons a w' : Fin (r + 1) → Pop)) (1 + 0) h' =
            trace (extend w') 0 h'
          rw [trace_reindex]
          congr 1
          funext i
          rw [extend_tail, Fin.tail_cons]
      rw [hprod, val_succ]
      simp only [List.nil_append, List.length_nil, extend_zero, Fin.cons_zero]
      rw [hbranch true, hbranch false]
      ring
    simp only [hstep]
    rw [← Finset.mul_sum]
    congr 1
    have hd : ∀ i : Fin r → Pop, (∏ k, α (i k)) *
        (p (arr a) * val p (fun h => arr (extend i h.length))
            (fun h => F ((a, true) :: trace (extend i) 0 h)) r [] +
          (1 - p (arr a)) * val p (fun h => arr (extend i h.length))
            (fun h => F ((a, false) :: trace (extend i) 0 h)) r [])
        = p (arr a) * ((∏ k, α (i k)) * val p (fun h => arr (extend i h.length))
            (fun h => F ((a, true) :: trace (extend i) 0 h)) r []) +
          (1 - p (arr a)) * ((∏ k, α (i k)) * val p (fun h => arr (extend i h.length))
            (fun h => F ((a, false) :: trace (extend i) 0 h)) r []) := fun i => by ring
    simp only [hd]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ih (fun l => F ((a, true) :: l)), ih (fun l => F ((a, false) :: l)),
      List.nil_append, List.nil_append, vval_cons, vval_cons]

end Venue

/-! ## 3. `qval`: the arrival law refined by a collision flag

`OracleBounds.Attacks.Obs` records only "did the arrival reach `c`, and what did the oracle say".
Corollary 4.2.5's type-I analysis needs one more bit per arrival: whether the arrival *also*
reached a face of `G₀`, since only then does the oracle's answer stop being `Bern(ρ)` under `H₀`.
`Obs'` carries it. -/

/-- One arrival as the venue's analysis sees it: `none` = did not reach the candidate;
`some (cl, b)` = reached, `cl` records whether it also reached a face of `G₀`, `b` is the answer. -/
abbrev Obs' := Option (Bool × Bool)

/-- Forget the collision flags: what the venue's *test* actually uses. -/
def qproj (h : List Obs') : List Obs := h.map (Option.map Prod.snd)

@[simp] lemma qproj_nil : qproj [] = [] := rfl

@[simp] lemma qproj_append_one (h : List Obs') (o : Obs') :
    qproj (h ++ [o]) = qproj h ++ [Option.map Prod.snd o] := by simp [qproj]

/-- The arrival law with the collision flag: an arrival is *reaching and colliding* with
probability `mc` (then the oracle answers `true` with probability `pc`), *reaching and free* with
probability `mf` (answer probability `pf`), and non-reaching otherwise. No division: the note's
`μ_pop = mf + mc` and `γ = mc/μ_pop`. -/
noncomputable def qval (mf mc pc pf : ℝ) (F : List Obs' → ℝ) : ℕ → List Obs' → ℝ
  | 0, h => F h
  | r + 1, h => (1 - mf - mc) * qval mf mc pc pf F r (h ++ [none])
      + mc * (pc * qval mf mc pc pf F r (h ++ [some (true, true)])
            + (1 - pc) * qval mf mc pc pf F r (h ++ [some (true, false)]))
      + mf * (pf * qval mf mc pc pf F r (h ++ [some (false, true)])
            + (1 - pf) * qval mf mc pc pf F r (h ++ [some (false, false)]))

@[simp] lemma qval_zero (mf mc pc pf : ℝ) (F : List Obs' → ℝ) (h : List Obs') :
    qval mf mc pc pf F 0 h = F h := rfl

lemma qval_succ (mf mc pc pf : ℝ) (F : List Obs' → ℝ) (r : ℕ) (h : List Obs') :
    qval mf mc pc pf F (r + 1) h = (1 - mf - mc) * qval mf mc pc pf F r (h ++ [none])
      + mc * (pc * qval mf mc pc pf F r (h ++ [some (true, true)])
            + (1 - pc) * qval mf mc pc pf F r (h ++ [some (true, false)]))
      + mf * (pf * qval mf mc pc pf F r (h ++ [some (false, true)])
            + (1 - pf) * qval mf mc pc pf F r (h ++ [some (false, false)])) := rfl

section ToQval

variable {X Pop : Type*} [Fintype Pop]

open Classical in
/-- The venue's reading of one *(arrival, answer)* pair: `R` = "reaches the candidate",
`C` = "reaches a face of `G₀`". -/
noncomputable def obsOf (R C : Pop → Prop) (ab : Pop × Bool) : Obs' :=
  if R ab.1 then some (if C ab.1 then true else false, ab.2) else none

open Classical in
/-- **The oracle bridge.** If the population's response function takes the single value `pc` at
reaching-and-colliding arrivals and `pf` at reaching-and-free arrivals — which the symmetric-flip
kernel guarantees — then the venue's law on its own observations is exactly `qval`, with
`mc`/`mf` the population masses of the two kinds of reaching arrival. Nothing is assumed about the
response at non-reaching arrivals: the venue discards their answers. -/
lemma vval_eq_qval (α : Pop → ℝ) (arr : Pop → X) (p : X → ℝ) (R C : Pop → Prop)
    (mf mc pc pf : ℝ) (hsum : ∑ a, α a = 1)
    (hmc : ∑ a ∈ univ.filter (fun a => R a ∧ C a), α a = mc)
    (hmf : ∑ a ∈ univ.filter (fun a => R a ∧ ¬ C a), α a = mf)
    (hpc : ∀ a, R a → C a → p (arr a) = pc)
    (hpf : ∀ a, R a → ¬ C a → p (arr a) = pf) :
    ∀ (r : ℕ) (F : List Obs' → ℝ) (h : List (Pop × Bool)),
      vval α arr p (fun l => F (l.map (obsOf R C))) r h
        = qval mf mc pc pf F r (h.map (obsOf R C)) := by
  have hR : ∑ a ∈ univ.filter (fun a => R a), α a = mc + mf := by
    rw [← hmc, ← hmf, ← Finset.sum_filter_add_sum_filter_not
      (univ.filter (fun a => R a)) (fun a => C a) α]
    congr 2 <;> · ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; try tauto
  have hnR : ∑ a ∈ univ.filter (fun a => ¬ R a), α a = 1 - mf - mc := by
    have h2 := Finset.sum_filter_add_sum_filter_not univ (fun a => R a) α
    rw [hsum, hR] at h2
    linarith
  intro r
  induction r with
  | zero => intro F h; rfl
  | succ r ih =>
    intro F h
    rw [vval_succ, qval_succ]
    have hext : ∀ (a : Pop) (b : Bool),
        (h ++ [(a, b)]).map (obsOf R C) = h.map (obsOf R C) ++ [obsOf R C (a, b)] := by
      intro a b; simp
    have hsummand : ∀ a : Pop,
        α a * (p (arr a) * vval α arr p (fun l => F (l.map (obsOf R C))) r (h ++ [(a, true)]) +
          (1 - p (arr a)) * vval α arr p (fun l => F (l.map (obsOf R C))) r (h ++ [(a, false)]))
        = α a * (p (arr a) * qval mf mc pc pf F r (h.map (obsOf R C) ++ [obsOf R C (a, true)]) +
          (1 - p (arr a)) * qval mf mc pc pf F r
            (h.map (obsOf R C) ++ [obsOf R C (a, false)])) := by
      intro a; rw [ih, ih, hext, hext]
    simp only [hsummand]
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun a => R a),
      ← Finset.sum_filter_add_sum_filter_not (univ.filter (fun a => R a)) (fun a => C a)]
    have e1 : ∑ a ∈ (univ.filter (fun a => R a)).filter (fun a => C a),
        α a * (p (arr a) * qval mf mc pc pf F r (h.map (obsOf R C) ++ [obsOf R C (a, true)]) +
          (1 - p (arr a)) * qval mf mc pc pf F r (h.map (obsOf R C) ++ [obsOf R C (a, false)]))
        = mc * (pc * qval mf mc pc pf F r (h.map (obsOf R C) ++ [some (true, true)])
            + (1 - pc) * qval mf mc pc pf F r (h.map (obsOf R C) ++ [some (true, false)])) := by
      rw [← hmc, Finset.sum_mul]
      refine Finset.sum_congr
        (by ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; try tauto)
        fun a ha => ?_
      simp only [Finset.mem_filter] at ha
      obtain ⟨-, hRa, hCa⟩ := ha
      rw [hpc a hRa hCa, show obsOf R C (a, true) = some (true, true) by
          simp [obsOf, hRa, hCa], show obsOf R C (a, false) = some (true, false) by
          simp [obsOf, hRa, hCa]]
      try ring
    have e2 : ∑ a ∈ (univ.filter (fun a => R a)).filter (fun a => ¬ C a),
        α a * (p (arr a) * qval mf mc pc pf F r (h.map (obsOf R C) ++ [obsOf R C (a, true)]) +
          (1 - p (arr a)) * qval mf mc pc pf F r (h.map (obsOf R C) ++ [obsOf R C (a, false)]))
        = mf * (pf * qval mf mc pc pf F r (h.map (obsOf R C) ++ [some (false, true)])
            + (1 - pf) * qval mf mc pc pf F r (h.map (obsOf R C) ++ [some (false, false)])) := by
      rw [← hmf, Finset.sum_mul]
      refine Finset.sum_congr
        (by ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; try tauto)
        fun a ha => ?_
      simp only [Finset.mem_filter] at ha
      obtain ⟨-, hRa, hCa⟩ := ha
      rw [hpf a hRa hCa, show obsOf R C (a, true) = some (false, true) by
          simp [obsOf, hRa, hCa], show obsOf R C (a, false) = some (false, false) by
          simp [obsOf, hRa, hCa]]
      try ring
    have e3 : ∑ a ∈ univ.filter (fun a => ¬ R a),
        α a * (p (arr a) * qval mf mc pc pf F r (h.map (obsOf R C) ++ [obsOf R C (a, true)]) +
          (1 - p (arr a)) * qval mf mc pc pf F r (h.map (obsOf R C) ++ [obsOf R C (a, false)]))
        = (1 - mf - mc) * qval mf mc pc pf F r (h.map (obsOf R C) ++ [none]) := by
      rw [← hnR, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a ha => ?_
      simp only [Finset.mem_filter] at ha
      rw [show obsOf R C (a, true) = none by simp [obsOf, ha.2],
        show obsOf R C (a, false) = none by simp [obsOf, ha.2]]
      ring
    rw [e1, e2, e3]
    ring

end ToQval

/-! ## 4. The venue's state, and the projection onto `pval` -/

/-- One step of the venue's test on a collision-flagged observation: the `pval` state
`(Λ, S, N)` (log-likelihood ratio, reaching arrivals used, arrivals observed) together with `NC`,
the number of *colliding reaching* arrivals seen while the test was still running. -/
noncomputable def qStep (ℓ A : ℝ) (st : (ℝ × ℕ × ℕ) × ℕ) (o : Obs') : (ℝ × ℕ × ℕ) × ℕ :=
  (pStep ℓ A st.1 (Option.map Prod.snd o),
    st.2 + (if |st.1.1| < A then (match o with | some (true, _) => 1 | _ => 0) else 0))

/-- The venue's state after the flagged history `h`. -/
noncomputable def qState (ℓ A : ℝ) (h : List Obs') : (ℝ × ℕ × ℕ) × ℕ :=
  h.foldl (qStep ℓ A) ((0, 0, 0), 0)

@[simp] lemma qState_nil (ℓ A : ℝ) : qState ℓ A [] = ((0, 0, 0), 0) := rfl

lemma qState_append (ℓ A : ℝ) (h : List Obs') (o : Obs') :
    qState ℓ A (h ++ [o]) = qStep ℓ A (qState ℓ A h) o := by
  simp [qState, List.foldl_append]

lemma qFoldl_fst (ℓ A : ℝ) : ∀ (l : List Obs') (st : (ℝ × ℕ × ℕ) × ℕ),
    (l.foldl (qStep ℓ A) st).1 = (qproj l).foldl (pStep ℓ A) st.1 := by
  intro l
  induction l with
  | nil => intro st; rfl
  | cons o t ih => intro st; simpa [qproj, qStep] using ih (qStep ℓ A st o)

/-- The first three components of the venue's state are exactly `pval`'s state on the projected
(collision-forgetting) history: the test itself never reads the collision flag. -/
lemma qState_fst (ℓ A : ℝ) (h : List Obs') : (qState ℓ A h).1 = pState ℓ A (qproj h) :=
  qFoldl_fst ℓ A h ((0, 0, 0), 0)

lemma qFrozen (ℓ A : ℝ) (l : List Obs') (st : (ℝ × ℕ × ℕ) × ℕ) (hst : ¬ |st.1.1| < A) :
    l.foldl (qStep ℓ A) st = st := by
  induction l with
  | nil => rfl
  | cons o t ih =>
    have hstep : qStep ℓ A st o = st := by
      cases o with
      | none => simp [qStep, pStep_none, hst]
      | some q => obtain ⟨cl, b⟩ := q; simp [qStep, pStep_some, hst]
    rw [List.foldl_cons, hstep]
    exact ih

lemma qState_frozen (ℓ A : ℝ) (h : List Obs') (hst : ¬ |(qState ℓ A h).1.1| < A) (l : List Obs') :
    qState ℓ A (h ++ l) = qState ℓ A h := by
  unfold qState
  rw [List.foldl_append]
  exact qFrozen ℓ A l _ hst

lemma pState_frozen (ℓ A : ℝ) (h : List Obs) (hst : ¬ |(pState ℓ A h).1| < A) (l : List Obs) :
    pState ℓ A (h ++ l) = pState ℓ A h := by
  unfold pState
  rw [List.foldl_append]
  exact pFrozen ℓ A l _ hst

/-! ### Constant-on-extensions -/

lemma pval_const_on_ext (m p : List Obs → ℝ) (F : List Obs → ℝ) (Cst : ℝ) :
    ∀ (r : ℕ) (h : List Obs), (∀ l : List Obs, l.length = r → F (h ++ l) = Cst) →
      pval m p F r h = Cst := by
  intro r
  induction r with
  | zero => intro h hF; simpa using hF [] rfl
  | succ r ih =>
    intro h hF
    have key : ∀ o : Obs, pval m p F r (h ++ [o]) = Cst := by
      intro o
      refine ih (h ++ [o]) fun l hl => ?_
      rw [List.append_assoc]
      exact hF (o :: l) (by simpa using hl)
    rw [pval_succ, key, key, key]
    ring

lemma qval_const_on_ext (mf mc pc pf : ℝ) (F : List Obs' → ℝ) (Cst : ℝ) :
    ∀ (r : ℕ) (h : List Obs'), (∀ l : List Obs', l.length = r → F (h ++ l) = Cst) →
      qval mf mc pc pf F r h = Cst := by
  intro r
  induction r with
  | zero => intro h hF; simpa using hF [] rfl
  | succ r ih =>
    intro h hF
    have key : ∀ o : Obs', qval mf mc pc pf F r (h ++ [o]) = Cst := by
      intro o
      refine ih (h ++ [o]) fun l hl => ?_
      rw [List.append_assoc]
      exact hF (o :: l) (by simpa using hl)
    rw [qval_succ, key, key, key, key, key]
    ring

lemma qval_const (mf mc pc pf c : ℝ) (r : ℕ) (h : List Obs') :
    qval mf mc pc pf (fun _ => c) r h = c :=
  qval_const_on_ext mf mc pc pf _ c r h fun _ _ => rfl

/-! ### Monotonicity and range -/

lemma qval_mono {mf mc pc pf : ℝ} (hmf : 0 ≤ mf) (hmc : 0 ≤ mc) (hm : mf + mc ≤ 1)
    (hpc : 0 ≤ pc ∧ pc ≤ 1) (hpf : 0 ≤ pf ∧ pf ≤ 1) {F G : List Obs' → ℝ} :
    ∀ (r : ℕ) (h : List Obs'), (∀ h', h'.length = h.length + r → F h' ≤ G h') →
      qval mf mc pc pf F r h ≤ qval mf mc pc pf G r h := by
  intro r
  induction r with
  | zero => intro h hFG; exact hFG h (by simp)
  | succ r ih =>
    intro h hFG
    have key : ∀ o : Obs', qval mf mc pc pf F r (h ++ [o]) ≤ qval mf mc pc pf G r (h ++ [o]) :=
      fun o => ih (h ++ [o]) fun h' hl => hFG h' (by simp at hl; omega)
    have h0 : (0 : ℝ) ≤ 1 - mf - mc := by linarith
    rw [qval_succ, qval_succ]
    have t1 := mul_le_mul_of_nonneg_left (key none) h0
    have t2 := mul_le_mul_of_nonneg_left (key (some (true, true))) hpc.1
    have t3 := mul_le_mul_of_nonneg_left (key (some (true, false))) (by linarith : (0:ℝ) ≤ 1 - pc)
    have t4 := mul_le_mul_of_nonneg_left (key (some (false, true))) hpf.1
    have t5 := mul_le_mul_of_nonneg_left (key (some (false, false))) (by linarith : (0:ℝ) ≤ 1 - pf)
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add t2 t3) hmc,
      mul_le_mul_of_nonneg_left (add_le_add t4 t5) hmf]

lemma qval_mem_Icc {mf mc pc pf : ℝ} (hmf : 0 ≤ mf) (hmc : 0 ≤ mc) (hm : mf + mc ≤ 1)
    (hpc : 0 ≤ pc ∧ pc ≤ 1) (hpf : 0 ≤ pf ∧ pf ≤ 1) {F : List Obs' → ℝ}
    (hF : ∀ h, 0 ≤ F h ∧ F h ≤ 1) (r : ℕ) (h : List Obs') :
    0 ≤ qval mf mc pc pf F r h ∧ qval mf mc pc pf F r h ≤ 1 := by
  constructor
  · have := qval_mono hmf hmc hm hpc hpf (F := fun _ => (0:ℝ)) (G := F) r h fun h' _ => (hF h').1
    rwa [qval_const] at this
  · have := qval_mono hmf hmc hm hpc hpf (F := F) (G := fun _ => (1:ℝ)) r h fun h' _ => (hF h').2
    rwa [qval_const] at this

/-! ### `qval` projects onto `pval` when the collision flag does not move the bit law -/

/-- **Projection.** If reaching arrivals answer with the same probability `p` whether or not they
collide, the collision flag is pure decoration: the venue's law on the observations its test
actually reads is `PassiveUpper.pval` at reach probability `mf + mc`. -/
lemma qval_eq_pval (mf mc p : ℝ) : ∀ (r : ℕ) (F : List Obs → ℝ) (h : List Obs'),
    qval mf mc p p (fun l => F (qproj l)) r h
      = pval (fun _ => mf + mc) (fun _ => p) F r (qproj h) := by
  intro r
  induction r with
  | zero => intro F h; rfl
  | succ r ih =>
    intro F h
    rw [qval_succ, pval_succ]
    simp only [ih, qproj_append_one, Option.map_none, Option.map_some]
    ring

/-- The stopped reach probability `pReach` may be replaced by the constant `μ` whenever the leaf
function only reads the state: once the test has stopped, the state is frozen, so the arrival law
after the decision is irrelevant. -/
lemma pval_reach_const (μ ℓ A p : ℝ) (φ : ℝ × ℕ × ℕ → ℝ) :
    ∀ (r : ℕ) (h : List Obs),
      pval (pReach μ ℓ A) (fun _ => p) (fun h' => φ (pState ℓ A h')) r h
        = pval (fun _ => μ) (fun _ => p) (fun h' => φ (pState ℓ A h')) r h := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    by_cases hA : |(pState ℓ A h).1| < A
    · rw [pval_succ, pval_succ, ih, ih, ih]
      unfold pReach
      rw [if_pos hA]
    · have hfr : ∀ l : List Obs, φ (pState ℓ A (h ++ l)) = φ (pState ℓ A h) := by
        intro l; rw [pState_frozen ℓ A h hA l]
      rw [pval_const_on_ext _ _ _ (φ (pState ℓ A h)) (r + 1) h (fun l _ => hfr l),
        pval_const_on_ext _ _ _ (φ (pState ℓ A h)) (r + 1) h (fun l _ => hfr l)]

private lemma abs_add3_le (x y z : ℝ) : |x + y + z| ≤ |x| + |y| + |z| := by
  calc |x + y + z| ≤ |x + y| + |z| := abs_add_le _ _
    _ ≤ |x| + |y| + |z| := by have := abs_add_le x y; linarith

/-! ## 5. Wald for the colliding arrivals, and the coupling with the collision-free test -/

/-- **Wald's identity for the collision count.** `(mf+mc)·NC − mc·S` is a `qval` martingale: an
arrival is reaching with probability `mf+mc` and reaching-and-colliding with probability `mc`,
whatever the answers so far; hence `μ·E[NC] = mc·E[S]`, i.e. `E[NC] = γ·E[S]`. The identity holds
under *any* answer probabilities `pc`, `pf`: the arrival law does not depend on them. -/
lemma qval_coll_wald (mf mc pc pf ℓ A : ℝ) :
    ∀ (r : ℕ) (h : List Obs'),
      qval mf mc pc pf (fun h' => (mf + mc) * ((qState ℓ A h').2 : ℝ)
          - mc * ((qState ℓ A h').1.2.1 : ℝ)) r h
        = (mf + mc) * ((qState ℓ A h).2 : ℝ) - mc * ((qState ℓ A h).1.2.1 : ℝ) := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    rw [qval_succ, ih, ih, ih, ih, ih, qState_append, qState_append, qState_append,
      qState_append, qState_append]
    by_cases hA : |(qState ℓ A h).1.1| < A
    · simp only [qStep, pStep_none, pStep_some, if_pos hA, Option.map_none, Option.map_some]
      push_cast
      ring
    · simp only [qStep, pStep_none, pStep_some, if_neg hA, Option.map_none, Option.map_some]
      push_cast
      ring

/-- **Wald's identity for the log-likelihood ratio in `qval`.** `Λ − d·N` is a martingale with
`d = ℓ·(mc(2pc−1) + mf(2pf−1))`, the expected drift *per arrival* (not per reaching arrival). At
`pc = pf = p` this is `PassiveUpper.pval_wald`; at `pc = 1−ρ`, `pf = ρ` — the true `H₀` law, where
a colliding reaching arrival answers the *wrong* way — the drift degrades to
`−KL_ρ·(mf − mc) = −KL_ρ·μ(1−2γ)`. -/
lemma qval_drift_wald (mf mc pc pf ℓ A d : ℝ)
    (hd : d = ℓ * (mc * (2 * pc - 1) + mf * (2 * pf - 1))) :
    ∀ (r : ℕ) (h : List Obs'),
      qval mf mc pc pf (fun h' => (qState ℓ A h').1.1 - d * ((qState ℓ A h').1.2.2 : ℝ)) r h
        = (qState ℓ A h).1.1 - d * ((qState ℓ A h).1.2.2 : ℝ) := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    rw [qval_succ, ih, ih, ih, ih, ih, qState_append, qState_append, qState_append,
      qState_append, qState_append]
    by_cases hA : |(qState ℓ A h).1.1| < A
    · simp only [qStep, pStep_none, pStep_some, if_pos hA, Option.map_none, Option.map_some]
      push_cast
      rw [hd]; ring
    · simp only [qStep, pStep_none, pStep_some, if_neg hA, Option.map_none, Option.map_some]
      push_cast
      ring

/-- Overshoot: the expected log-likelihood ratio never leaves `(−(A+ℓ), A+ℓ)`. -/
lemma qval_lambda_bound {mf mc pc pf : ℝ} (hmf : 0 ≤ mf) (hmc : 0 ≤ mc) (hm : mf + mc ≤ 1)
    (hpc : 0 ≤ pc ∧ pc ≤ 1) (hpf : 0 ≤ pf ∧ pf ≤ 1) {ℓ A : ℝ} (hℓ : 0 ≤ ℓ) (hA : 0 < A)
    (r : ℕ) (h : List Obs') :
    -(A + ℓ) ≤ qval mf mc pc pf (fun l => (qState ℓ A l).1.1) r h ∧
      qval mf mc pc pf (fun l => (qState ℓ A l).1.1) r h ≤ A + ℓ := by
  have hb : ∀ l : List Obs', |(qState ℓ A l).1.1| < A + ℓ := by
    intro l; rw [qState_fst]; exact pState_bound ℓ A hℓ hA (qproj l)
  constructor
  · have := qval_mono hmf hmc hm hpc hpf (F := fun _ => -(A + ℓ))
      (G := fun l => (qState ℓ A l).1.1) r h fun l _ => (abs_lt.1 (hb l)).1.le
    rwa [qval_const] at this
  · have := qval_mono hmf hmc hm hpc hpf (F := fun l => (qState ℓ A l).1.1)
      (G := fun _ => A + ℓ) r h fun l _ => (abs_lt.1 (hb l)).2.le
    rwa [qval_const] at this

/-- **The coupling of Corollary 4.2.5's proof.** Two runs that differ only in the answer
probability at *colliding reaching* arrivals (`pc` against `pc'`) differ, in the probability of any
state event, by at most `|pc − pc'|` times the expected number of colliding reaching arrivals
before the test stops. Both processes freeze once `|Λ| ≥ A`, so arrivals after the decision are
not charged. The charge is computed under the `pc` law — instantiate `pc := ρ` to get the note's
`γ·E⁰[τ]`, an expectation under the collision-free test. -/
lemma qval_coupling {mf mc pc pc' pf : ℝ} (ℓ A : ℝ)
    (hmf : 0 ≤ mf) (hmc : 0 ≤ mc) (hm : mf + mc ≤ 1)
    (hpc : 0 ≤ pc ∧ pc ≤ 1) (hpc' : 0 ≤ pc' ∧ pc' ≤ 1) (hpf : 0 ≤ pf ∧ pf ≤ 1)
    {φ : (ℝ × ℕ × ℕ) × ℕ → ℝ} (hφ : ∀ st, 0 ≤ φ st ∧ φ st ≤ 1) :
    ∀ (r : ℕ) (h : List Obs'),
      |qval mf mc pc pf (fun h' => φ (qState ℓ A h')) r h
        - qval mf mc pc' pf (fun h' => φ (qState ℓ A h')) r h|
      ≤ |pc - pc'| * (qval mf mc pc pf (fun h' => ((qState ℓ A h').2 : ℝ)) r h
          - ((qState ℓ A h).2 : ℝ)) := by
  have h0 : (0 : ℝ) ≤ 1 - mf - mc := by linarith
  intro r
  induction r with
  | zero => intro h; simp
  | succ r ih =>
    intro h
    by_cases hA : |(qState ℓ A h).1.1| < A
    · -- the test is still running: charge `mc·|pc − pc'|` for this arrival
      have hN : ∀ o : Obs', ((qState ℓ A (h ++ [o])).2 : ℝ) =
          ((qState ℓ A h).2 : ℝ) + (if o = some (true, true) ∨ o = some (true, false)
            then (1 : ℝ) else 0) := by
        intro o
        rw [qState_append]
        match o with
        | none => simp [qStep, hA]
        | some (true, true) => simp [qStep, hA]
        | some (true, false) => simp [qStep, hA]
        | some (false, true) => simp [qStep, hA]
        | some (false, false) => simp [qStep, hA]
      set N0 : ℝ := ((qState ℓ A h).2 : ℝ) with hN0
      set Φ : List Obs' → ℝ := fun h' => φ (qState ℓ A h') with hΦ
      set NN : List Obs' → ℝ := fun h' => ((qState ℓ A h').2 : ℝ) with hNN
      set an := qval mf mc pc pf Φ r (h ++ [none]) with han
      set bn := qval mf mc pc' pf Φ r (h ++ [none]) with hbn
      set att := qval mf mc pc pf Φ r (h ++ [some (true, true)]) with hatt
      set btt := qval mf mc pc' pf Φ r (h ++ [some (true, true)]) with hbtt
      set atf := qval mf mc pc pf Φ r (h ++ [some (true, false)]) with hatf
      set btf := qval mf mc pc' pf Φ r (h ++ [some (true, false)]) with hbtf
      set aft := qval mf mc pc pf Φ r (h ++ [some (false, true)]) with haft
      set bft := qval mf mc pc' pf Φ r (h ++ [some (false, true)]) with hbft
      set aff := qval mf mc pc pf Φ r (h ++ [some (false, false)]) with haff
      set bff := qval mf mc pc' pf Φ r (h ++ [some (false, false)]) with hbff
      set Dn := qval mf mc pc pf NN r (h ++ [none]) - N0 with hDn
      set Dtt := qval mf mc pc pf NN r (h ++ [some (true, true)]) - (N0 + 1) with hDtt
      set Dtf := qval mf mc pc pf NN r (h ++ [some (true, false)]) - (N0 + 1) with hDtf
      set Dft := qval mf mc pc pf NN r (h ++ [some (false, true)]) - N0 with hDft
      set Dff := qval mf mc pc pf NN r (h ++ [some (false, false)]) - N0 with hDff
      -- the induction hypothesis at each child
      have ihn : |an - bn| ≤ |pc - pc'| * Dn := by
        have := ih (h ++ [none]); rw [hN none] at this; simpa using this
      have ihtt : |att - btt| ≤ |pc - pc'| * Dtt := by
        have := ih (h ++ [some (true, true)]); rw [hN (some (true, true))] at this
        simpa using this
      have ihtf : |atf - btf| ≤ |pc - pc'| * Dtf := by
        have := ih (h ++ [some (true, false)]); rw [hN (some (true, false))] at this
        simpa using this
      have ihft : |aft - bft| ≤ |pc - pc'| * Dft := by
        have := ih (h ++ [some (false, true)]); rw [hN (some (false, true))] at this
        simpa using this
      have ihff : |aff - bff| ≤ |pc - pc'| * Dff := by
        have := ih (h ++ [some (false, false)]); rw [hN (some (false, false))] at this
        simpa using this
      -- `|b_tt − b_tf| ≤ 1`, since both are probabilities
      have hb01 : ∀ x : ℝ, x ∈ ({btt, btf} : Set ℝ) → 0 ≤ x ∧ x ≤ 1 := by
        intro x hx
        rcases hx with hx | hx
        · subst hx; exact qval_mem_Icc hmf hmc hm hpc' hpf (fun h' => hφ _) r _
        · simp only [Set.mem_singleton_iff] at hx; subst hx
          exact qval_mem_Icc hmf hmc hm hpc' hpf (fun h' => hφ _) r _
      have hbtt01 := hb01 btt (by simp)
      have hbtf01 := hb01 btf (by simp)
      have hbd : |btt - btf| ≤ 1 :=
        abs_le.2 ⟨by linarith [hbtt01.1, hbtf01.2], by linarith [hbtt01.2, hbtf01.1]⟩
      -- the three blocks
      have b1 : |(1 - mf - mc) * (an - bn)| ≤ (1 - mf - mc) * (|pc - pc'| * Dn) := by
        rw [abs_mul, abs_of_nonneg h0]; exact mul_le_mul_of_nonneg_left ihn h0
      have b2 : |mc * (pc * (att - btt) + (1 - pc) * (atf - btf) + (pc - pc') * (btt - btf))|
          ≤ mc * (pc * (|pc - pc'| * Dtt) + (1 - pc) * (|pc - pc'| * Dtf) + |pc - pc'|) := by
        rw [abs_mul, abs_of_nonneg hmc]
        refine mul_le_mul_of_nonneg_left ?_ hmc
        have t1 : |pc * (att - btt)| ≤ pc * (|pc - pc'| * Dtt) := by
          rw [abs_mul, abs_of_nonneg hpc.1]; exact mul_le_mul_of_nonneg_left ihtt hpc.1
        have t2 : |(1 - pc) * (atf - btf)| ≤ (1 - pc) * (|pc - pc'| * Dtf) := by
          rw [abs_mul, abs_of_nonneg (by linarith [hpc.2] : (0:ℝ) ≤ 1 - pc)]
          exact mul_le_mul_of_nonneg_left ihtf (by linarith [hpc.2])
        have t3 : |(pc - pc') * (btt - btf)| ≤ |pc - pc'| := by
          rw [abs_mul]
          calc |pc - pc'| * |btt - btf| ≤ |pc - pc'| * 1 :=
                mul_le_mul_of_nonneg_left hbd (abs_nonneg _)
            _ = |pc - pc'| := mul_one _
        calc |pc * (att - btt) + (1 - pc) * (atf - btf) + (pc - pc') * (btt - btf)|
            ≤ |pc * (att - btt)| + |(1 - pc) * (atf - btf)| + |(pc - pc') * (btt - btf)| :=
              abs_add3_le _ _ _
          _ ≤ _ := by linarith
      have b3 : |mf * (pf * (aft - bft) + (1 - pf) * (aff - bff))|
          ≤ mf * (pf * (|pc - pc'| * Dft) + (1 - pf) * (|pc - pc'| * Dff)) := by
        rw [abs_mul, abs_of_nonneg hmf]
        refine mul_le_mul_of_nonneg_left ?_ hmf
        have t1 : |pf * (aft - bft)| ≤ pf * (|pc - pc'| * Dft) := by
          rw [abs_mul, abs_of_nonneg hpf.1]; exact mul_le_mul_of_nonneg_left ihft hpf.1
        have t2 : |(1 - pf) * (aff - bff)| ≤ (1 - pf) * (|pc - pc'| * Dff) := by
          rw [abs_mul, abs_of_nonneg (by linarith [hpf.2] : (0:ℝ) ≤ 1 - pf)]
          exact mul_le_mul_of_nonneg_left ihff (by linarith [hpf.2])
        calc |pf * (aft - bft) + (1 - pf) * (aff - bff)|
            ≤ |pf * (aft - bft)| + |(1 - pf) * (aff - bff)| := abs_add_le _ _
          _ ≤ _ := by linarith
      -- put it together
      have hNCval : qval mf mc pc pf NN (r + 1) h
          = (1 - mf - mc) * (Dn + N0) + mc * (pc * (Dtt + (N0 + 1)) + (1 - pc) * (Dtf + (N0 + 1)))
            + mf * (pf * (Dft + N0) + (1 - pf) * (Dff + N0)) := by
        rw [qval_succ, hDn, hDtt, hDtf, hDft, hDff]; ring
      have hsplit : qval mf mc pc pf Φ (r + 1) h - qval mf mc pc' pf Φ (r + 1) h
          = (1 - mf - mc) * (an - bn)
            + mc * (pc * (att - btt) + (1 - pc) * (atf - btf) + (pc - pc') * (btt - btf))
            + mf * (pf * (aft - bft) + (1 - pf) * (aff - bff)) := by
        rw [qval_succ, qval_succ, ← han, ← hbn, ← hatt, ← hbtt, ← hatf, ← hbtf, ← haft, ← hbft,
          ← haff, ← hbff]
        ring
      rw [hsplit, hNCval]
      calc |(1 - mf - mc) * (an - bn)
              + mc * (pc * (att - btt) + (1 - pc) * (atf - btf) + (pc - pc') * (btt - btf))
              + mf * (pf * (aft - bft) + (1 - pf) * (aff - bff))|
          ≤ |(1 - mf - mc) * (an - bn)|
            + |mc * (pc * (att - btt) + (1 - pc) * (atf - btf) + (pc - pc') * (btt - btf))|
            + |mf * (pf * (aft - bft) + (1 - pf) * (aff - bff))| := abs_add3_le _ _ _
        _ ≤ ((1 - mf - mc) * (|pc - pc'| * Dn)
            + mc * (pc * (|pc - pc'| * Dtt) + (1 - pc) * (|pc - pc'| * Dtf) + |pc - pc'|))
            + mf * (pf * (|pc - pc'| * Dft) + (1 - pf) * (|pc - pc'| * Dff)) := by linarith
        _ = |pc - pc'| * ((1 - mf - mc) * (Dn + N0)
              + mc * (pc * (Dtt + (N0 + 1)) + (1 - pc) * (Dtf + (N0 + 1)))
              + mf * (pf * (Dft + N0) + (1 - pf) * (Dff + N0)) - N0) := by ring
    · -- the test has stopped: both runs are frozen, and nothing more is charged
      have hfrφ : ∀ l : List Obs', φ (qState ℓ A (h ++ l)) = φ (qState ℓ A h) := fun l => by
        rw [qState_frozen ℓ A h hA l]
      have hfrN : ∀ l : List Obs', ((qState ℓ A (h ++ l)).2 : ℝ) = ((qState ℓ A h).2 : ℝ) :=
        fun l => by rw [qState_frozen ℓ A h hA l]
      rw [qval_const_on_ext mf mc pc pf _ (φ (qState ℓ A h)) (r + 1) h (fun l _ => hfrφ l),
        qval_const_on_ext mf mc pc' pf _ (φ (qState ℓ A h)) (r + 1) h (fun l _ => hfrφ l),
        qval_const_on_ext mf mc pc pf _ ((qState ℓ A h).2 : ℝ) (r + 1) h (fun l _ => hfrN l)]
      simp

/-! ## 6. Linearity -/

lemma qval_lin (mf mc pc pf a b : ℝ) (F G : List Obs' → ℝ) : ∀ (r : ℕ) (h : List Obs'),
    qval mf mc pc pf (fun h' => a * F h' + b * G h') r h
      = a * qval mf mc pc pf F r h + b * qval mf mc pc pf G r h := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih => intro h; simp only [qval_succ, ih]; ring

lemma pval_smul (m p : List Obs → ℝ) (b : ℝ) (F : List Obs → ℝ) (r : ℕ) (h : List Obs) :
    pval m p (fun h' => b * F h') r h = b * pval m p F r h := by
  have := pval_affine m p 0 b F r h
  simpa using this

lemma pval_lin (m p : List Obs → ℝ) (a b : ℝ) (F G : List Obs → ℝ) (r : ℕ) (h : List Obs) :
    pval m p (fun h' => a * F h' + b * G h') r h
      = a * pval m p F r h + b * pval m p G r h := by
  rw [pval_add m p (fun h' => a * F h') (fun h' => b * G h') r h, pval_smul, pval_smul]

/-! ## 7. The venue's record, and the two laws it induces -/

section Record

variable {X Pop : Type*} [Fintype Pop] [Inhabited Pop]

open Classical in
/-- What the venue's *test* reads off one arrival: `none` if the arrival did not reach the
candidate (its answer is discarded), `some b` if it did. Unlike `obsOf` this uses no information
the venue does not have. -/
noncomputable def obsPlain (R : Pop → Prop) (ab : Pop × Bool) : Obs :=
  if R ab.1 then some ab.2 else none

open Classical in
lemma qproj_map_obsOf (R C : Pop → Prop) (l : List (Pop × Bool)) :
    qproj (l.map (obsOf R C)) = l.map (obsPlain R) := by
  simp only [qproj, List.map_map]
  refine List.map_congr_left fun ab _ => ?_
  by_cases h : R ab.1 <;> simp [obsOf, obsPlain, h, Function.comp]

/-- The venue's record after the transcript `h`, for the arrival sequence `w`. -/
noncomputable def venueObs (R : Pop → Prop) (w : ℕ → Pop) (h : List Bool) : List Obs :=
  (trace w 0 h).map (obsPlain R)

/-- The venue's SPRT state after the transcript `h`. -/
noncomputable def venueState (R : Pop → Prop) (ℓ A : ℝ) (w : ℕ → Pop) (h : List Bool) :
    ℝ × ℕ × ℕ := pState ℓ A (venueObs R w h)

/-- The venue's decision after the transcript `h`: `1` for "enrolled". -/
noncomputable def venueDecide (R : Pop → Prop) (ℓ A : ℝ) (w : ℕ → Pop) (h : List Bool) : ℝ :=
  pDecide ℓ A (venueObs R w h)

open Classical in
/-- **Step 1+2, collision-flagged form.** The gallery/oracle process with i.i.d. arrivals equals
the flagged arrival law `qval`. -/
lemma venue_flag_law (arr : Pop → X) (α : Pop → ℝ) (p : X → ℝ) (R C : Pop → Prop)
    (mf mc pc pf : ℝ) (hα1 : ∑ a, α a = 1)
    (hmc : ∑ a ∈ univ.filter (fun a => R a ∧ C a), α a = mc)
    (hmf : ∑ a ∈ univ.filter (fun a => R a ∧ ¬ C a), α a = mf)
    (hpc : ∀ a, R a → C a → p (arr a) = pc) (hpf : ∀ a, R a → ¬ C a → p (arr a) = pf)
    (r : ℕ) (F : List Obs' → ℝ) :
    ∑ w : Fin r → Pop, (∏ k, α (w k)) *
        val p (fun h => arr (extend w h.length))
          (fun h => F ((trace (extend w) 0 h).map (obsOf R C))) r []
      = qval mf mc pc pf F r [] := by
  rw [iid_bridge α arr p r (fun l => F (l.map (obsOf R C))),
    vval_eq_qval α arr p R C mf mc pc pf hα1 hmc hmf hpc hpf r F []]
  simp

open Classical in
/-- **Steps 1–3.** When reaching arrivals answer with one probability `pconst` whether or not they
collide, the venue's record is an i.i.d. Bernoulli sequence: `pval` at reach rate `mf + mc` and
answer rate `pconst`. This is exactly `PassiveUpper`'s assumed model, now derived. -/
lemma venue_plain_law (arr : Pop → X) (α : Pop → ℝ) (p : X → ℝ) (R C : Pop → Prop)
    (mf mc pconst : ℝ) (hα1 : ∑ a, α a = 1)
    (hmc : ∑ a ∈ univ.filter (fun a => R a ∧ C a), α a = mc)
    (hmf : ∑ a ∈ univ.filter (fun a => R a ∧ ¬ C a), α a = mf)
    (hp : ∀ a, R a → p (arr a) = pconst)
    (r : ℕ) (F : List Obs → ℝ) :
    ∑ w : Fin r → Pop, (∏ k, α (w k)) *
        val p (fun h => arr (extend w h.length))
          (fun h => F (venueObs R (extend w) h)) r []
      = pval (fun _ => mf + mc) (fun _ => pconst) F r [] := by
  have h1 := venue_flag_law arr α p R C mf mc pconst pconst hα1 hmc hmf
    (fun a hR _ => hp a hR) (fun a hR _ => hp a hR) r (fun l => F (qproj l))
  rw [qval_eq_pval mf mc pconst r F []] at h1
  simp only [qproj_nil] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2
  funext h
  rw [venueObs, ← qproj_map_obsOf R C]

end Record

/-! ## 8. Corollary 4.2.5 on the gallery -/

section GalleryVenue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [Fintype Fine]
variable {Pop : Type*} [Fintype Pop] [Inhabited Pop]
variable (G : Gallery E ι Fine) [Nonempty ι] (V : ι → Fine) (c : Sph E)
variable (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
variable (hκq : ∀ s ≤ G.thr, G.κ s = ρ) (hκl : ∀ s, G.thr < s → G.κ s = 1 - ρ)
variable (arr : Pop → Sph E) (α : Pop → ℝ) (hα0 : ∀ a, 0 ≤ α a) (hα1 : ∑ a, α a = 1)
variable (μ γ : ℝ) (hμ0 : 0 < μ)

open Classical in
/-- Basic consequences of the two mass hypotheses. -/
private lemma mass_facts (hα0 : ∀ a, 0 ≤ α a) (hα1 : ∑ a, α a = 1)
    (hmc : ∑ a ∈ univ.filter (fun a => G.reachC c.1 (arr a) ∧ G.thr < G.score V (arr a)), α a
        = γ * μ)
    (hmf : ∑ a ∈ univ.filter (fun a => G.reachC c.1 (arr a) ∧ ¬ G.thr < G.score V (arr a)), α a
        = (1 - γ) * μ) :
    0 ≤ γ * μ ∧ 0 ≤ (1 - γ) * μ ∧ (1 - γ) * μ + γ * μ ≤ 1 := by
  refine ⟨hmc ▸ Finset.sum_nonneg fun a _ => hα0 a, hmf ▸ Finset.sum_nonneg fun a _ => hα0 a, ?_⟩
  rw [← hmc, ← hmf]
  have hunion : ∑ a ∈ univ.filter (fun a => G.reachC c.1 (arr a) ∧ ¬ G.thr < G.score V (arr a)),
        α a +
      ∑ a ∈ univ.filter (fun a => G.reachC c.1 (arr a) ∧ G.thr < G.score V (arr a)), α a
      = ∑ a ∈ univ.filter (fun a => G.reachC c.1 (arr a)), α a := by
    rw [← Finset.sum_filter_add_sum_filter_not (univ.filter (fun a => G.reachC c.1 (arr a)))
      (fun a => G.thr < G.score V (arr a)) α]
    rw [add_comm]
    congr 2 <;> · ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; try tauto
  rw [hunion]
  calc ∑ a ∈ univ.filter (fun a => G.reachC c.1 (arr a)), α a ≤ ∑ a, α a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun a _ _ => hα0 a
    _ = 1 := hα1

include hρ0 hρ1 hκq hκl hα0 hα1 hμ0 in
open Classical in
/-- **Corollary 4.2.5 (passive venue), on the gallery process.**

A venue holding the candidate `c` watches `Q` arrivals drawn i.i.d. from the population law `α`
on the finite arrival alphabet `Pop` (the arrival tuple `w : Fin Q → Pop` has prior
`∏ₖ α (w k)`; the probe rule `Gallery.passiveProbe` never reads the transcript, so the arrivals
are independent of it), runs Wald's test of Theorem 4.2.3 on the arrivals that reach `c`, and
ignores the rest. `μ` is the population mass of arrivals reaching `c` (`μ_pop`); `γ` is the
conditional probability that an arrival reaching `c` also reaches a face of `G₀` (so the joint
mass is `γ·μ`). `H₀` is the enrolled gallery `V = G₀` (`G.resp V`), `H₁` is `G₀ ∪ {c}`
(`G.respWith V c`), and the oracle is the symmetric-flip kernel `κ = ρ` at or below `thr`,
`1 − ρ` above. With `A := log(2/δ)`, `ℓ := log((1−ρ)/ρ)` and `KL_ρ := (1−2ρ)ℓ`:

* the venue's record is a probability distribution over arrival tuples (first conjunct);
* `E¹[#arrivals before a decision] ≤ (A + ℓ)/(KL_ρ·μ)` (second);
* `δ_I ≤ δ/2 + γ·(A + ℓ)/KL_ρ` (third) — the note's statement exactly, with the collision paid
  once per reaching arrival;
* `δ_II ≤ δ/2 + (A + ℓ)/(KL_ρ·μ·Q)`, the budgeted form of the note's `δ_II ≤ δ/2` (fourth).

Nothing about the arrival process is assumed: the i.i.d. structure is the product prior, and the
per-arrival Bernoulli laws are computed from `G.resp`/`G.respWith`. -/
theorem passive_venue_gallery
    (hmc : ∑ a ∈ univ.filter (fun a => G.reachC c.1 (arr a) ∧ G.thr < G.score V (arr a)), α a
        = γ * μ)
    (hmf : ∑ a ∈ univ.filter (fun a => G.reachC c.1 (arr a) ∧ ¬ G.thr < G.score V (arr a)), α a
        = (1 - γ) * μ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ w : Fin Q → Pop, ∏ k, α (w k)) = 1 ∧
    (∑ w : Fin Q → Pop, (∏ k, α (w k)) *
        val (G.respWith V c.1)
          (Gallery.passiveProbe (fun (w : Fin Q → Pop) (k : ℕ) => arr (extend w k)) w)
          (fun h => ((venueState (fun a => G.reachC c.1 (arr a))
            (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ)) (extend w) h).2.2 : ℝ)) Q [])
      ≤ (Real.log (2 / δ) + Real.log ((1 - ρ) / ρ)) /
          ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * μ) ∧
    (∑ w : Fin Q → Pop, (∏ k, α (w k)) *
        val (G.resp V)
          (Gallery.passiveProbe (fun (w : Fin Q → Pop) (k : ℕ) => arr (extend w k)) w)
          (venueDecide (fun a => G.reachC c.1 (arr a))
            (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ)) (extend w)) Q [])
      ≤ δ / 2 + γ * ((Real.log (2 / δ) + Real.log ((1 - ρ) / ρ)) /
          ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ))) ∧
    (∑ w : Fin Q → Pop, (∏ k, α (w k)) *
        val (G.respWith V c.1)
          (Gallery.passiveProbe (fun (w : Fin Q → Pop) (k : ℕ) => arr (extend w k)) w)
          (fun h => 1 - venueDecide (fun a => G.reachC c.1 (arr a))
            (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ)) (extend w) h) Q [])
      ≤ δ / 2 + (Real.log (2 / δ) + Real.log ((1 - ρ) / ρ)) /
          ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * μ * Q) := by
  classical
  obtain ⟨hmc0, hmf0, hm1⟩ := mass_facts G V c arr α μ γ hα0 hα1 hmc hmf
  have hμ1 : μ ≤ 1 := by nlinarith
  have hρ1' : 0 < 1 - ρ := by linarith
  have hratio : 1 < (1 - ρ) / ρ := by rw [lt_div_iff₀ hρ0]; linarith
  obtain ⟨hEN0, hEN1, hI, hII⟩ := passive_sprt_delta ρ μ δ hρ0 hρ1 hμ0 hμ1 hδ0 hδ1 Q hQ
  have harr := pval_arrivals (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ)) μ ρ Q []
  set ℓ := Real.log ((1 - ρ) / ρ) with hℓdef
  set A := Real.log (2 / δ) with hAdef
  set mc := γ * μ with hmcdef
  set mf := (1 - γ) * μ with hmfdef
  have hℓ : 0 < ℓ := Real.log_pos hratio
  have hApos : 0 < A := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hKL : 0 < (1 - 2 * ρ) * ℓ := mul_pos (by linarith) hℓ
  have hsum : mf + mc = μ := by rw [hmfdef, hmcdef]; ring
  have hγ0 : 0 ≤ γ := by rw [hmcdef] at hmc0; nlinarith
  have hρ01 : (0 : ℝ) ≤ ρ ∧ ρ ≤ 1 := ⟨hρ0.le, by linarith⟩
  have hρ01' : (0 : ℝ) ≤ 1 - ρ ∧ (1 : ℝ) - ρ ≤ 1 := ⟨by linarith, by linarith⟩
  -- the probe rule is the passive one, and it never reads the transcript
  have hprobe : ∀ w : Fin Q → Pop,
      Gallery.passiveProbe (fun (w : Fin Q → Pop) (k : ℕ) => arr (extend w k)) w
        = fun h => arr (extend w h.length) := fun _ => rfl
  -- the per-arrival response laws at the symmetric-flip kernel
  have hp1 : ∀ a, G.reachC c.1 (arr a) → G.respWith V c.1 (arr a) = 1 - ρ := fun a hRa =>
    (reaching_resp G V c.1 ρ hκq hκl (arr a) hRa).1
  have hp0c : ∀ a, G.reachC c.1 (arr a) → G.thr < G.score V (arr a) →
      G.resp V (arr a) = 1 - ρ := fun a _ hCa => hκl _ hCa
  have hp0f : ∀ a, G.reachC c.1 (arr a) → ¬ G.thr < G.score V (arr a) →
      G.resp V (arr a) = ρ := fun a _ hCa => hκq _ (not_lt.mp hCa)
  -- (0) the product prior is a probability distribution
  have hprob : (∑ w : Fin Q → Pop, ∏ k, α (w k)) = 1 := by
    have := venue_plain_law (X := Sph E) arr α (G.respWith V c.1)
      (fun a => G.reachC c.1 (arr a)) (fun a => G.thr < G.score V (arr a)) mf mc (1 - ρ)
      hα1 hmc hmf hp1 Q (fun _ => (1 : ℝ))
    simpa [val_const, pval_const] using this
  -- the venue's law under `H₁`, on the observations its test reads
  have law1 : ∀ F : List Obs → ℝ,
      (∑ w : Fin Q → Pop, (∏ k, α (w k)) *
        val (G.respWith V c.1)
          (Gallery.passiveProbe (fun (w : Fin Q → Pop) (k : ℕ) => arr (extend w k)) w)
          (fun h => F (venueObs (fun a => G.reachC c.1 (arr a)) (extend w) h)) Q [])
      = pval (fun _ => μ) (fun _ => 1 - ρ) F Q [] := by
    intro F
    simp only [hprobe]
    rw [venue_plain_law (X := Sph E) arr α (G.respWith V c.1)
      (fun a => G.reachC c.1 (arr a)) (fun a => G.thr < G.score V (arr a)) mf mc (1 - ρ)
      hα1 hmc hmf hp1 Q F, hsum]
  -- the venue's law under `H₀`, keeping the collision flag
  have law0 : ∀ F : List Obs' → ℝ,
      (∑ w : Fin Q → Pop, (∏ k, α (w k)) *
        val (G.resp V) (fun h => arr (extend w h.length))
          (fun h => F ((trace (extend w) 0 h).map
            (obsOf (fun a => G.reachC c.1 (arr a))
              (fun a => G.thr < G.score V (arr a))))) Q [])
      = qval mf mc (1 - ρ) ρ F Q [] := fun F =>
    venue_flag_law (X := Sph E) arr α (G.resp V) (fun a => G.reachC c.1 (arr a))
      (fun a => G.thr < G.score V (arr a)) mf mc (1 - ρ) ρ hα1 hmc hmf hp0c hp0f Q F
  refine ⟨hprob, ?_, ?_, ?_⟩
  · -- (i) expected arrivals before a decision, under `H₁`
    rw [show (fun (w : Fin Q → Pop) => (∏ k, α (w k)) *
        val (G.respWith V c.1)
          (Gallery.passiveProbe (fun (w : Fin Q → Pop) (k : ℕ) => arr (extend w k)) w)
          (fun h => ((venueState (fun a => G.reachC c.1 (arr a)) ℓ A (extend w) h).2.2 : ℝ))
          Q []) = fun (w : Fin Q → Pop) => (∏ k, α (w k)) *
        val (G.respWith V c.1)
          (Gallery.passiveProbe (fun (w : Fin Q → Pop) (k : ℕ) => arr (extend w k)) w)
          (fun h => (fun l => ((pState ℓ A l).2.2 : ℝ))
            (venueObs (fun a => G.reachC c.1 (arr a)) (extend w) h)) Q [] from rfl,
      law1 (fun l => ((pState ℓ A l).2.2 : ℝ)),
      ← pval_reach_const μ ℓ A (1 - ρ) (fun st => ((st.2.2 : ℕ) : ℝ)) Q []]
    exact hEN1
  · -- (ii) type-I error: the collision-free test, plus the colliding reaching arrivals
    have hleaf : ∀ w : Fin Q → Pop,
        venueDecide (fun a => G.reachC c.1 (arr a)) ℓ A (extend w)
        = fun h => if A ≤ (qState ℓ A ((trace (extend w) 0 h).map
            (obsOf (fun a => G.reachC c.1 (arr a))
              (fun a => G.thr < G.score V (arr a))))).1.1 then (1 : ℝ) else 0 := by
      intro w
      funext h
      unfold venueDecide venueObs pDecide
      rw [qState_fst, qproj_map_obsOf]
    simp only [hprobe, hleaf]
    rw [law0 (fun l => if A ≤ (qState ℓ A l).1.1 then (1 : ℝ) else 0)]
    -- the coupling with the collision-free test
    have hφ : ∀ st : (ℝ × ℕ × ℕ) × ℕ,
        0 ≤ (if A ≤ st.1.1 then (1 : ℝ) else 0) ∧ (if A ≤ st.1.1 then (1 : ℝ) else 0) ≤ 1 := by
      intro st; split_ifs <;> norm_num
    have hcoup := qval_coupling (mf := mf) (mc := mc) (pc := ρ) (pc' := 1 - ρ) (pf := ρ)
      ℓ A hmf0 hmc0 hm1 hρ01 hρ01' hρ01
      (φ := fun st => if A ≤ st.1.1 then (1 : ℝ) else 0) hφ Q []
    have habs : |ρ - (1 - ρ)| = 1 - 2 * ρ := by rw [abs_of_nonpos (by linarith)]; ring
    rw [habs] at hcoup
    simp only [qState_nil, Nat.cast_zero, sub_zero] at hcoup
    -- the collision-free test is Theorem 4.2.3's: `δ_I ≤ δ/2`
    have hfree : qval mf mc ρ ρ (fun l => if A ≤ (qState ℓ A l).1.1 then (1 : ℝ) else 0) Q []
        = pval (fun _ => μ) (fun _ => ρ)
            (fun h => if A ≤ (pState ℓ A h).1 then (1 : ℝ) else 0) Q [] := by
      have h1 := qval_eq_pval mf mc ρ Q
        (fun h => if A ≤ (pState ℓ A h).1 then (1 : ℝ) else 0) []
      simp only [qproj_nil] at h1
      rw [hsum] at h1
      rw [← h1]
      congr 1
      funext l
      rw [qState_fst]
    have hfree' : qval mf mc ρ ρ (fun l => if A ≤ (qState ℓ A l).1.1 then (1 : ℝ) else 0) Q []
        ≤ δ / 2 := by
      rw [hfree, ← pval_reach_const μ ℓ A ρ (fun st => if A ≤ st.1 then (1 : ℝ) else 0) Q []]
      exact hI
    -- Wald for the collision count: `μ·E[NC] = mc·E[S]`
    have hlin := qval_lin mf mc ρ ρ (mf + mc) (-mc)
      (fun l => ((qState ℓ A l).2 : ℝ)) (fun l => ((qState ℓ A l).1.2.1 : ℝ)) Q []
    simp only [neg_mul, ← sub_eq_add_neg] at hlin
    have hzero : (mf + mc) * qval mf mc ρ ρ (fun l => ((qState ℓ A l).2 : ℝ)) Q []
        - mc * qval mf mc ρ ρ (fun l => ((qState ℓ A l).1.2.1 : ℝ)) Q [] = 0 := by
      rw [← hlin, qval_coll_wald]
      simp
    -- the reaching count is `pval`'s
    have hSproj : qval mf mc ρ ρ (fun l => ((qState ℓ A l).1.2.1 : ℝ)) Q []
        = pval (fun _ => μ) (fun _ => ρ) (fun h => ((pState ℓ A h).2.1 : ℝ)) Q [] := by
      have h1 := qval_eq_pval mf mc ρ Q (fun h => ((pState ℓ A h).2.1 : ℝ)) []
      simp only [qproj_nil] at h1
      rw [hsum] at h1
      rw [← h1]
      congr 1
      funext l
      rw [qState_fst]
    -- Wald for the arrivals: `E[S] = μ·E[N]`
    have harr' : pval (fun _ => μ) (fun _ => ρ)
        (fun h => ((pState ℓ A h).2.1 : ℝ) - μ * ((pState ℓ A h).2.2 : ℝ)) Q [] = 0 := by
      rw [← pval_reach_const μ ℓ A ρ
        (fun st => ((st.2.1 : ℕ) : ℝ) - μ * ((st.2.2 : ℕ) : ℝ)) Q []]
      simpa using harr
    have hSN : pval (fun _ => μ) (fun _ => ρ) (fun h => ((pState ℓ A h).2.1 : ℝ)) Q []
        = μ * pval (fun _ => μ) (fun _ => ρ) (fun h => ((pState ℓ A h).2.2 : ℝ)) Q [] := by
      have hl := pval_lin (fun _ : List Obs => μ) (fun _ : List Obs => ρ) 1 (-μ)
        (fun h => ((pState ℓ A h).2.1 : ℝ)) (fun h => ((pState ℓ A h).2.2 : ℝ)) Q []
      simp only [one_mul, neg_mul, ← sub_eq_add_neg] at hl
      rw [hl] at harr'
      linarith
    have hN0 : pval (fun _ => μ) (fun _ => ρ) (fun h => ((pState ℓ A h).2.2 : ℝ)) Q []
        ≤ (A + ℓ) / ((1 - 2 * ρ) * ℓ * μ) := by
      rw [← pval_reach_const μ ℓ A ρ (fun st => ((st.2.2 : ℕ) : ℝ)) Q []]
      exact hEN0
    -- hence `E[NC] ≤ γ·(A+ℓ)/KL_ρ`
    have hT0 : 0 ≤ (A + ℓ) / ((1 - 2 * ρ) * ℓ) := by positivity
    have hNC : qval mf mc ρ ρ (fun l => ((qState ℓ A l).2 : ℝ)) Q []
        ≤ γ * ((A + ℓ) / ((1 - 2 * ρ) * ℓ)) := by
      have h1 : μ * qval mf mc ρ ρ (fun l => ((qState ℓ A l).2 : ℝ)) Q []
          = mc * qval mf mc ρ ρ (fun l => ((qState ℓ A l).1.2.1 : ℝ)) Q [] := by
        rw [← hsum]; linarith
      rw [hSproj, hSN] at h1
      have h2 : mc * (μ * pval (fun _ => μ) (fun _ => ρ)
            (fun h => ((pState ℓ A h).2.2 : ℝ)) Q [])
          ≤ mc * (μ * ((A + ℓ) / ((1 - 2 * ρ) * ℓ * μ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN0 hμ0.le) hmc0
      have h3 : mc * (μ * ((A + ℓ) / ((1 - 2 * ρ) * ℓ * μ)))
          = μ * (γ * ((A + ℓ) / ((1 - 2 * ρ) * ℓ))) := by
        rw [hmcdef]; field_simp; try ring
      refine le_of_mul_le_mul_left ?_ hμ0
      rw [h1]
      linarith
    -- assemble
    have hstep : qval mf mc (1 - ρ) ρ
          (fun l => if A ≤ (qState ℓ A l).1.1 then (1 : ℝ) else 0) Q []
        ≤ qval mf mc ρ ρ (fun l => if A ≤ (qState ℓ A l).1.1 then (1 : ℝ) else 0) Q []
          + (1 - 2 * ρ) * qval mf mc ρ ρ (fun l => ((qState ℓ A l).2 : ℝ)) Q [] :=
      by linarith [(abs_le.1 hcoup).1]
    have h4 : (1 - 2 * ρ) * qval mf mc ρ ρ (fun l => ((qState ℓ A l).2 : ℝ)) Q []
        ≤ (1 - 2 * ρ) * (γ * ((A + ℓ) / ((1 - 2 * ρ) * ℓ))) :=
      mul_le_mul_of_nonneg_left hNC (by linarith)
    nlinarith [mul_nonneg hγ0 hT0]
  · -- (iii) type-II error
    rw [show (fun (w : Fin Q → Pop) => (∏ k, α (w k)) *
        val (G.respWith V c.1)
          (Gallery.passiveProbe (fun (w : Fin Q → Pop) (k : ℕ) => arr (extend w k)) w)
          (fun h => 1 - venueDecide (fun a => G.reachC c.1 (arr a)) ℓ A (extend w) h) Q [])
        = fun (w : Fin Q → Pop) => (∏ k, α (w k)) *
        val (G.respWith V c.1)
          (Gallery.passiveProbe (fun (w : Fin Q → Pop) (k : ℕ) => arr (extend w k)) w)
          (fun h => (fun l => 1 - (if A ≤ (pState ℓ A l).1 then (1 : ℝ) else 0))
            (venueObs (fun a => G.reachC c.1 (arr a)) (extend w) h)) Q [] from rfl,
      law1 (fun l => 1 - (if A ≤ (pState ℓ A l).1 then (1 : ℝ) else 0)),
      ← pval_reach_const μ ℓ A (1 - ρ)
        (fun st => 1 - (if A ≤ st.1 then (1 : ℝ) else 0)) Q []]
    exact hII

include hρ0 hρ1 hκq hκl hα1 in
open Classical in
/-- **Off the collision event the reaching arrivals are i.i.d. Bernoulli trials at `c`.**

If no arrival that reaches the candidate also reaches a face of `G₀`, then the venue's record
under `H₀` is an i.i.d. `Bern(ρ)` sequence at reach rate `μ`, and under `H₁` an i.i.d.
`Bern(1−ρ)` sequence at the same reach rate — the model `PassiveUpper.pval` postulates, here
computed from `Gallery.resp`/`Gallery.respWith` and the product prior on arrival tuples. The
reach indicator and the answers are independent of the past because the passive probe rule does
not read the transcript. -/
theorem venue_reaching_iid
    (hnocoll : ∀ a, G.reachC c.1 (arr a) → ¬ G.thr < G.score V (arr a))
    (hμdef : ∑ a ∈ univ.filter (fun a => G.reachC c.1 (arr a)), α a = μ) (Q : ℕ) :
    (∀ F : List Obs → ℝ,
      (∑ w : Fin Q → Pop, (∏ k, α (w k)) *
        val (G.resp V)
          (Gallery.passiveProbe (fun (w : Fin Q → Pop) (k : ℕ) => arr (extend w k)) w)
          (fun h => F (venueObs (fun a => G.reachC c.1 (arr a)) (extend w) h)) Q [])
      = pval (fun _ => μ) (fun _ => ρ) F Q []) ∧
    (∀ F : List Obs → ℝ,
      (∑ w : Fin Q → Pop, (∏ k, α (w k)) *
        val (G.respWith V c.1)
          (Gallery.passiveProbe (fun (w : Fin Q → Pop) (k : ℕ) => arr (extend w k)) w)
          (fun h => F (venueObs (fun a => G.reachC c.1 (arr a)) (extend w) h)) Q [])
      = pval (fun _ => μ) (fun _ => 1 - ρ) F Q []) := by
  classical
  have hmc : ∑ a ∈ univ.filter (fun a => G.reachC c.1 (arr a) ∧ G.thr < G.score V (arr a)), α a
      = 0 := by
    rw [Finset.filter_eq_empty_iff.mpr (fun a _ h => hnocoll a h.1 h.2), Finset.sum_empty]
  have hmf : ∑ a ∈ univ.filter
      (fun a => G.reachC c.1 (arr a) ∧ ¬ G.thr < G.score V (arr a)), α a = μ := by
    rw [← hμdef]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.1, fun h => ⟨h, hnocoll a h⟩⟩
  have hprobe : ∀ w : Fin Q → Pop,
      Gallery.passiveProbe (fun (w : Fin Q → Pop) (k : ℕ) => arr (extend w k)) w
        = fun h => arr (extend w h.length) := fun _ => rfl
  constructor
  · intro F
    simp only [hprobe]
    rw [venue_plain_law (X := Sph E) arr α (G.resp V) (fun a => G.reachC c.1 (arr a))
      (fun a => G.thr < G.score V (arr a)) μ 0 ρ hα1 hmc hmf
      (fun a hRa => hκq _ (not_lt.mp (hnocoll a hRa))) Q F, add_zero]
  · intro F
    simp only [hprobe]
    rw [venue_plain_law (X := Sph E) arr α (G.respWith V c.1) (fun a => G.reachC c.1 (arr a))
      (fun a => G.thr < G.score V (arr a)) μ 0 (1 - ρ) hα1 hmc hmf
      (fun a hRa => (reaching_resp G V c.1 ρ hκq hκl (arr a) hRa).1) Q F, add_zero]

include hρ0 hρ1 hκq hκl hα0 hα1 hμ0 in
open Classical in
/-- **The expected number of arrivals under `H₀`, with collisions.** Corollary 4.2.5 asserts
`E[#arrivals] ≤ (A+ℓ)/(KL_ρ·μ_pop)` when "the target never visits", i.e. under `H₀`. With a
collision rate `γ > 0` the per-arrival drift of the log-likelihood ratio is only
`−KL_ρ·μ(1−2γ)`, since a colliding reaching arrival answers the wrong way, so the correct bound
carries a factor `1/(1−2γ)` and is vacuous at `γ ≥ 1/2`. (At `γ = 0`, and under `H₁` for any `γ`
— see `passive_venue_gallery` — the note's form is exact.) -/
theorem passive_venue_arrivals_H0
    (hmc : ∑ a ∈ univ.filter (fun a => G.reachC c.1 (arr a) ∧ G.thr < G.score V (arr a)), α a
        = γ * μ)
    (hmf : ∑ a ∈ univ.filter (fun a => G.reachC c.1 (arr a) ∧ ¬ G.thr < G.score V (arr a)), α a
        = (1 - γ) * μ)
    (hγ2 : γ < 1 / 2) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (Q : ℕ) :
    (∑ w : Fin Q → Pop, (∏ k, α (w k)) *
        val (G.resp V)
          (Gallery.passiveProbe (fun (w : Fin Q → Pop) (k : ℕ) => arr (extend w k)) w)
          (fun h => ((venueState (fun a => G.reachC c.1 (arr a))
            (Real.log ((1 - ρ) / ρ)) (Real.log (2 / δ)) (extend w) h).2.2 : ℝ)) Q [])
      ≤ (Real.log (2 / δ) + Real.log ((1 - ρ) / ρ)) /
          ((1 - 2 * ρ) * Real.log ((1 - ρ) / ρ) * μ * (1 - 2 * γ)) := by
  classical
  obtain ⟨hmc0, hmf0, hm1⟩ := mass_facts G V c arr α μ γ hα0 hα1 hmc hmf
  have hρ1' : 0 < 1 - ρ := by linarith
  have hratio : 1 < (1 - ρ) / ρ := by rw [lt_div_iff₀ hρ0]; linarith
  set ℓ := Real.log ((1 - ρ) / ρ) with hℓdef
  set A := Real.log (2 / δ) with hAdef
  set mc := γ * μ with hmcdef
  set mf := (1 - γ) * μ with hmfdef
  have hℓ : 0 < ℓ := Real.log_pos hratio
  have hApos : 0 < A := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hρ01 : (0 : ℝ) ≤ ρ ∧ ρ ≤ 1 := ⟨hρ0.le, by linarith⟩
  have hρ01' : (0 : ℝ) ≤ 1 - ρ ∧ (1 : ℝ) - ρ ≤ 1 := ⟨by linarith, by linarith⟩
  have hprobe : ∀ w : Fin Q → Pop,
      Gallery.passiveProbe (fun (w : Fin Q → Pop) (k : ℕ) => arr (extend w k)) w
        = fun h => arr (extend w h.length) := fun _ => rfl
  have hp0c : ∀ a, G.reachC c.1 (arr a) → G.thr < G.score V (arr a) →
      G.resp V (arr a) = 1 - ρ := fun a _ hCa => hκl _ hCa
  have hp0f : ∀ a, G.reachC c.1 (arr a) → ¬ G.thr < G.score V (arr a) →
      G.resp V (arr a) = ρ := fun a _ hCa => hκq _ (not_lt.mp hCa)
  have law0 : ∀ F : List Obs' → ℝ,
      (∑ w : Fin Q → Pop, (∏ k, α (w k)) *
        val (G.resp V) (fun h => arr (extend w h.length))
          (fun h => F ((trace (extend w) 0 h).map
            (obsOf (fun a => G.reachC c.1 (arr a))
              (fun a => G.thr < G.score V (arr a))))) Q [])
      = qval mf mc (1 - ρ) ρ F Q [] := fun F =>
    venue_flag_law (X := Sph E) arr α (G.resp V) (fun a => G.reachC c.1 (arr a))
      (fun a => G.thr < G.score V (arr a)) mf mc (1 - ρ) ρ hα1 hmc hmf hp0c hp0f Q F
  have hleaf : ∀ w : Fin Q → Pop,
      (fun h => ((venueState (fun a => G.reachC c.1 (arr a)) ℓ A (extend w) h).2.2 : ℝ))
      = fun h => ((qState ℓ A ((trace (extend w) 0 h).map
          (obsOf (fun a => G.reachC c.1 (arr a))
            (fun a => G.thr < G.score V (arr a))))).1.2.2 : ℝ) := by
    intro w
    funext h
    unfold venueState venueObs
    rw [qState_fst, qproj_map_obsOf]
  simp only [hprobe, hleaf]
  rw [law0 (fun l => ((qState ℓ A l).1.2.2 : ℝ))]
  set d := ℓ * (mc * (2 * (1 - ρ) - 1) + mf * (2 * ρ - 1)) with hddef
  have hw := qval_drift_wald mf mc (1 - ρ) ρ ℓ A d hddef Q []
  have hlin := qval_lin mf mc (1 - ρ) ρ 1 (-d) (fun l => (qState ℓ A l).1.1)
    (fun l => ((qState ℓ A l).1.2.2 : ℝ)) Q []
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at hlin
  rw [hlin] at hw
  simp only [qState_nil, Nat.cast_zero, mul_zero, sub_zero] at hw
  have hb := qval_lambda_bound hmf0 hmc0 hm1 hρ01' hρ01 hℓ.le hApos (pc := 1 - ρ) (pf := ρ) Q []
  have hdval : d = -((1 - 2 * ρ) * ℓ * μ * (1 - 2 * γ)) := by
    rw [hddef, hmcdef, hmfdef]; ring
  rw [hdval] at hw
  have hKpos : 0 < (1 - 2 * ρ) * ℓ * μ * (1 - 2 * γ) :=
    mul_pos (mul_pos (mul_pos (by linarith) hℓ) hμ0) (by linarith)
  rw [le_div_iff₀ hKpos]
  nlinarith [hb.1, hw]

end GalleryVenue

/-! ## 9. Sanity checks on the model (guards against a mis-specified venue) -/

section Sanity

variable {Pop : Type*} [Fintype Pop] [Inhabited Pop]

/-- The record of a run pairs each arrival with the answer it produced, in order. -/
example (x : ℕ → Pop) (b₀ b₁ : Bool) :
    trace x 0 [b₀, b₁] = [(x 0, b₀), (x 1, b₁)] := rfl

/-- A non-reaching arrival is recorded as `none`: its answer is discarded. -/
example (R C : Pop → Prop) (a : Pop) (b : Bool) (h : ¬ R a) : obsOf R C (a, b) = none := by
  simp [obsOf, h]

/-- A reaching arrival is recorded with its collision flag and its answer. -/
example (R C : Pop → Prop) (a : Pop) (b : Bool) (hR : R a) (hC : C a) :
    obsOf R C (a, b) = some (true, b) := by simp [obsOf, hR, hC]

/-- The test ignores a non-reaching arrival: `Λ` and the reach count `S` do not move, only the
arrival count `N`. -/
example (ℓ A : ℝ) (hA : 0 < A) : qState ℓ A [none] = ((0, 0, 1), 0) := by
  simp [qState, qStep, pStep_none, hA]

/-- A reaching, non-colliding arrival answering `true` moves `Λ` up by `ℓ` and `S` by one; the
collision counter `NC` stays put. -/
example (ℓ A : ℝ) (hA : 0 < A) : qState ℓ A [some (false, true)] = ((ℓ, 1, 1), 0) := by
  simp [qState, qStep, pStep_some, hA]

/-- A reaching, *colliding* arrival answering `false` moves `Λ` down by `ℓ` and increments `NC`. -/
example (ℓ A : ℝ) (hA : 0 < A) : qState ℓ A [some (true, false)] = ((-ℓ, 1, 1), 1) := by
  simp [qState, qStep, pStep_some, hA]

/-- Once `|Λ| ≥ A` the venue has decided: nothing moves, including the collision counter. -/
example (ℓ A : ℝ) (hA : 0 < A) (hℓ : A ≤ ℓ) :
    qState ℓ A [some (false, true), some (true, true)] = ((ℓ, 1, 1), 0) := by
  simp [qState, qStep, pStep_some, hA, abs_of_nonneg (le_trans hA.le hℓ), not_lt.2 hℓ]

/-- One round of the venue's law: draw the arrival, then the oracle answers. -/
example {X : Type*} (α : Pop → ℝ) (arr : Pop → X) (p : X → ℝ) (F : List (Pop × Bool) → ℝ) :
    vval α arr p F 1 [] =
      ∑ a, α a * (p (arr a) * F [(a, true)] + (1 - p (arr a)) * F [(a, false)]) := rfl

end Sanity

end OracleBounds.Attacks
