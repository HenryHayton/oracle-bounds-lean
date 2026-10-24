import OracleBounds.V6.Process
import OracleBounds.V6.Information

/-!
# Theorem 5.1 inside the process model (information bound with switching reference)

This connects the adaptive process of `OracleBounds.V6.Process` to mutual information.

* `pathProb p probe r h e` is the probability of the next `r` answer bits being `e` from history `h`
  (a pmf on `Fin r → Bool`), and `val_eq_sum` shows `val` is the expectation under it.
* `klRounds` accumulates per-round Bernoulli KL along the transcript; `kl_chain` proves that the KL
  divergence between two transcript laws equals it (the divergence decomposition for adaptive
  sampling; Kaufmann–Cappé–Garivier Lemma 1 / N1 Lemma 4.2 with a fixed reference process).
* **Thm 5.1 (band-null).** Hidden parameter `θ` with prior `π`; for each `θ` the answer probability
  `pθ x`. If on *quiet* probes every `pθ` equals a common `p₀` (band-null: probe outside every face's
  reach), then `I(θ; transcript) ≤ β*·E[#non-quiet probes]`, with `β* = log 2`, or `Cap(ρ)` when all
  answer probabilities lie in `[ρ, 1−ρ]`.

**Proof route differs from v6/v7.** Instead of switching between `ν₀` and the *predictive*
reference (which is what forced v7's Lemma 4.2′), we use the fixed reference process that answers
with `p₀` on quiet probes and with probability `1/2` on the others. Then
`I ≤ Σ π KL(Pθ ‖ R)` (golden formula) and every non-quiet round costs `KL(Bern p ‖ Bern ½) = log 2 − h(p)`,
which is `≤ log 2` always and `≤ Cap(ρ)` for `p ∈ [ρ, 1−ρ]`.
-/

namespace OracleBounds.V6

open Finset

variable {X : Type*}

/-- Probability of answer bit `b` when bit 1 has probability `q`. -/
def bern (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

lemma bern_mem {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) (b : Bool) : 0 ≤ bern q b ∧ bern q b ≤ 1 := by
  cases b <;> simp [bern] <;> constructor <;> linarith [hq.1, hq.2]

/-- Probability of the next `r` bits being `e`, started from history `h`. -/
noncomputable def pathProb (p : X → ℝ) (probe : List Bool → X) :
    (r : ℕ) → List Bool → (Fin r → Bool) → ℝ
  | 0, _, _ => 1
  | r + 1, h, e => bern (p (probe h)) (e 0) * pathProb p probe r (h ++ [e 0]) (Fin.tail e)

lemma sum_fin_succ_bool {r : ℕ} (G : (Fin (r + 1) → Bool) → ℝ) :
    ∑ e, G e = ∑ e' : Fin r → Bool, G (Fin.cons true e') + ∑ e' : Fin r → Bool, G (Fin.cons false e') := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  rfl

section pathProb

variable (p : X → ℝ) (probe : List Bool → X)

/-- `val` is the expectation under `pathProb`. -/
theorem val_eq_sum (F : List Bool → ℝ) :
    ∀ r h, val p probe F r h = ∑ e, pathProb p probe r h e * F (h ++ List.ofFn e) := by
  intro r
  induction r with
  | zero => intro h; simp [pathProb]
  | succ r ih =>
    intro h
    rw [sum_fin_succ_bool, val_succ, ih, ih]
    simp only [pathProb, Fin.cons_zero, Fin.tail_cons, bern, if_true, Bool.false_eq_true, if_false,
      List.ofFn_succ, Fin.cons_succ, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun e _ => ?_ <;> simp [mul_assoc]

variable {p}

lemma pathProb_nonneg (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    ∀ r h e, 0 ≤ pathProb p probe r h e := by
  intro r
  induction r with
  | zero => intro h e; simp [pathProb]
  | succ r ih => intro h e; exact mul_nonneg (bern_mem (hp _) _).1 (ih _ _)

lemma pathProb_sum (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) (r : ℕ) (h : List Bool) :
    ∑ e, pathProb p probe r h e = 1 := by
  have := val_eq_sum p probe (fun _ => 1) r h
  simpa [val_const] using this.symm

end pathProb

/-- KL divergence of finite pmfs, `Σ P log(P/R)` (with Lean's `log 0 = 0`; used only under
absolute continuity `R = 0 → P = 0`). -/
noncomputable def klPmf {ι : Type*} [Fintype ι] (P R : ι → ℝ) : ℝ := ∑ i, P i * Real.log (P i / R i)

/-- Bernoulli KL, `KL(Bern a ‖ Bern c)`. -/
noncomputable def bkl (a c : ℝ) : ℝ := ∑ b, bern a b * Real.log (bern a b / bern c b)

/-- Per-round KL accumulated along the transcript of the `p`-process. -/
noncomputable def klRounds (p q : X → ℝ) (probe : List Bool → X) : ℕ → List Bool → ℝ
  | 0, _ => 0
  | r + 1, h => bkl (p (probe h)) (q (probe h)) +
      p (probe h) * klRounds p q probe r (h ++ [true]) +
      (1 - p (probe h)) * klRounds p q probe r (h ++ [false])

section chain

variable {p q : X → ℝ} {probe : List Bool → X}

lemma pathProb_ac (hac : ∀ x b, bern (q x) b = 0 → bern (p x) b = 0) :
    ∀ r h e, pathProb q probe r h e = 0 → pathProb p probe r h e = 0 := by
  intro r
  induction r with
  | zero => intro h e; simp [pathProb]
  | succ r ih =>
    intro h e he
    simp only [pathProb] at he ⊢
    rcases mul_eq_zero.1 he with h1 | h1
    · rw [hac _ _ h1, zero_mul]
    · rw [ih _ _ h1, mul_zero]

/-- **Divergence decomposition** for adaptive processes with a common probe rule. -/
theorem kl_chain (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1)
    (hac : ∀ x b, bern (q x) b = 0 → bern (p x) b = 0) :
    ∀ r h, klPmf (pathProb p probe r h) (pathProb q probe r h) = klRounds p q probe r h := by
  intro r
  induction r with
  | zero => intro h; simp [klPmf, pathProb, klRounds]
  | succ r ih =>
    intro h
    unfold klPmf
    rw [sum_fin_succ_bool]
    -- pointwise splitting of the log
    have key : ∀ (b : Bool) (e' : Fin r → Bool),
        pathProb p probe (r + 1) h (Fin.cons b e') *
          Real.log (pathProb p probe (r + 1) h (Fin.cons b e') / pathProb q probe (r + 1) h (Fin.cons b e'))
        = pathProb p probe r (h ++ [b]) e' *
            (bern (p (probe h)) b * Real.log (bern (p (probe h)) b / bern (q (probe h)) b))
          + bern (p (probe h)) b * (pathProb p probe r (h ++ [b]) e' *
            Real.log (pathProb p probe r (h ++ [b]) e' / pathProb q probe r (h ++ [b]) e')) := by
      intro b e'
      simp only [pathProb, Fin.cons_zero, Fin.tail_cons]
      set a := bern (p (probe h)) b
      set c := bern (q (probe h)) b
      set P' := pathProb p probe r (h ++ [b]) e'
      set R' := pathProb q probe r (h ++ [b]) e'
      have ha : 0 ≤ a := (bern_mem (hp _) b).1
      have hP' : 0 ≤ P' := pathProb_nonneg probe hp _ _ _
      rcases eq_or_lt_of_le ha with ha0 | ha0
      · rw [← ha0]; simp
      rcases eq_or_lt_of_le hP' with hP0 | hP0
      · rw [← hP0]; simp
      have hc : c ≠ 0 := fun h0 => ha0.ne' (hac _ _ h0)
      have hR : R' ≠ 0 := fun h0 => hP0.ne' (pathProb_ac hac _ _ _ h0)
      rw [mul_div_mul_comm, Real.log_mul (div_ne_zero ha0.ne' hc) (div_ne_zero hP0.ne' hR)]
      ring
    simp only [key, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      pathProb_sum probe hp]
    have e1 := ih (h ++ [true])
    have e2 := ih (h ++ [false])
    unfold klPmf at e1 e2
    rw [e1, e2, klRounds, bkl, Fintype.sum_bool]
    simp only [bern, if_true, Bool.false_eq_true, if_false]
    ring

end chain

/-! ### Per-round costs -/

lemma bkl_self (a : ℝ) : bkl a a = 0 := by
  unfold bkl
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases h : bern a b = 0
  · simp [h]
  · rw [div_self h, Real.log_one, mul_zero]

/-- `KL(Bern a ‖ Bern ½) = log 2 − h(a)`. -/
lemma bkl_half {a : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) : bkl a (1 / 2) = Real.log 2 - Real.binEntropy a := by
  unfold bkl
  rw [Fintype.sum_bool]
  simp only [bern, if_true, Bool.false_eq_true, if_false]
  have t : ∀ y : ℝ, 0 ≤ y → y * Real.log (y / (1 / 2)) = y * Real.log 2 - y * Real.log y⁻¹ := by
    intro y hy
    rcases eq_or_lt_of_le hy with h0 | h0
    · rw [← h0]; simp
    · rw [Real.log_inv, div_div_eq_mul_div, div_one, mul_comm y 2,
        Real.log_mul (by norm_num) h0.ne']; ring
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, t a ha.1, t (1 - a) (by linarith [ha.2])]
  unfold Real.binEntropy
  ring

lemma bkl_half_le_log_two {a : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) : bkl a (1 / 2) ≤ Real.log 2 := by
  rw [bkl_half ha]; linarith [Real.binEntropy_nonneg ha.1 ha.2]

/-- For `a ∈ [ρ, 1−ρ]`: `KL(Bern a ‖ Bern ½) ≤ Cap(ρ) = log 2 − h(ρ)` (N1 Lemma 3.2's constant). -/
lemma bkl_half_le_cap {a ρ : ℝ} (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 1 / 2) (ha : ρ ≤ a ∧ a ≤ 1 - ρ) :
    bkl a (1 / 2) ≤ Real.log 2 - Real.binEntropy ρ := by
  rw [bkl_half ⟨by linarith [ha.1], by linarith [ha.2]⟩]
  have hc := Real.strictConcave_binEntropy.concaveOn.min_le_of_mem_Icc
    (x := ρ) (y := 1 - ρ) (z := a) ⟨hρ, by linarith⟩ ⟨by linarith, by linarith⟩ ha
  rw [Real.binEntropy_one_sub, min_self] at hc
  linarith

/-! ### Counting non-quiet rounds -/

/-- Expected number of rounds, over the next `r`, whose probe satisfies `act`. -/
noncomputable def accCount (p : X → ℝ) (probe : List Bool → X) (act : X → Prop) [DecidablePred act] :
    ℕ → List Bool → ℝ
  | 0, _ => 0
  | r + 1, h => (if act (probe h) then 1 else 0) + p (probe h) * accCount p probe act r (h ++ [true]) +
      (1 - p (probe h)) * accCount p probe act r (h ++ [false])

lemma klRounds_le {p q : X → ℝ} {probe : List Bool → X} (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (act : X → Prop) [DecidablePred act] (β : ℝ)
    (hcost : ∀ x, bkl (p x) (q x) ≤ β * (if act x then 1 else 0)) :
    ∀ r h, klRounds p q probe r h ≤ β * accCount p probe act r h := by
  intro r
  induction r with
  | zero => intro h; simp [klRounds, accCount]
  | succ r ih =>
    intro h
    simp only [klRounds, accCount]
    have h1 := ih (h ++ [true])
    have h2 := ih (h ++ [false])
    have hc := hcost (probe h)
    have hp0 := (hp (probe h)).1
    have hp1 : 0 ≤ 1 - p (probe h) := by linarith [(hp (probe h)).2]
    nlinarith [mul_le_mul_of_nonneg_left h1 hp0, mul_le_mul_of_nonneg_left h2 hp1]

/-- `val` congruence for leaf functions that agree on extensions of `h`. -/
lemma val_congr_prefix (p : X → ℝ) (probe : List Bool → X) {F G : List Bool → ℝ} :
    ∀ r h, (∀ h', h <+: h' → h'.length = h.length + r → F h' = G h') →
      val p probe F r h = val p probe G r h := by
  intro r
  induction r with
  | zero => intro h hFG; exact hFG h (List.prefix_refl h) (by simp)
  | succ r ih =>
    intro h hFG
    simp only [val_succ]
    rw [ih (h ++ [true]) (fun h' hpre hl =>
        hFG h' ((List.prefix_append h [true]).trans hpre) (by simp at hl; omega)),
      ih (h ++ [false]) (fun h' hpre hl =>
        hFG h' ((List.prefix_append h [false]).trans hpre) (by simp at hl; omega))]

/-- `accCount` is the expectation of the pathwise count of `act`-probes. -/
theorem accCount_eq_val (p : X → ℝ) (probe : List Bool → X) (act : X → Prop) [DecidablePred act] :
    ∀ r h, accCount p probe act r h = val p probe (fun h' =>
      ∑ k ∈ Finset.Ico h.length (h.length + r), if act (probe (h'.take k)) then 1 else 0) r h := by
  intro r
  induction r with
  | zero => intro h; simp [accCount]
  | succ r ih =>
    intro h
    simp only [accCount, val_succ, ih]
    have hstep : ∀ b : Bool,
        val p probe (fun h' => ∑ k ∈ Finset.Ico (h ++ [b]).length ((h ++ [b]).length + r),
          if act (probe (h'.take k)) then (1 : ℝ) else 0) r (h ++ [b]) + (if act (probe h) then 1 else 0)
        = val p probe (fun h' => ∑ k ∈ Finset.Ico h.length (h.length + (r + 1)),
          if act (probe (h'.take k)) then (1 : ℝ) else 0) r (h ++ [b]) := by
      intro b
      rw [add_comm, ← val_const p probe (if act (probe h) then (1 : ℝ) else 0) r (h ++ [b]),
        ← val_add]
      apply val_congr_prefix
      intro h' hpre _
      have htake : h'.take h.length = h := by
        have := (List.prefix_append h [b]).trans hpre
        exact (List.prefix_iff_eq_take.mp this).symm
      rw [Finset.sum_eq_sum_Ico_succ_bot (show h.length < h.length + (r + 1) by omega), htake]
      simp only [List.length_append, List.length_singleton]
      rw [show h.length + (r + 1) = h.length + 1 + r by omega]
    have e1 := hstep true
    have e2 := hstep false
    linear_combination (p (probe h)) * e1 + (1 - p (probe h)) * e2

/-! ### Golden formula (proved) and Theorem 5.1 -/

/-- **Golden formula.** `I(θ; Y) ≤ Σ_θ π(θ) KL(P_θ ‖ R)` for any reference pmf `R` dominating
every `P_θ`. -/
theorem mutualInfo_le_avg_kl {Θ ι : Type*} [Fintype Θ] [Fintype ι] (π : Θ → ℝ) (P : Θ → ι → ℝ)
    (R : ι → ℝ) (hπ : ∀ θ, 0 ≤ π θ) (hπ1 : ∑ θ, π θ = 1) (hP : ∀ θ i, 0 ≤ P θ i)
    (hP1 : ∀ θ, ∑ i, P θ i = 1) (hR : ∀ i, 0 ≤ R i) (hR1 : ∑ i, R i = 1)
    (hac : ∀ θ i, R i = 0 → P θ i = 0) :
    Info.mutualInfo (fun ti : Θ × ι => π ti.1 * P ti.1 ti.2) ≤ ∑ θ, π θ * klPmf (P θ) R := by
  set Pb : ι → ℝ := fun i => ∑ θ, π θ * P θ i with hPb
  have hm1 : ∀ θ, Info.marg₁ (fun ti : Θ × ι => π ti.1 * P ti.1 ti.2) θ = π θ := by
    intro θ; simp [Info.marg₁, ← Finset.mul_sum, hP1]
  have hm2 : ∀ i, Info.marg₂ (fun ti : Θ × ι => π ti.1 * P ti.1 ti.2) i = Pb i := fun i => rfl
  -- pointwise identity
  have hpt : ∀ θ i, π θ * (P θ i * Real.log (P θ i / R i)) -
      π θ * P θ i * Real.log (π θ * P θ i / (π θ * Pb i)) = π θ * P θ i * Real.log (Pb i / R i) := by
    intro θ i
    rcases eq_or_lt_of_le (hπ θ) with h0 | h0
    · rw [← h0]; simp
    rcases eq_or_lt_of_le (hP θ i) with h1 | h1
    · rw [← h1]; simp
    have hRi : 0 < R i := lt_of_le_of_ne (hR i) (fun h => h1.ne' (hac θ i h.symm))
    have hPbi : 0 < Pb i := by
      have : π θ * P θ i ≤ Pb i := Finset.single_le_sum (f := fun θ => π θ * P θ i)
        (fun θ _ => mul_nonneg (hπ θ) (hP θ i)) (Finset.mem_univ θ)
      have := mul_pos h0 h1; linarith
    rw [mul_div_mul_left _ _ h0.ne', Real.log_div h1.ne' hRi.ne', Real.log_div h1.ne' hPbi.ne',
      Real.log_div hPbi.ne' hRi.ne']
    ring
  have hgibbs : 0 ≤ klPmf Pb R := by
    have hpt2 : ∀ i, Pb i - R i ≤ Pb i * Real.log (Pb i / R i) := fun i =>
      Info.mul_log_div_ge_sub (show 0 ≤ Pb i from Finset.sum_nonneg fun θ _ => mul_nonneg (hπ θ) (hP θ i))
        (hR i) (fun h0 => show Pb i = 0 from Finset.sum_eq_zero fun θ _ => by rw [hac θ i h0, mul_zero])
    have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt2 i
    have hPb1 : ∑ i, Pb i = 1 := by
      simp only [hPb]; rw [Finset.sum_comm]; simp [← Finset.mul_sum, hP1, hπ1]
    rw [Finset.sum_sub_distrib, hPb1, hR1, sub_self] at h
    exact h
  have hsplit : ∑ θ, π θ * klPmf (P θ) R - Info.mutualInfo (fun ti : Θ × ι => π ti.1 * P ti.1 ti.2)
      = klPmf Pb R := by
    unfold Info.mutualInfo klPmf
    simp only [hm1, hm2, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [hpt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul]
  linarith

open Classical in
/-- **Theorem 5.1 (band-null), in the process model.** Fix the attacker's randomness and the caps `W`
(so the rule `probe` and the set of *quiet* probes are fixed). The hidden parameter `θ` (the fine
indices `V⁽¹ᐟⁿ⁾`) has prior `π`; `p θ x` is the probability of answer 1 to probe `x`. If on quiet
probes the answer law does not depend on `θ` (`p θ x = p₀ x`), and every non-quiet round satisfies
`KL(Bern(p θ x) ‖ Bern ½) ≤ β`, then
`I(θ; b₁..b_Q) ≤ β · Σ_θ π(θ) E_θ[#{k ≤ Q : probe k is not quiet}]`. -/
theorem thm51_process {Θ : Type*} [Fintype Θ] (π : Θ → ℝ) (hπ : ∀ θ, 0 ≤ π θ)
    (hπ1 : ∑ θ, π θ = 1) (p : Θ → X → ℝ) (hp : ∀ θ x, 0 ≤ p θ x ∧ p θ x ≤ 1)
    (probe : List Bool → X) (quiet : X → Prop) (p₀ : X → ℝ) (hp₀ : ∀ x, 0 ≤ p₀ x ∧ p₀ x ≤ 1)
    (hquiet : ∀ θ x, quiet x → p θ x = p₀ x) (β : ℝ)
    (hβ : ∀ θ x, ¬ quiet x → bkl (p θ x) (1 / 2) ≤ β) (Q : ℕ) :
    Info.mutualInfo (fun te : Θ × (Fin Q → Bool) => π te.1 * pathProb (p te.1) probe Q [] te.2)
      ≤ β * ∑ θ, π θ * val (p θ) probe
          (fun h => ∑ k ∈ Finset.range Q, if ¬ quiet (probe (h.take k)) then 1 else 0) Q [] := by
  set q : X → ℝ := fun x => if quiet x then p₀ x else 1 / 2 with hqdef
  have hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1 := by
    intro x; simp only [hqdef]; split_ifs
    · exact hp₀ x
    · norm_num
  have hac : ∀ θ x b, bern (q x) b = 0 → bern (p θ x) b = 0 := by
    intro θ x b h0
    by_cases hx : quiet x
    · simp only [hqdef, if_pos hx] at h0; rwa [hquiet θ x hx]
    · simp only [hqdef, if_neg hx] at h0; cases b <;> simp [bern] at h0 <;> norm_num at h0
  have hgold := mutualInfo_le_avg_kl π (fun θ => pathProb (p θ) probe Q []) (pathProb q probe Q [])
    hπ hπ1 (fun θ => pathProb_nonneg probe (hp θ) Q []) (fun θ => pathProb_sum probe (hp θ) Q [])
    (pathProb_nonneg probe hq Q []) (pathProb_sum probe hq Q [])
    (fun θ e h0 => pathProb_ac (hac θ) Q [] e h0)
  refine hgold.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun θ _ => ?_
  rw [kl_chain (hp θ) hq (hac θ)]
  have hcost : ∀ x, bkl (p θ x) (q x) ≤ β * (if ¬ quiet x then 1 else 0) := by
    intro x
    by_cases hx : quiet x
    · rw [if_neg (not_not.2 hx), mul_zero,
        show q x = p θ x by simp [hqdef, hx, hquiet θ x hx], bkl_self]
    · rw [if_pos hx, mul_one, show q x = 1 / 2 by simp [hqdef, hx]]; exact hβ θ x hx
  have hk := klRounds_le (probe := probe) (hp θ) (fun x => ¬ quiet x) β hcost Q []
  rw [accCount_eq_val] at hk
  simp only [List.length_nil, zero_add, ← Finset.range_eq_Ico] at hk
  calc π θ * klRounds (p θ) q probe Q [] ≤ π θ * (β * val (p θ) probe
        (fun h => ∑ k ∈ Finset.range Q, if ¬ quiet (probe (h.take k)) then 1 else 0) Q []) :=
        mul_le_mul_of_nonneg_left hk (hπ θ)
    _ = _ := by ring

open Classical in
/-- Thm 5.1 with `β* = log 2` (any band-null kernel, including deterministic ones). -/
theorem thm51_log_two {Θ : Type*} [Fintype Θ] (π : Θ → ℝ) (hπ : ∀ θ, 0 ≤ π θ)
    (hπ1 : ∑ θ, π θ = 1) (p : Θ → X → ℝ) (hp : ∀ θ x, 0 ≤ p θ x ∧ p θ x ≤ 1)
    (probe : List Bool → X) (quiet : X → Prop) (p₀ : X → ℝ) (hp₀ : ∀ x, 0 ≤ p₀ x ∧ p₀ x ≤ 1)
    (hquiet : ∀ θ x, quiet x → p θ x = p₀ x) (Q : ℕ) :
    Info.mutualInfo (fun te : Θ × (Fin Q → Bool) => π te.1 * pathProb (p te.1) probe Q [] te.2)
      ≤ Real.log 2 * ∑ θ, π θ * val (p θ) probe
          (fun h => ∑ k ∈ Finset.range Q, if ¬ quiet (probe (h.take k)) then 1 else 0) Q [] :=
  thm51_process π hπ hπ1 p hp probe quiet p₀ hp₀ hquiet _
    (fun θ x _ => bkl_half_le_log_two (hp θ x)) Q

open Classical in
/-- Thm 5.1 with `β* = Cap(ρ) = log 2 − h(ρ)` when every answer probability lies in `[ρ, 1−ρ]`
(Model A). -/
theorem thm51_cap {Θ : Type*} [Fintype Θ] (π : Θ → ℝ) (hπ : ∀ θ, 0 ≤ π θ)
    (hπ1 : ∑ θ, π θ = 1) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 1 / 2) (p : Θ → X → ℝ)
    (hp : ∀ θ x, ρ ≤ p θ x ∧ p θ x ≤ 1 - ρ)
    (probe : List Bool → X) (quiet : X → Prop) (p₀ : X → ℝ) (hp₀ : ∀ x, 0 ≤ p₀ x ∧ p₀ x ≤ 1)
    (hquiet : ∀ θ x, quiet x → p θ x = p₀ x) (Q : ℕ) :
    Info.mutualInfo (fun te : Θ × (Fin Q → Bool) => π te.1 * pathProb (p te.1) probe Q [] te.2)
      ≤ (Real.log 2 - Real.binEntropy ρ) * ∑ θ, π θ * val (p θ) probe
          (fun h => ∑ k ∈ Finset.range Q, if ¬ quiet (probe (h.take k)) then 1 else 0) Q [] :=
  thm51_process π hπ hπ1 p (fun θ x => ⟨by linarith [(hp θ x).1], by linarith [(hp θ x).2]⟩)
    probe quiet p₀ hp₀ hquiet _ (fun θ x _ => bkl_half_le_cap hρ hρ2 (hp θ x)) Q

end OracleBounds.V6
