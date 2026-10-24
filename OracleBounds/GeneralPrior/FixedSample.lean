import OracleBounds.GeneralPrior.BudgetBest

/-!
# Fixed-sample membership tests (upper-bounds note, Theorems 2.1–2.2)

The attacker probes the candidate `c` `N` times and answers "member" iff more than half the bits
are `1`. Against the symmetric-flip kernel (`κ = ρ` at or below `thr`, `1 − ρ` above):

* `fixed_sample` — for a fixed rest of the list `V`: `δII ≤ (2√(ρ(1−ρ)))^N = e^{−N·C_ch(ρ)}`, and
  `δI ≤ e^{−N·C_ch(ρ)}` when no listed face collides with `c`;
* `collision_le` — the collision probability under the product prior is `≤ n·μ₁`;
* `fixed_sample_avg` — **Thm 2.2**: averaged over `G₀ ∼ ∏πᵢ`,
  `δI + δII ≤ 2·e^{−N·C_ch(ρ)} + n·μ₁`;
* `one_probe_avg` — **Thm 2.1** (noiseless kernel): one probe, `δII = 0`, `δI ≤ n·μ₁`.

`C_ch(ρ) = ½·log(1/(4ρ(1−ρ)))` (the Chernoff information of `Bern ρ` vs `Bern(1−ρ)`); the proof
is the exponential-moment (Chernoff) bound, done by induction on the process.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

/-! ### Exponential moments of the bit counts under a constant response probability -/

section Moments

variable {X : Type*}

/-- Under a constant response probability `pc`, `E[λ^{#b₀}] = λ^{#b₀ so far}·(q λ + 1 − q)^r`,
`q = P[bit = b₀]`. -/
lemma val_pow_count (p : X → ℝ) (probe : List Bool → X) (pc : ℝ)
    (hpc : ∀ h, p (probe h) = pc) (b₀ : Bool) (lam : ℝ) :
    ∀ r h, val p probe (fun h' => lam ^ (h'.count b₀)) r h =
      lam ^ (h.count b₀) * (bern pc b₀ * lam + (1 - bern pc b₀)) ^ r := by
  intro r
  induction r with
  | zero => intro h; simp
  | succ r ih =>
    intro h
    rw [val_succ, ih, ih, hpc]
    cases b₀ <;> simp [List.count_append, bern, pow_succ] <;> ring

/-- Markov/Chernoff: for `μ ≥ 1`, `[#b₀ ≥ N/2] ≤ (μ²)^{#b₀} / μ^N`. -/
lemma ind_le_moment {μ : ℝ} (hμ : 1 ≤ μ) (N k : ℕ) :
    (if (N : ℝ) / 2 ≤ k then (1 : ℝ) else 0) ≤ (μ ^ 2) ^ k / μ ^ N := by
  have hμ0 : 0 < μ := by linarith
  split_ifs with h
  · rw [le_div_iff₀ (by positivity), one_mul, ← pow_mul]
    exact pow_le_pow_right₀ hμ (by
      have : (N : ℝ) ≤ 2 * k := by linarith
      exact_mod_cast (by exact_mod_cast this : N ≤ 2 * k) |>.trans (le_of_eq (by ring)))
  · positivity

end Moments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι]

/-- The fixed-sample decision: "member" iff more than `N/2` of the bits are `1`. -/
noncomputable def majority (N : ℕ) (h : List Bool) : ℝ :=
  if (N : ℝ) / 2 < h.count true then 1 else 0

/-- The Chernoff bound for `N` bits of a `ρ`-coin: `(2√(ρ(1−ρ)))^N`. -/
lemma chernoff_half (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (N : ℕ) (pc : ℝ) (b₀ : Bool)
    (hq : bern pc b₀ = ρ) {X : Type*} (p : X → ℝ) (probe : List Bool → X)
    (hpc : ∀ h, p (probe h) = pc) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    val p probe (fun h => if (N : ℝ) / 2 ≤ h.count b₀ then (1 : ℝ) else 0) N [] ≤
      (2 * Real.sqrt (ρ * (1 - ρ))) ^ N := by
  set μ := Real.sqrt ((1 - ρ) / ρ) with hμdef
  have hr : 1 ≤ (1 - ρ) / ρ := by rw [le_div_iff₀ hρ0]; linarith
  have hμ : 1 ≤ μ := by rw [hμdef]; exact Real.one_le_sqrt.2 hr
  have hμ2 : μ ^ 2 = (1 - ρ) / ρ := Real.sq_sqrt (by linarith)
  have hmono := val_mono probe hp (F := fun h => if (N : ℝ) / 2 ≤ h.count b₀ then (1 : ℝ) else 0)
    (G := fun h => (μ ^ 2) ^ (h.count b₀) / μ ^ N) N [] (fun h' _ => ind_le_moment hμ N _)
  refine hmono.trans (le_of_eq ?_)
  have hdiv : ∀ h' : List Bool, (μ ^ 2) ^ (h'.count b₀) / μ ^ N =
      (μ ^ N)⁻¹ * (μ ^ 2) ^ (h'.count b₀) := fun h' => by ring
  simp only [hdiv]
  have ha := val_affine p probe 0 (μ ^ N)⁻¹ (fun h' => (μ ^ 2) ^ (h'.count b₀)) N []
  simp only [zero_add] at ha
  rw [ha, val_pow_count p probe pc hpc b₀ (μ ^ 2) N [], hq, hμ2]
  simp only [List.count_nil, pow_zero, one_mul]
  have hk : ρ * ((1 - ρ) / ρ) + (1 - ρ) = 2 * (1 - ρ) := by field_simp; ring
  rw [hk, ← inv_pow, ← mul_pow]
  congr 1
  have hs : Real.sqrt (ρ * (1 - ρ)) = (1 - ρ) * Real.sqrt (ρ / (1 - ρ)) := by
    rw [show ρ * (1 - ρ) = (1 - ρ) ^ 2 * (ρ / (1 - ρ)) by field_simp,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  rw [hs, hμdef, ← Real.sqrt_inv, inv_div]
  ring

lemma count_true_add_false (h : List Bool) : h.count true + h.count false = h.length := by
  induction h with
  | nil => simp
  | cons b t ih => cases b <;> simp <;> omega

/-- **Fixed-sample membership test, fixed `G₀ = V`.** -/
theorem fixed_sample (V : ι → Fine) (c : Sph E) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hthr1 : G.thr < 1) (hκq : ∀ s ≤ G.thr, G.κ s = ρ) (hκl : ∀ s, G.thr < s → G.κ s = 1 - ρ)
    (N : ℕ) :
    (G.score V c ≤ G.thr →
      val (G.resp V) (fun _ => c) (majority N) N [] ≤ (2 * Real.sqrt (ρ * (1 - ρ))) ^ N) ∧
    val (G.respWith V c.1) (fun _ => c) (fun h => 1 - majority N h) N [] ≤
      (2 * Real.sqrt (ρ * (1 - ρ))) ^ N := by
  have hcc : inner ℝ c.1 c.1 = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, c.2]; norm_num
  have hs1 := (G.score_mem V c).2
  constructor
  · intro hq
    have hpc : G.resp V c = ρ := hκq _ hq
    refine le_trans (val_mono (fun _ => c) (fun x => G.hκ _) N [] fun h _ => ?_)
      (chernoff_half ρ hρ0 hρ1 N ρ true (by simp [bern]) (G.resp V) (fun _ => c)
        (fun _ => hpc) (fun x => G.hκ _))
    unfold majority
    by_cases h1 : (N : ℝ) / 2 < h.count true
    · rw [if_pos h1, if_pos h1.le]
    · rw [if_neg h1]; split_ifs <;> norm_num
  · have hpc : G.respWith V c.1 c = 1 - ρ := by
      unfold respWith; rw [hcc, max_eq_right hs1]; exact hκl 1 hthr1
    refine le_trans (val_mono (fun _ => c) (fun x => G.hκ _) N [] fun h hl => ?_)
      (chernoff_half ρ hρ0 hρ1 N (1 - ρ) false (by simp [bern]) (G.respWith V c.1) (fun _ => c)
        (fun _ => hpc) (fun x => G.hκ _))
    simp only [List.length_nil, zero_add] at hl
    have hsum : (h.count true : ℝ) + h.count false = N := by
      have := count_true_add_false h
      rw [hl] at this; exact_mod_cast this
    unfold majority
    by_cases h1 : (N : ℝ) / 2 < h.count true
    · rw [if_pos h1, sub_self]; split_ifs <;> norm_num
    · rw [if_neg h1, if_pos (by push Not at h1; linarith)]; norm_num

open Classical in
/-- **Collision probability** under the product prior: `P[some listed face reaches c] ≤ n·μ₁`. -/
lemma collision_le (c : Sph E) (μ₁ : ℝ)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁) :
    ∑ V, G.prior V * (if G.thr < G.score V c then (1 : ℝ) else 0) ≤ Fintype.card ι * μ₁ := by
  have hind : ∀ V : ι → Fine, (if G.thr < G.score V c then (1 : ℝ) else 0) ≤
      ∑ i, if G.reachG (V i) c then (1 : ℝ) else 0 := by
    intro V
    split_ifs with h
    · unfold score at h
      obtain ⟨j, -, hj⟩ := (Finset.lt_sup'_iff _).1 h
      exact le_trans (by simp [reachG, hj])
        (Finset.single_le_sum (f := fun i => if G.reachG (V i) c then (1 : ℝ) else 0)
          (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ j))
    · exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hmarg : ∀ i, ∑ V : ι → Fine, G.prior V * (if G.reachG (V i) c then (1 : ℝ) else 0) =
      ∑ l ∈ Finset.univ.filter (G.reachG · c), G.π i l := by
    intro i
    have hfib : ∀ V : ι → Fine, G.prior V * (if G.reachG (V i) c then (1 : ℝ) else 0) =
        ∑ l, (if G.reachG l c then (1 : ℝ) else 0) * (if V i = l then G.prior V else 0) := by
      intro V
      rw [Finset.sum_eq_single (V i)]
      · simp [mul_comm]
      · intro l _ hl; simp [Ne.symm hl]
      · simp
    rw [Finset.sum_congr rfl fun V _ => hfib V, Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_sum]
    have := prodPrior_marg G.π G.hπ1 i l
    unfold prior
    split_ifs <;> simp [this]
  calc ∑ V, G.prior V * (if G.thr < G.score V c then (1 : ℝ) else 0)
      ≤ ∑ V, G.prior V * ∑ i, (if G.reachG (V i) c then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun V _ => mul_le_mul_of_nonneg_left (hind V) (G.prior_nonneg V)
    _ = ∑ i, ∑ V, G.prior V * (if G.reachG (V i) c then (1 : ℝ) else 0) := by
        simp only [Finset.mul_sum]; exact Finset.sum_comm
    _ ≤ ∑ _i : ι, μ₁ := Finset.sum_le_sum fun i _ => by rw [hmarg i]; exact hcov i c
    _ = _ := by simp

open Classical in
/-- **Theorem 2.2 (fixed-sample membership), averaged over `G₀`.**
`δI + δII ≤ 2·(2√(ρ(1−ρ)))^N + n·μ₁`. -/
theorem fixed_sample_avg (c : Sph E) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hthr1 : G.thr < 1) (hκq : ∀ s ≤ G.thr, G.κ s = ρ) (hκl : ∀ s, G.thr < s → G.κ s = 1 - ρ)
    (μ₁ : ℝ) (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁) (N : ℕ) :
    ∑ V, G.prior V * (val (G.resp V) (fun _ => c) (majority N) N [] +
      val (G.respWith V c.1) (fun _ => c) (fun h => 1 - majority N h) N []) ≤
      2 * (2 * Real.sqrt (ρ * (1 - ρ))) ^ N + Fintype.card ι * μ₁ := by
  set B := (2 * Real.sqrt (ρ * (1 - ρ))) ^ N
  have hB0 : 0 ≤ B := by positivity
  have hper : ∀ V, val (G.resp V) (fun _ => c) (majority N) N [] +
      val (G.respWith V c.1) (fun _ => c) (fun h => 1 - majority N h) N [] ≤
      2 * B + (if G.thr < G.score V c then (1 : ℝ) else 0) := by
    intro V
    obtain ⟨h1, h2⟩ := G.fixed_sample V c ρ hρ0 hρ1 hthr1 hκq hκl N
    have hle1 : val (G.resp V) (fun _ => c) (majority N) N [] ≤ 1 :=
      (val_mem_Icc (fun _ => c) (fun x => G.hκ _)
        (fun h => by unfold majority; split_ifs <;> norm_num) N []).2
    split_ifs with h
    · linarith
    · push Not at h; linarith [h1 h]
  calc _ ≤ ∑ V, G.prior V * (2 * B + (if G.thr < G.score V c then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun V _ => mul_le_mul_of_nonneg_left (hper V) (G.prior_nonneg V)
    _ = 2 * B + ∑ V, G.prior V * (if G.thr < G.score V c then (1 : ℝ) else 0) := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, G.prior_sum, one_mul]
    _ ≤ _ := by linarith [G.collision_le c μ₁ hcov]

open Classical in
/-- **Theorem 2.1 (noiseless kernel: one probe), averaged over `G₀`.** With `κ = 1{s > thr}`,
probing `c` once and answering the bit gives `δII = 0` and `δI ≤ n·μ₁`. -/
theorem one_probe_avg (c : Sph E) (hthr1 : G.thr < 1)
    (hκ0 : ∀ s ≤ G.thr, G.κ s = 0) (hκ1 : ∀ s, G.thr < s → G.κ s = 1)
    (μ₁ : ℝ) (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁) :
    (∀ V, val (G.respWith V c.1) (fun _ => c) (fun h => 1 - majority 1 h) 1 [] = 0) ∧
    ∑ V, G.prior V * val (G.resp V) (fun _ => c) (majority 1) 1 [] ≤ Fintype.card ι * μ₁ := by
  have hcc : inner ℝ c.1 c.1 = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, c.2]; norm_num
  constructor
  · intro V
    have hs1 := (G.score_mem V c).2
    have hpc : G.respWith V c.1 c = 1 := by
      unfold respWith; rw [hcc, max_eq_right hs1]; exact hκ1 1 hthr1
    simp [val_succ, hpc, majority]
    norm_num
  · refine le_trans (Finset.sum_le_sum fun V _ => mul_le_mul_of_nonneg_left ?_
      (G.prior_nonneg V)) (G.collision_le c μ₁ hcov)
    by_cases h : G.thr < G.score V c
    · rw [if_pos h]
      exact (val_mem_Icc (fun _ => c) (fun x => G.hκ _)
        (fun h => by unfold majority; split_ifs <;> norm_num) 1 []).2
    · rw [if_neg h]; push Not at h
      have hpc : G.resp V c = 0 := hκ0 _ h
      simp [val_succ, hpc, majority]
      norm_num

end Gallery

end OracleBounds.GeneralPrior
