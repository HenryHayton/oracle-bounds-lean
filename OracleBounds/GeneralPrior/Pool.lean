import OracleBounds.GeneralPrior.Randomised

/-!
# The candidate-pool prior (P1 Cor P.3; draft §3.3)

The attacker holds a pool of `M` candidate templates (`G.g : Fine → E`, `card Fine = M`) and the
list is `n` of them.

* **i.i.d. version** (`pool_ball`, `pool_m_of_n`): every face uniform on the pool, drawn
  independently. This is a finite independent prior, so every result of the general-prior chain
  applies directly, with `p(ε) ≤ K_ε/M` (`K_ε` the worst `ε`-ball occupancy of the pool) and
  `μ₁ ≤ W/M` (`W` the worst probe's reach count):

    `Q ≥ m/(2β*)·(log(M/(k·K_ε)) − log(2en/m))`.

* **Without replacement** (`wo_transfer`, `pool_wo_m_of_n`): the actual list has distinct entries.
  Its law is the i.i.d. law conditioned on distinctness, and distinctness has probability
  `≥ 1 − n(n−1)/M`; so any success probability transfers with an additive loss `η = n(n−1)/M`,
  and the bound holds with `m` replaced by `m(1 − 2η)`. No dependent-faces machinery is needed.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι] [Nonempty Fine]

open Classical in
/-- Pool ball mass: `p(ε) ≤ K/M` when every `ε`-ball contains at most `K` pool points. -/
lemma pool_ball (hunif : ∀ i l, G.π i l = 1 / Fintype.card Fine) (ε : ℝ) (K : ℕ)
    (hK : ∀ y : Sph E, (Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε)).card ≤ K) (i : ι)
    (y : Sph E) :
    (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ K / Fintype.card Fine := by
  simp only [hunif, Finset.sum_const, nsmul_eq_mul]
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hK y) (Nat.cast_nonneg _)

open Classical in
/-- Pool reach mass: `μ₁ ≤ W/M` when every probe reaches at most `W` pool points. -/
lemma pool_reach (hunif : ∀ i l, G.π i l = 1 / Fintype.card Fine) (W : ℕ)
    (hW : ∀ x : Sph E, (Finset.univ.filter (G.reachG · x)).card ≤ W) (i : ι) (x : Sph E) :
    (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ W / Fintype.card Fine := by
  simp only [hunif, Finset.sum_const, nsmul_eq_mul]
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hW x) (Nat.cast_nonneg _)

lemma log_pool {k K M : ℝ} (hk : 0 < k) (hK : 0 < K) (hM : 0 < M) :
    Real.log (1 / (k * (K / M))) = Real.log (M / (k * K)) := by
  congr 1; field_simp

open Classical in
/-- **Pool prior, i.i.d. draws (P1 Cor P.3, information branch).** If `P[N_ε ≥ m] ≥ ½`,
`1 ≤ m ≤ n` and `k·K_ε < M`: `Q ≥ m/(2β*)·(log(M/(k·K_ε)) − log(2en/m))`. -/
theorem pool_m_of_n (hunif : ∀ i l, G.π i l = 1 / Fintype.card Fine)
    (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ) (hβpos : 0 < βstar)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar)
    (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)
    (hk : 1 ≤ kout) (ε : ℝ) (K : ℕ) (hK0 : 1 ≤ K)
    (hK : ∀ y : Sph E, (Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε)).card ≤ K)
    (hkK : (kout : ℝ) * K < Fintype.card Fine)
    (m : ℝ) (hm : 1 ≤ m) (hmn : m ≤ Fintype.card ι) (hPN : 1 / 2 ≤ G.PN probe out ε m) :
    m / (2 * βstar) * (Real.log (Fintype.card Fine / ((kout : ℝ) * K)) -
      Real.log (2 * Real.exp 1 * Fintype.card ι / m)) ≤ Q := by
  have hM : (0 : ℝ) < Fintype.card Fine := by exact_mod_cast Fintype.card_pos
  have hk0 : (0 : ℝ) < kout := by exact_mod_cast hk
  have hK0' : (0 : ℝ) < K := by exact_mod_cast hK0
  have hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ 1 := fun i x =>
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun l _ _ => G.hπ0 i l).trans (G.hπ1 i).le
  have hkp : (kout : ℝ) * (K / Fintype.card Fine) < 1 := by
    rw [← mul_div_assoc, div_lt_one hM]; exact hkK
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hΛ := log_pool (k := (kout : ℝ)) hk0 hK0' hM
  by_cases hLΛ : Real.log (2 * Real.exp 1 * Fintype.card ι / m) ≤
      Real.log (1 / ((kout : ℝ) * (K / Fintype.card Fine)))
  · have h := (G.cor62_ii probe out hν βstar hβ 1 zero_le_one hcov ε _ (by positivity) hkp
      (G.pool_ball hunif ε K hK) m hm hmn hPN).2 hLΛ
    rw [hΛ] at h
    have hB : Bbest (Fintype.card ι) 1 G.ζ G.ν₀ βstar Q ≤ Q * βstar := min_le_left _ _
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  · push Not at hLΛ
    rw [hΛ] at hLΛ
    have : m / (2 * βstar) * (Real.log (Fintype.card Fine / ((kout : ℝ) * K)) -
        Real.log (2 * Real.exp 1 * Fintype.card ι / m)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith

/-! ### Sampling without replacement -/

open Classical in
/-- Average of `F` over lists of **distinct** pool entries (sampling without replacement). -/
noncomputable def woAvg (F : (ι → Fine) → ℝ) : ℝ :=
  (∑ v ∈ Finset.univ.filter (fun v : ι → Fine => Function.Injective v), F v) /
    (Finset.univ.filter (fun v : ι → Fine => Function.Injective v)).card

open Classical in
/-- `#{distinct lists} ≥ M^n·(1 − n(n−1)/M)`. -/
lemma card_inj_ge :
    (Fintype.card Fine : ℝ) ^ Fintype.card ι *
        (1 - (Fintype.card ι : ℝ) * (Fintype.card ι - 1) / Fintype.card Fine) ≤
      (Finset.univ.filter (fun v : ι → Fine => Function.Injective v)).card := by
  set n := Fintype.card ι
  set M := Fintype.card Fine
  have hM : (0 : ℝ) < M := by exact_mod_cast Fintype.card_pos
  have hcard : (Finset.univ.filter (fun v : ι → Fine => Function.Injective v)).card =
      M.descFactorial n := by
    rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding
      ι Fine), Fintype.card_embedding_eq]
  rw [hcard]
  by_cases hnM : n ≤ M
  · have hdesc : ((M + 1 - n : ℕ) : ℝ) ^ n ≤ (M.descFactorial n : ℝ) := by
      exact_mod_cast Nat.pow_sub_le_descFactorial M n
    have hcast : ((M + 1 - n : ℕ) : ℝ) = M * (1 + (-( (n : ℝ) - 1) / M)) := by
      rw [Nat.cast_sub (by omega)]; push_cast; field_simp; ring
    rw [hcast, mul_pow] at hdesc
    have hbern := one_add_mul_le_pow (a := -((n : ℝ) - 1) / M) (by
      rw [neg_div, neg_le_neg_iff]
      have : ((n : ℝ) - 1) / M ≤ 1 := by
        rw [div_le_one hM]; have := (show (n : ℝ) ≤ M by exact_mod_cast hnM); linarith
      linarith) n
    have e : (1 : ℝ) - n * (n - 1) / M = 1 + n * (-((n : ℝ) - 1) / M) := by ring
    rw [e]
    calc (M : ℝ) ^ n * (1 + n * (-((n : ℝ) - 1) / M))
        ≤ (M : ℝ) ^ n * (1 + (-((n : ℝ) - 1) / M)) ^ n :=
          mul_le_mul_of_nonneg_left hbern (by positivity)
      _ ≤ _ := hdesc
  · -- more faces than pool points: the bound is non-positive
    push Not at hnM
    have hnM' : (M : ℝ) + 1 ≤ n := by exact_mod_cast hnM
    have : (1 : ℝ) - n * (n - 1) / M ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hM]; nlinarith
    calc (M : ℝ) ^ n * (1 - n * (n - 1) / M) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) this
      _ ≤ _ := Nat.cast_nonneg _

open Classical in
/-- **Transfer from without- to with-replacement.** For `F ∈ [0,1]` and the uniform pool prior,
`E_iid[F] ≥ E_wo[F] − n(n−1)/M`. -/
theorem wo_transfer (hunif : ∀ i l, G.π i l = 1 / Fintype.card Fine) (F : (ι → Fine) → ℝ)
    (hF : ∀ v, 0 ≤ F v ∧ F v ≤ 1) :
    woAvg F - (Fintype.card ι : ℝ) * (Fintype.card ι - 1) / Fintype.card Fine ≤
      ∑ v, G.prior v * F v := by
  set n := Fintype.card ι
  set M := Fintype.card Fine
  set S := Finset.univ.filter (fun v : ι → Fine => Function.Injective v)
  have hM : (0 : ℝ) < M := by exact_mod_cast Fintype.card_pos
  have hprior : ∀ v, G.prior v = ((M : ℝ) ^ n)⁻¹ := fun v => by
    unfold prior; simp [hunif, n, M, Finset.prod_const, Finset.card_univ]
  have hsum : ∑ v, G.prior v * F v ≥ ((M : ℝ) ^ n)⁻¹ * ∑ v ∈ S, F v := by
    rw [Finset.mul_sum]
    calc ∑ v, G.prior v * F v ≥ ∑ v ∈ S, G.prior v * F v :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun v _ _ => mul_nonneg (G.prior_nonneg v) (hF v).1
      _ = _ := Finset.sum_congr rfl fun v _ => by rw [hprior]
  have hcard := card_inj_ge (ι := ι) (Fine := Fine)
  have hwo1 : woAvg F ≤ 1 := by
    unfold woAvg
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · rw [h0]; simp
    · rw [div_le_one (by exact_mod_cast hpos)]
      calc ∑ v ∈ S, F v ≤ ∑ _v ∈ S, (1 : ℝ) := Finset.sum_le_sum fun v _ => (hF v).2
        _ = S.card := by simp
  have hwo0 : 0 ≤ woAvg F :=
    div_nonneg (Finset.sum_nonneg fun v _ => (hF v).1) (Nat.cast_nonneg _)
  have hkey : woAvg F * (S.card / (M : ℝ) ^ n) = ((M : ℝ) ^ n)⁻¹ * ∑ v ∈ S, F v := by
    unfold woAvg
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · have : ∑ v ∈ S, F v = 0 := by rw [Finset.card_eq_zero.1 h0]; simp
      rw [h0, this]; simp
    · show (∑ v ∈ S, F v) / (S.card : ℝ) * ((S.card : ℝ) / (M : ℝ) ^ n) =
        ((M : ℝ) ^ n)⁻¹ * ∑ v ∈ S, F v
      have : (S.card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      field_simp
  have hratio : 1 - (n : ℝ) * (n - 1) / M ≤ S.card / (M : ℝ) ^ n := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have : woAvg F * (1 - (n : ℝ) * (n - 1) / M) ≤ woAvg F * (S.card / (M : ℝ) ^ n) :=
    mul_le_mul_of_nonneg_left hratio hwo0
  have hη0 : 0 ≤ (n : ℝ) * (n - 1) / M := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
    exact div_nonneg (by nlinarith) hM.le
  have hwη := mul_le_mul_of_nonneg_right hwo1 hη0
  have e : woAvg F * (1 - (n : ℝ) * (n - 1) / M) =
      woAvg F - woAvg F * ((n : ℝ) * (n - 1) / M) := by ring
  linarith

open Classical in
/-- **Pool prior, sampling without replacement.** If the attacker recovers `≥ m` entries with
probability `≥ ½` on a list of `n` *distinct* pool entries, then with `η = n(n−1)/M` and
`1 ≤ m` and `m′ = m(1 − 2η) ≥ 1`:

  `Q ≥ m′/(2β*)·(log(M/(k·K_ε)) − log(2en/m′))`. -/
theorem pool_wo_m_of_n (hunif : ∀ i l, G.π i l = 1 / Fintype.card Fine)
    (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ) (hβpos : 0 < βstar)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar)
    (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)
    (hk : 1 ≤ kout) (ε : ℝ) (K : ℕ) (hK0 : 1 ≤ K)
    (hK : ∀ y : Sph E, (Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε)).card ≤ K)
    (hkK : (kout : ℝ) * K < Fintype.card Fine) (m : ℝ) (hm : 1 ≤ m)
    (hm' : 1 ≤ m * (1 - 2 * ((Fintype.card ι : ℝ) * (Fintype.card ι - 1) / Fintype.card Fine)))
    (hPN : 1 / 2 ≤ woAvg (fun v => ∑ e, pathProb (G.resp v) probe Q [] e *
      (if m ≤ G.Ncount out ε v e then (1 : ℝ) else 0))) :
    let m' := m * (1 - 2 * ((Fintype.card ι : ℝ) * (Fintype.card ι - 1) / Fintype.card Fine))
    m' / (2 * βstar) * (Real.log (Fintype.card Fine / ((kout : ℝ) * K)) -
      Real.log (2 * Real.exp 1 * Fintype.card ι / m')) ≤ Q := by
  intro m'
  set n : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hndef
  set η := (Fintype.card ι : ℝ) * (Fintype.card ι - 1) / Fintype.card Fine with hη
  have hM : (0 : ℝ) < Fintype.card Fine := by exact_mod_cast Fintype.card_pos
  have hk0 : (0 : ℝ) < kout := by exact_mod_cast hk
  have hK0' : (0 : ℝ) < K := by exact_mod_cast hK0
  have hn0 : 0 < n := by rw [hndef]; exact_mod_cast Fintype.card_pos
  have hη0 : 0 ≤ η := by
    rw [hη]; apply div_nonneg _ hM.le
    have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
    nlinarith
  have hm0 : 0 ≤ m := by linarith
  -- the i.i.d. success probability
  set F : (ι → Fine) → ℝ := fun v => ∑ e, pathProb (G.resp v) probe Q [] e *
    (if m ≤ G.Ncount out ε v e then (1 : ℝ) else 0) with hFdef
  have hF : ∀ v, 0 ≤ F v ∧ F v ≤ 1 := fun v => by
    have h0 : ∀ e, 0 ≤ pathProb (G.resp v) probe Q [] e :=
      pathProb_nonneg probe (G.resp_mem v) Q []
    have hs := pathProb_sum probe (G.resp_mem v) Q []
    constructor
    · exact Finset.sum_nonneg fun e _ => mul_nonneg (h0 e) (by split_ifs <;> norm_num)
    · calc F v ≤ ∑ e, pathProb (G.resp v) probe Q [] e := Finset.sum_le_sum fun e _ =>
            mul_le_of_le_one_right (h0 e) (by split_ifs <;> norm_num)
        _ = 1 := hs
  have hPN_eq : G.PN probe out ε m = ∑ v, G.prior v * F v := by
    unfold PN wt; simp only [hFdef, Finset.mul_sum, mul_assoc]
  have hiid : 1 / 2 - η ≤ G.PN probe out ε m := by
    rw [hPN_eq]; have := G.wo_transfer hunif F hF; linarith
  -- Markov, then the information branch with `m′`
  have hxm : m' / 2 ≤ G.EN probe out ε := by
    have hle : m * G.PN probe out ε m ≤ G.EN probe out ε := by
      unfold PN EN
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun e _ => ?_
      have hw := G.wt_nonneg probe v e
      have hN := (G.Ncount_mem out ε v e).1
      split_ifs <;> nlinarith
    have : m * (1 / 2 - η) ≤ m * G.PN probe out ε m := mul_le_mul_of_nonneg_left hiid hm0
    show m * (1 - 2 * η) / 2 ≤ _
    linarith
  have hxn := G.EN_le_n probe out ε
  have hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ 1 := fun i x =>
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun l _ _ => G.hπ0 i l).trans (G.hπ1 i).le
  have hkp : (kout : ℝ) * (K / Fintype.card Fine) < 1 := by
    rw [← mul_div_assoc, div_lt_one hM]; exact hkK
  set Λ := Real.log (1 / ((kout : ℝ) * (K / Fintype.card Fine)))
  set B := Bbest (Fintype.card ι) 1 G.ζ G.ν₀ βstar Q
  have h4 := G.thm61_4 probe out hν βstar hβ 1 zero_le_one hcov ε _ (by positivity) hkp
    (G.pool_ball hunif ε K hK)
  have cv := Info.cor62_v7 n m' Λ 1 B B (G.EN probe out ε) hm' one_pos le_rfl hxm hxn
    (by rw [one_mul]; exact h4)
  have hΛ : Λ = Real.log (Fintype.card Fine / ((kout : ℝ) * K)) := log_pool hk0 hK0' hM
  have hm'0 : 0 < m' := by linarith
  have hL : Real.log (2 * Real.exp 1 * n / m') = 1 + Real.log (2 * n / m') :=
    log_two_e hn0 hm'0
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hB1 : B ≤ Q * βstar := min_le_left _ _
  by_cases hLΛ : Real.log (2 * Real.exp 1 * n / m') ≤ Λ
  · have hBm := cv.2 (by rw [← hL]; exact hLΛ)
    rw [← hL] at hBm
    rw [← hΛ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    simp only [one_mul, mul_one] at hBm
    nlinarith
  · push Not at hLΛ
    have : m' / (2 * βstar) * (Λ - Real.log (2 * Real.exp 1 * n / m')) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    rw [← hΛ]; linarith

/-! ### The whole candidate list (technical note §3.3, Corollary 3.3.2) -/

open Classical in
/-- **Corollary 3.3.2 (the whole list, any list size).**
*Signed off by the administrator, 23 Sep 2026; faithful to technical note Corollary 3.3.2.*

In the setting of Proposition 3.3.1 (list `n` i.i.d. uniform draws from the pool of size `M`),
suppose no probe reaches two pool points (`W = 1`, so `μ₁ ≤ 1/M`), the pool is more than
`2ε`-separated (`K_ε = 1`, so `p(ε) ≤ 1/M`), the kernel is band-null (`ζ = 0`) and the attacker
outputs at most `n` guesses. If `P[N_ε ≥ n] ≥ ½` then `Q ≥ M/2 − n`.

This is the rearrangement of `cor62_i` (Corollary 2.6.3(i) in its general form
`nQμ₁ ≥ m/2 − n·k_out·p(ε)`) at `m = n`, `k_out ≤ n`, `μ₁ ≤ 1/M`, `p(ε) ≤ 1/M`; the proof in fact
gives the slightly stronger `Q ≥ M/2 − k_out`. -/
theorem cor_whole_list (hunif : ∀ i l, G.π i l = 1 / Fintype.card Fine) (hζ : G.ζ = 0)
    (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)
    (hk : kout ≤ Fintype.card ι) (ε : ℝ)
    (hW : ∀ x : Sph E, (Finset.univ.filter (G.reachG · x)).card ≤ 1)
    (hK : ∀ y : Sph E, (Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε)).card ≤ 1)
    (hPN : 1 / 2 ≤ G.PN probe out ε (Fintype.card ι)) :
    (Fintype.card Fine : ℝ) / 2 - Fintype.card ι ≤ Q := by
  set M := (Fintype.card Fine : ℝ) with hMdef
  set n := (Fintype.card ι : ℝ) with hndef
  have hM : (0 : ℝ) < M := by rw [hMdef]; exact_mod_cast Fintype.card_pos
  have hn : (1 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast Fintype.card_pos
  have hn0 : (0 : ℝ) < n := by linarith
  have hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ 1 / M := by
    intro i x
    have h := G.pool_reach hunif 1 hW i x
    simpa [hMdef] using h
  have hball : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ 1 / M := by
    intro i y
    have h := G.pool_ball hunif ε 1 hK i y
    simpa [hMdef] using h
  have h := (G.cor62_i probe out (1 / M) ε (1 / M) (by positivity) (by positivity)
    hcov hball n hn hPN).1
  rw [hζ] at h
  have h1 : n / 2 - n * (kout : ℝ) / M ≤ n * Q / M := by
    have e1 : n * (kout : ℝ) * (1 / M) = n * kout / M := by ring
    have e2 : n * (Q : ℝ) * (1 / M + 2 * 0) = n * Q / M := by ring
    rw [e1, e2] at h
    exact h
  have h2 : n * (M / 2) - n * (kout : ℝ) ≤ n * Q := by
    have h3 := mul_le_mul_of_nonneg_right h1 hM.le
    calc n * (M / 2) - n * (kout : ℝ) = (n / 2 - n * (kout : ℝ) / M) * M := by
          field_simp
      _ ≤ (n * Q / M) * M := h3
      _ = n * Q := by field_simp
  have h4 : M / 2 - (kout : ℝ) ≤ Q :=
    le_of_mul_le_mul_left (by linarith : n * (M / 2 - (kout : ℝ)) ≤ n * Q) hn0
  have hkn : ((kout : ℕ) : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hk
  linarith

end Gallery

end OracleBounds.GeneralPrior
