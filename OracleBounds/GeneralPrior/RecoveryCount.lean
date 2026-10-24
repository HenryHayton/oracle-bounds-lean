import OracleBounds.GeneralPrior.Information
import OracleBounds.GeneralPrior.Budget

/-!
# The recovery-count inequality and the m-of-n bound (`n-face-general-prior-v2` Thm 6.1(4),
# Cor 6.2(ii), Cor 6.3 branch Q₁)

This file assembles the information branch end to end for an arbitrary independent product
prior, from the adaptive process up to a closed-form query lower bound. Every ingredient is
already proved elsewhere; here they are wired together:

* the per-face joint law of `(Vᵢ, transcript)` has first marginal `πᵢ` (`faceJoint_marg₁`);
* small-ball list-Fano for each face (`small_ball_fano`, G6);
* superadditivity over independent faces (`mutualInfo_superadditive_prior`, G7);
* the global budget `I ≤ β·Q` (`info_le_global`, Thm 5.1(d));
* the prior-agnostic summation algebra (`V6.Info.thm61_eq4`) and the m-of-n rearrangement
  (`V6.Info.cor62_v7`).

**Model.** `n` independent faces, face `i` drawn from `πᵢ` on a finite `Fine`. The oracle answers
probe `x` with probability `resp v x` when the gallery is `v` — any kernel at all; the budget
only needs `KL(Bern(resp v x) ‖ Bern ½) ≤ β`. The attacker is a deterministic adaptive probe rule
(randomised attackers average over it) whose outputs `centers e : Fin k → C` depend on the
transcript `e`. Face `i` is *recovered* when it is `near` some output — for the sphere, "within
`ε`". `p₀` bounds the prior mass of every such ball.

`xRec := Σᵢ P[face i recovered]` is `E[N_ε]` by linearity.

No `sorry`s.
-/

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6 OracleBounds.V6.Info

variable {ι Fine C X : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]

open Classical in
/-- **Theorem 6.1(4), general prior, any budget.** For any independent product prior, any
response kernel, any valid budget `B ≥ I(G; b₁..b_Q)`, and any adaptive attacker making `Q`
queries and producing `k` outputs, with `Λ := log(1/(k·p₀))` and `x := E[N_ε]`:

  `x · Λ ≤ B + n · h(min{x/n, ½})`.

Attacker's achievement on the left, query budget on the right. -/
theorem recovery_count_budget [Nonempty ι] [Nonempty Fine]
    (π : ι → Fine → ℝ) (hπ0 : ∀ i l, 0 ≤ π i l) (hπ1 : ∀ i, ∑ l, π i l = 1)
    (resp : (ι → Fine) → X → ℝ) (hresp : ∀ v x, 0 ≤ resp v x ∧ resp v x ≤ 1)
    (probe : List Bool → X) (Q : ℕ) (B : ℝ)
    (hB : Info.mutualInfo (fun te : (ι → Fine) × (Fin Q → Bool) =>
      (∏ j, π j (te.1 j)) * pathProb (resp te.1) probe Q [] te.2) ≤ B)
    (near : Fine → C → Prop) (k : ℕ) (centers : (Fin Q → Bool) → Fin k → C)
    (p₀ : ℝ) (hp₀0 : 0 ≤ p₀) (hp₀1 : (k : ℝ) * p₀ < 1)
    (hball : ∀ i (c : C), (∑ l ∈ Finset.univ.filter (near · c), π i l) ≤ p₀) :
    let qf : ι → Fine × (Fin Q → Bool) → ℝ := fun i le =>
      ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = le.1),
        (∏ j, π j (v j)) * pathProb (resp v) probe Q [] le.2
    let L : (Fin Q → Bool) → Finset Fine := fun e =>
      Finset.univ.filter (fun a => ∃ j, near a (centers e j))
    let P : ι → ℝ := fun i => ∑ le, if le.1 ∈ L le.2 then qf i le else 0
    (∑ i, P i) * Real.log (1 / ((k : ℝ) * p₀)) ≤
      B + (Fintype.card ι : ℝ) *
        Real.binEntropy (min ((∑ i, P i) / Fintype.card ι) (1 / 2)) := by
  intro qf L P
  have hPv0 : ∀ v e, 0 ≤ pathProb (resp v) probe Q [] e :=
    fun v => pathProb_nonneg probe (hresp v) Q []
  have hPv1 : ∀ v, ∑ e, pathProb (resp v) probe Q [] e = 1 :=
    fun v => pathProb_sum probe (hresp v) Q []
  have hqV0 : ∀ v : ι → Fine, 0 ≤ ∏ j, π j (v j) := fun v => Finset.prod_nonneg fun j _ => hπ0 j (v j)
  have hq0 : ∀ i le, 0 ≤ qf i le :=
    fun i le => Finset.sum_nonneg fun v _ => mul_nonneg (hqV0 v) (hPv0 v _)
  -- face `i`'s joint law has first marginal `πᵢ`, hence is a pmf
  have hm1 : ∀ i l, marg₁ (qf i) l = π i l :=
    fun i l => faceJoint_marg₁ π hπ1 (fun v e => pathProb (resp v) probe Q [] e) hPv1 i l
  have hqsum : ∀ i, ∑ le, qf i le = 1 := by
    intro i
    rw [Fintype.sum_prod_type]
    show ∑ l, marg₁ (qf i) l = 1
    rw [Finset.sum_congr rfl fun l _ => hm1 i l]
    exact hπ1 i
  -- small-ball Fano, face by face (G6)
  have hFano : ∀ i, P i * Real.log (1 / ((k : ℝ) * p₀)) - Real.binEntropy (P i)
      ≤ mutualInfo (qf i) := by
    intro i
    have hb : ∀ c : C, (∑ a ∈ Finset.univ.filter (near · c), marg₁ (qf i) a) ≤ p₀ := by
      intro c
      rw [Finset.sum_congr rfl fun a _ => hm1 i a]
      exact hball i c
    exact small_ball_fano (qf i) (hq0 i) (hqsum i) near k centers p₀ hp₀0 hp₀1 hb
  -- superadditivity (G7) then the global budget (Thm 5.1(d))
  have hInfo : ∑ i, mutualInfo (qf i) ≤ B := by
    have hsup := mutualInfo_superadditive_prior π hπ0 hπ1
      (fun v e => pathProb (resp v) probe Q [] e) hPv0 hPv1
    exact hsup.trans hB
  have hI0 : ∀ i, 0 ≤ mutualInfo (qf i) := fun i => mutualInfo_nonneg _ (hq0 i) (hqsum i)
  have hP : ∀ i, 0 ≤ P i ∧ P i ≤ 1 := by
    intro i
    refine ⟨Finset.sum_nonneg fun le _ => ?_, ?_⟩
    · split_ifs
      · exact hq0 i le
      · exact le_rfl
    · calc P i ≤ ∑ le, qf i le := Finset.sum_le_sum fun le _ => by
            split_ifs
            · exact le_rfl
            · exact hq0 i le
        _ = 1 := hqsum i
  have hΛ : 0 ≤ Real.log (1 / ((k : ℝ) * p₀)) := by
    rcases eq_or_lt_of_le (mul_nonneg (Nat.cast_nonneg k) hp₀0) with h | h
    · rw [← h]; simp
    · exact Real.log_nonneg (by rw [le_div_iff₀ h]; linarith)
  have h := thm61_eq4 (Real.log (1 / ((k : ℝ) * p₀))) B (∑ i, P i) 0 P
    (fun i => mutualInfo (qf i)) hΛ hP hFano hInfo hI0
    (Finset.sum_nonneg fun i _ => (hP i).1) le_rfl le_rfl
  linarith

open Classical in
/-- **Theorem 6.1(4) with the global budget `β·Q`** (Thm 5.1(d)). -/
theorem recovery_count_info [Nonempty ι] [Nonempty Fine]
    (π : ι → Fine → ℝ) (hπ0 : ∀ i l, 0 ≤ π i l) (hπ1 : ∀ i, ∑ l, π i l = 1)
    (resp : (ι → Fine) → X → ℝ) (hresp : ∀ v x, 0 ≤ resp v x ∧ resp v x ≤ 1)
    (probe : List Bool → X) (Q : ℕ) (β : ℝ) (hβ : ∀ v x, bkl (resp v x) (1 / 2) ≤ β)
    (near : Fine → C → Prop) (k : ℕ) (centers : (Fin Q → Bool) → Fin k → C)
    (p₀ : ℝ) (hp₀0 : 0 ≤ p₀) (hp₀1 : (k : ℝ) * p₀ < 1)
    (hball : ∀ i (c : C), (∑ l ∈ Finset.univ.filter (near · c), π i l) ≤ p₀) :
    let qf : ι → Fine × (Fin Q → Bool) → ℝ := fun i le =>
      ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = le.1),
        (∏ j, π j (v j)) * pathProb (resp v) probe Q [] le.2
    let L : (Fin Q → Bool) → Finset Fine := fun e =>
      Finset.univ.filter (fun a => ∃ j, near a (centers e j))
    let P : ι → ℝ := fun i => ∑ le, if le.1 ∈ L le.2 then qf i le else 0
    (∑ i, P i) * Real.log (1 / ((k : ℝ) * p₀)) ≤
      β * Q + (Fintype.card ι : ℝ) *
        Real.binEntropy (min ((∑ i, P i) / Fintype.card ι) (1 / 2)) :=
  recovery_count_budget π hπ0 hπ1 resp hresp probe Q (β * Q)
    (info_le_global (fun v : ι → Fine => ∏ j, π j (v j))
      (fun v => Finset.prod_nonneg fun j _ => hπ0 j (v j)) (prodPrior_sum π hπ1)
      resp hresp probe β hβ Q) near k centers p₀ hp₀0 hp₀1 hball

open Classical in
/-- **Corollary 6.2(ii) + Corollary 6.3 branch Q₁, general prior.** If the attacker recovers,
in expectation, at least `m/2` of the `n` faces at precision `ε` (which follows by Markov from
`P[N_ε ≥ m] ≥ ½`), and `Λ ≥ log(2en/m)`, then

  `Q ≥ m/(2β) · (Λ − log(2en/m))`,   `Λ = log(1/(k·p₀))`.

This is the closed-form query lower bound. With `β = log 2` it is prior- and kernel-free apart
from `p₀`; with `β = Cap(ρ)` it shows added noise multiplying the cost by `log 2 / Cap(ρ)`. -/
theorem m_of_n_queries [Nonempty ι] [Nonempty Fine]
    (π : ι → Fine → ℝ) (hπ0 : ∀ i l, 0 ≤ π i l) (hπ1 : ∀ i, ∑ l, π i l = 1)
    (resp : (ι → Fine) → X → ℝ) (hresp : ∀ v x, 0 ≤ resp v x ∧ resp v x ≤ 1)
    (probe : List Bool → X) (Q : ℕ) (β : ℝ) (hβpos : 0 < β)
    (hβ : ∀ v x, bkl (resp v x) (1 / 2) ≤ β)
    (near : Fine → C → Prop) (k : ℕ) (centers : (Fin Q → Bool) → Fin k → C)
    (p₀ : ℝ) (hp₀0 : 0 ≤ p₀) (hp₀1 : (k : ℝ) * p₀ < 1)
    (hball : ∀ i (c : C), (∑ l ∈ Finset.univ.filter (near · c), π i l) ≤ p₀)
    (m : ℝ) (hm : 1 ≤ m) :
    let qf : ι → Fine × (Fin Q → Bool) → ℝ := fun i le =>
      ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = le.1),
        (∏ j, π j (v j)) * pathProb (resp v) probe Q [] le.2
    let L : (Fin Q → Bool) → Finset Fine := fun e =>
      Finset.univ.filter (fun a => ∃ j, near a (centers e j))
    let P : ι → ℝ := fun i => ∑ le, if le.1 ∈ L le.2 then qf i le else 0
    m / 2 ≤ ∑ i, P i →
    1 + Real.log (2 * Fintype.card ι / m) ≤ Real.log (1 / ((k : ℝ) * p₀)) →
    m / (2 * β) * (Real.log (1 / ((k : ℝ) * p₀)) - (1 + Real.log (2 * Fintype.card ι / m)))
      ≤ Q := by
  intro qf L P hxm hΛL
  have h4 := recovery_count_info π hπ0 hπ1 resp hresp probe Q β hβ near k centers p₀ hp₀0 hp₀1
    hball
  have hxn : ∑ i, P i ≤ (Fintype.card ι : ℝ) := by
    have hle : ∀ i, P i ≤ 1 := fun i => by
      calc P i ≤ ∑ le, qf i le := Finset.sum_le_sum fun le _ => by
              split_ifs
              · exact le_rfl
              · exact Finset.sum_nonneg fun v _ => mul_nonneg
                  (Finset.prod_nonneg fun j _ => hπ0 j (v j))
                  (pathProb_nonneg probe (hresp v) Q [] _)
        _ = 1 := by
            rw [Fintype.sum_prod_type]
            show ∑ l, marg₁ (qf i) l = 1
            rw [Finset.sum_congr rfl fun l _ =>
              faceJoint_marg₁ π hπ1 (fun v e => pathProb (resp v) probe Q [] e)
                (fun v => pathProb_sum probe (hresp v) Q []) i l]
            exact hπ1 i
    calc ∑ i, P i ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => hle i
      _ = Fintype.card ι := by simp
  exact (cor62_v7 (Fintype.card ι) m _ β Q Q (∑ i, P i) hm hβpos le_rfl hxm hxn h4).2 hΛL

end OracleBounds.GeneralPrior
