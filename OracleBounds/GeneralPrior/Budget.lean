import OracleBounds.V6.InfoProcess

/-!
# The global per-round budget (`n-face-general-prior-v2` Thm 5.1(d))

v1 of the general-prior note showed that v7's *per-contact* bound `β*·E[C_Q] + β₀Q` is false for
a general prior (its Example 5.0). What survives — and what v1 missed — is the elementary
**global** bound: each round is one Bernoulli bit, so

* `I(G; b₁..b_Q | U) ≤ Q · log 2` for any prior and any kernel, and
* `I(G; b₁..b_Q | U) ≤ Q · Cap(ρ)` under the range condition `κ(s) ∈ [ρ, 1−ρ]`.

No measurability-of-quietness is needed, which is exactly why Example 5.0 does not touch it.
This is the branch of `B_best` that binds at any realistic gallery size (`n·μ₁·Q ≳ 1`), so it is
the budget every downstream number actually rests on.

Formally it is `OracleBounds.V6.thm51_process` with the quiet predicate taken to be *empty*: with
nothing quiet, the non-quiet round count is `Q` identically, and the conclusion collapses to
`β · Q`. No new machinery is required — the golden formula (`mutualInfo_le_avg_kl`), the KL chain
rule (`kl_chain`) and the constant `Bern(½)` reference already in `V6.InfoProcess` suffice.

No `sorry`s.
-/

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {X : Type*}

open Classical in
/-- **Theorem 5.1(d), general form.** If every round's answer probability satisfies
`KL(Bern(p θ x) ‖ Bern ½) ≤ β`, then `Q` rounds leak at most `β·Q` nats — for *every* prior,
with no quietness structure whatsoever. -/
theorem info_le_global {Θ : Type*} [Fintype Θ] (π : Θ → ℝ) (hπ : ∀ θ, 0 ≤ π θ)
    (hπ1 : ∑ θ, π θ = 1) (p : Θ → X → ℝ) (hp : ∀ θ x, 0 ≤ p θ x ∧ p θ x ≤ 1)
    (probe : List Bool → X) (β : ℝ) (hβ : ∀ θ x, bkl (p θ x) (1 / 2) ≤ β) (Q : ℕ) :
    Info.mutualInfo (fun te : Θ × (Fin Q → Bool) => π te.1 * pathProb (p te.1) probe Q [] te.2)
      ≤ β * Q := by
  have h := thm51_process π hπ hπ1 p hp probe (fun _ => False) (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun θ x hx => absurd hx not_false) β (fun θ x _ => hβ θ x) Q
  refine h.trans (le_of_eq ?_)
  -- the leaf count is identically `Q` (nothing is quiet), so `val` of it is `Q`
  have hstep : ∀ (F : List Bool → ℝ), (∀ h' : List Bool, F h' = (Q : ℝ)) →
      ∀ θ : Θ, val (p θ) probe F Q [] = (Q : ℝ) := by
    intro F hF θ
    rw [val_mono_eq (G := fun _ => (Q : ℝ)) (fun h' _ => hF h')]
    exact val_const (p θ) probe (Q : ℝ) Q []
  congr 1
  rw [Finset.sum_congr rfl (fun θ _ => by rw [hstep _ (fun h' => by simp) θ])]
  rw [← Finset.sum_mul, hπ1, one_mul]

open Classical in
/-- **Theorem 5.1(d), `log 2` form.** For any prior and any kernel: `Q` one-bit answers leak at
most `Q · log 2` nats. This is the prior-free statement — nothing is assumed about the templates,
the geometry, or the attacker. -/
theorem info_le_log_two {Θ : Type*} [Fintype Θ] (π : Θ → ℝ) (hπ : ∀ θ, 0 ≤ π θ)
    (hπ1 : ∑ θ, π θ = 1) (p : Θ → X → ℝ) (hp : ∀ θ x, 0 ≤ p θ x ∧ p θ x ≤ 1)
    (probe : List Bool → X) (Q : ℕ) :
    Info.mutualInfo (fun te : Θ × (Fin Q → Bool) => π te.1 * pathProb (p te.1) probe Q [] te.2)
      ≤ Real.log 2 * Q :=
  info_le_global π hπ hπ1 p hp probe _ (fun θ x => bkl_half_le_log_two (hp θ x)) Q

open Classical in
/-- **Theorem 5.1(d), `Cap(ρ)` form.** Under the range condition `p θ x ∈ [ρ, 1−ρ]` (fresh noise
at level `ρ`), `Q` answers leak at most `Q · (log 2 − h(ρ))` nats. This is where deliberately
added noise enters every downstream bound, as the factor `log 2 / Cap(ρ)`. -/
theorem info_le_cap {Θ : Type*} [Fintype Θ] (π : Θ → ℝ) (hπ : ∀ θ, 0 ≤ π θ)
    (hπ1 : ∑ θ, π θ = 1) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 1 / 2) (p : Θ → X → ℝ)
    (hp : ∀ θ x, ρ ≤ p θ x ∧ p θ x ≤ 1 - ρ) (probe : List Bool → X) (Q : ℕ) :
    Info.mutualInfo (fun te : Θ × (Fin Q → Bool) => π te.1 * pathProb (p te.1) probe Q [] te.2)
      ≤ (Real.log 2 - Real.binEntropy ρ) * Q :=
  info_le_global π hπ hπ1 p
    (fun θ x => ⟨by linarith [(hp θ x).1], by linarith [(hp θ x).2]⟩) probe _
    (fun θ x => bkl_half_le_cap hρ hρ2 (hp θ x)) Q

end OracleBounds.GeneralPrior
