import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Geometric and kernel facts used by the operational theorems (v6 §§3, 4, 7, 10)

All proved, no `sorry`s. These are the only places where the sphere / inner product enters the
coupling results; the spread family (N1 Lemma 2.7) enters only through the coverage hypothesis
`#{w : ⟨x, z_w⟩ > t₀} ≤ μ₁M`, and the 1-separation `‖z_w − z_w'‖ ≥ 1`, both taken as hypotheses.
-/

namespace OracleBounds.V6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Reach containment** (v6 §3, N1 §5; task a19, contrapositive form): a unit probe that
*matches* a template `g` in cap `z` (score above `τ − δ`) lies in the cap's reach `⟨x,z⟩ > t₀`,
`t₀ = τ − δ − r₀`. -/
theorem reach_of_match {x g z : E} {thr r₀ : ℝ} (hx : ‖x‖ = 1) (hg : ‖g - z‖ ≤ r₀)
    (hm : thr < inner ℝ x g) : thr - r₀ < inner ℝ x z := by
  have h1 : inner ℝ x g = inner ℝ x z + inner ℝ x (g - z) := by rw [inner_sub_right]; ring
  have h2 : inner ℝ x (g - z) ≤ ‖x‖ * ‖g - z‖ := real_inner_le_norm _ _
  rw [hx, one_mul] at h2
  linarith

/-- **Kernel locality** (proof of Lemma 4.1, case analysis). `κ s` is the probability of bit 1 at
score `s`; for binary responses total variation is `|κ s − κ s'|`. If the kernel is `ζ`-band-null
(`TV(κ(·|s), ν₀) ≤ ζ` for `s ≤ τ − δ`) and face `i`'s own score is `≤ τ − δ`, then deleting face `i`
changes the response law by at most `2ζ`, whatever the other faces' maximum score `m` is. -/
theorem kernel_locality (κ : ℝ → ℝ) (ν₀ ζ thr : ℝ) (hband : ∀ s ≤ thr, |κ s - ν₀| ≤ ζ)
    {s : ℝ} (m : ℝ) (hs : s ≤ thr) : |κ (max s m) - κ m| ≤ 2 * ζ := by
  have hζ : 0 ≤ ζ := (abs_nonneg _).trans (hband thr le_rfl)
  rcases le_total s m with h | h
  · rw [max_eq_right h]; simp; linarith
  · rw [max_eq_left h]
    calc |κ s - κ m| = |(κ s - ν₀) - (κ m - ν₀)| := by ring_nf
      _ ≤ |κ s - ν₀| + |κ m - ν₀| := abs_sub _ _
      _ ≤ ζ + ζ := add_le_add (hband s hs) (hband m (h.trans hs))
      _ = 2 * ζ := by ring

/-- **At most one centre within `1/2`** (Prop 7.3, Thm 10.1, Thm 6.1 (3) proofs). If two unit
centres are at chordal distance `≥ 1`, no *unit* vector is within distance `1/2` of both. This
holds with non-strict `≤ 1/2`, so the equality case `r₀ + 3/8 = 1/2` flagged in F4 is harmless. -/
theorem not_near_two {a b c : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hab : 1 ≤ ‖a - b‖) (hac : ‖a - c‖ ≤ 1 / 2) (hbc : ‖b - c‖ ≤ 1 / 2) : False := by
  set u := a - c
  set v := b - c
  have huv : u - v = a - b := by simp [u, v]
  have e1 := norm_sub_sq_real u v
  have e2 := norm_add_sq_real u v
  have ea : ‖c + u‖ = 1 := by simp [u, ha]
  have eb : ‖c + v‖ = 1 := by simp [v, hb]
  have e3 := norm_add_sq_real c u
  have e4 := norm_add_sq_real c v
  rw [ea, hc] at e3
  rw [eb, hc] at e4
  have e5 : inner ℝ c (u + v) = inner ℝ c u + inner ℝ c v := inner_add_right _ _ _
  have e6 := abs_real_inner_le_norm c (u + v)
  rw [hc, one_mul] at e6
  have e7 := (abs_le.mp e6).1
  rw [huv] at e1
  have hu0 := norm_nonneg u
  have hv0 := norm_nonneg v
  have hw0 := norm_nonneg (u + v)
  have hab2 : 1 ≤ ‖a - b‖ ^ 2 := by nlinarith
  have hu2 : ‖u‖ ^ 2 ≤ 1 / 4 := by nlinarith
  have hv2 : ‖v‖ ^ 2 ≤ 1 / 4 := by nlinarith
  -- ‖u+v‖² = 2‖u‖² + 2‖v‖² − ‖u−v‖² ≤ 0, while ⟨c, u+v⟩ = −(‖u‖²+‖v‖²)/2 ≤ −1/4.
  have hw2 : ‖u + v‖ ^ 2 ≤ 0 := by nlinarith
  have hw : ‖u + v‖ = 0 := by nlinarith
  nlinarith

/-- Pathwise count used for Prop 7.3 / Thm 6.1 (3) / Thm 10.1: `k` unit output points can be
within `1/2` of at most `k` of the (1-separated, unit) centres. -/
theorem card_near_le {Cap : Type*} (S : Finset Cap) (z : Cap → E) (hz : ∀ w ∈ S, ‖z w‖ = 1)
    (hsep : ∀ w ∈ S, ∀ w' ∈ S, w ≠ w' → 1 ≤ ‖z w - z w'‖) {k : ℕ} (y : Fin k → E)
    (hy : ∀ j, ‖y j‖ = 1) [DecidablePred fun w => ∃ j, ‖y j - z w‖ ≤ 1 / 2]
    [∀ j, DecidablePred fun w => ‖y j - z w‖ ≤ 1 / 2] [DecidableEq Cap] :
    (S.filter fun w => ∃ j, ‖y j - z w‖ ≤ 1 / 2).card ≤ k := by
  have hsub : (S.filter fun w => ∃ j, ‖y j - z w‖ ≤ 1 / 2) =
      Finset.univ.biUnion (fun j => S.filter fun w => ‖y j - z w‖ ≤ 1 / 2) := by
    ext w; simp
  rw [hsub]
  calc (Finset.univ.biUnion (fun j => S.filter fun w => ‖y j - z w‖ ≤ 1 / 2)).card
      ≤ ∑ j, (S.filter fun w => ‖y j - z w‖ ≤ 1 / 2).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin k, 1 := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.card_le_one.2
        intro w hw w' hw'
        simp only [Finset.mem_filter] at hw hw'
        by_contra hne
        exact not_near_two (hz w hw.1) (hz w' hw'.1) (hy j) (hsep w hw.1 w' hw'.1 hne)
          (by rw [norm_sub_rev]; exact hw.2) (by rw [norm_sub_rev]; exact hw'.2)
    _ = k := by simp

omit [InnerProductSpace ℝ E] in
/-- Recovery at precision `ε` forces an output within `ε + r₀ ≤ 1/2` of the cap centre. -/
theorem near_of_close {y g z : E} {ε r₀ : ℝ} (hy : ‖y - g‖ ≤ ε) (hg : ‖g - z‖ ≤ r₀)
    (h : ε + r₀ ≤ 1 / 2) : ‖y - z‖ ≤ 1 / 2 :=
  calc ‖y - z‖ = ‖(y - g) + (g - z)‖ := by abel_nf
    _ ≤ ‖y - g‖ + ‖g - z‖ := norm_add_le _ _
    _ ≤ 1 / 2 := by linarith

omit [InnerProductSpace ℝ E] in
/-- An output farther than `1/2` from the centre is at least `3/8` from the template (`r₀ ≤ 1/8`). -/
theorem far_of_not_near {y g z : E} {r₀ : ℝ} (hy : 1 / 2 < ‖y - z‖) (hg : ‖g - z‖ ≤ r₀)
    (hr : r₀ ≤ 1 / 8) : 3 / 8 ≤ ‖y - g‖ := by
  have : ‖y - z‖ ≤ ‖y - g‖ + ‖g - z‖ := by
    calc ‖y - z‖ = ‖(y - g) + (g - z)‖ := by abel_nf
      _ ≤ _ := norm_add_le _ _
  linarith

end OracleBounds.V6
