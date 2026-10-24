import Mathlib

/-!
# The separation event `SEP` of Theorem 4.3.8 (blind `m`-of-`n`, K0)

**Signed off by the administrator, 22 Sep 2026.** Statements drafted by a subagent; each re-read
against `briefs/v11.1/airlock-draft-v11.1.tex` Theorem 4.3.8 and against v12's restatement.

* `launch_targets_injective` is a faithful transcription of v12 Theorem 4.3.8(ii). Its hypotheses
  `hx` (probes are unit vectors), `hloud` (each launch probe is loud on its target) and `htest`
  (each launch probe passed the attribution test against every earlier output) are invariants of
  the algorithm, not assumptions on the world; the one substantive hypothesis, `hacc`, is (ii)'s
  "each localisation returns a point within `ε` of its target".
* The `SEP` results transcribe v11.1's `SEP` as a predicate on a gallery rather than an event
  (proving the event empty is stronger than bounding its probability). `sep := 3πε/√(1−t²)` is
  generalised to any `sep ≥ 0`, which only strengthens them. `sep_forces_tiny_reach` carries the
  labelled geometric input `μ₁ ≤ (2(1−t))^k`; its conclusion is about the uniform-sphere model in
  which Theorem 4.3.8 is posed, not about deployed systems (see findings/v11-change-requests.md A).

Theorem 4.3.8 of `briefs/v11.1/airlock-draft-v11.1.tex` conditions its success guarantee on

> `SEP` := the event that all pairwise angles between faces exceed
> `2·arccos t + 3πε/√(1−t²)`, of probability `≥ 1 − p_sep`,

and concludes success with probability `≥ 1 − δ/2 − p_sep − n(n−1)Q_loc q`.

This file records the *geometric* fact that `SEP` is not merely improbable but **empty** in the
deployment regime, so `p_sep = 1` and the guarantee is vacuous there.  The mechanism is the
elementary Gram bound `0 ≤ ‖∑ᵢ gᵢ‖²`: `n` unit vectors with all pairwise inner products `≤ C`
force `0 ≤ n + n(n−1)C`, i.e. `C ≥ −1/(n−1)`.  Since `SEP` forces every pairwise inner product
below `cos(2 arccos t) = 2t² − 1`, it is unsatisfiable as soon as `n + n(n−1)(2t²−1) ≤ 0`.

At the draft's operating point `C1 = (d_eff, n, q, ε) = (512, 10⁴, 10⁻⁶, 10⁻³)` the threshold is
`t = 0.2081` (`briefs/attacks/assumption-a.md`), so `2 arccos t = 156°` and `2t² − 1 = −0.9134`:
`SEP` is empty already at `n = 3` (`sep_empty_of_thr_le_half`, since `t ≤ 1/2`), let alone at
`n = 10⁴`.  Conversely `sep_forces_thr` shows `SEP` can only be non-empty when
`2(n−1)t² > n−2`, i.e. `t > 1/√2` for large `n`, where the reach probability — and hence the
theorem's own query budget `K = ⌈log(2n/δ)/q⌉` — is astronomically outside the regime the
theorem is quoted in (`sep_forces_tiny_reach`).

Throughout, `0 ≤ t` is assumed where it is needed; the draft assumes `thr > 0` wherever the
blind prior of §3.2 is in force.

The last section discharges `SEP`'s *role* in the proof without any separation hypothesis:
`launch_targets_injective` is the "`m` points ε-close to `m` **distinct** faces" conclusion,
obtained from the attribution test alone (`briefs/attacks/assumption-a.md` §4.4).

No `sorry`.
-/

namespace OracleBounds.Attacks.BlindMofN

open Real Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## 1. The Gram bound -/

/-- Expansion of `‖∑ᵢ gᵢ‖²` as the sum of all Gram entries. -/
lemma norm_sum_sq_eq {n : ℕ} (g : Fin n → E) :
    ‖∑ i, g i‖ ^ 2 = ∑ i, ∑ j, (inner ℝ (g i) (g j) : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  exact Finset.sum_congr rfl fun i _ => inner_sum _ _ _

private lemma card_erase_cast {n : ℕ} (i : Fin n) :
    (((univ : Finset (Fin n)).erase i).card : ℝ) = (n : ℝ) - 1 := by
  have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact i.elim0)
  rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ, Fintype.card_fin,
    Nat.cast_sub h1, Nat.cast_one]

/-- One row of the Gram matrix: unit `gᵢ`, off-diagonal entries `≤ C`. -/
lemma row_le {n : ℕ} (g : Fin n → E) (hg : ∀ i, ‖g i‖ = 1) (C : ℝ)
    (hC : ∀ i j, i ≠ j → (inner ℝ (g i) (g j) : ℝ) ≤ C) (i : Fin n) :
    ∑ j, (inner ℝ (g i) (g j) : ℝ) ≤ 1 + ((n : ℝ) - 1) * C := by
  have hmem : i ∈ (univ : Finset (Fin n)) := mem_univ i
  have hsplit := Finset.add_sum_erase (univ : Finset (Fin n))
    (fun j => (inner ℝ (g i) (g j) : ℝ)) hmem
  have hdiag : (inner ℝ (g i) (g i) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hg i]; norm_num
  have hoff : ∑ j ∈ univ.erase i, (inner ℝ (g i) (g j) : ℝ) ≤ ((n : ℝ) - 1) * C := by
    calc ∑ j ∈ univ.erase i, (inner ℝ (g i) (g j) : ℝ)
        ≤ ∑ _j ∈ univ.erase i, C :=
          Finset.sum_le_sum fun j hj => hC i j (Ne.symm (Finset.ne_of_mem_erase hj))
      _ = ((n : ℝ) - 1) * C := by
          rw [Finset.sum_const, nsmul_eq_mul, card_erase_cast i]
  rw [← hsplit, hdiag]
  linarith

private lemma sum_const_row {n : ℕ} (C : ℝ) :
    ∑ _i : Fin n, (1 + ((n : ℝ) - 1) * C) = (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1) * C := by
  rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Gram bound.** `n` unit vectors with all pairwise inner products `≤ C` satisfy
`0 ≤ n + n(n−1)C`; equivalently `C ≥ −1/(n−1)` for `n ≥ 2`. -/
theorem gram_pairwise_le {n : ℕ} (g : Fin n → E) (hg : ∀ i, ‖g i‖ = 1) (C : ℝ)
    (hC : ∀ i j, i ≠ j → (inner ℝ (g i) (g j) : ℝ) ≤ C) :
    (0 : ℝ) ≤ (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1) * C := by
  have h0 : (0 : ℝ) ≤ ‖∑ i, g i‖ ^ 2 := sq_nonneg _
  rw [norm_sum_sq_eq] at h0
  calc (0 : ℝ) ≤ ∑ i, ∑ j, (inner ℝ (g i) (g j) : ℝ) := h0
    _ ≤ ∑ _i : Fin n, (1 + ((n : ℝ) - 1) * C) :=
        Finset.sum_le_sum fun i _ => row_le g hg C hC i
    _ = (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1) * C := sum_const_row C

/-- **Strict Gram bound.** With `n ≥ 2` and all pairwise inner products *strictly* below `C`,
`0 < n + n(n−1)C`.  Strictness is what rules out the boundary configurations, e.g. three unit
vectors at exactly `120°`. -/
theorem gram_pairwise_lt {n : ℕ} (hn : 2 ≤ n) (g : Fin n → E) (hg : ∀ i, ‖g i‖ = 1) (C : ℝ)
    (hC : ∀ i j, i ≠ j → (inner ℝ (g i) (g j) : ℝ) < C) :
    (0 : ℝ) < (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1) * C := by
  have h0 : (0 : ℝ) ≤ ‖∑ i, g i‖ ^ 2 := sq_nonneg _
  rw [norm_sum_sq_eq] at h0
  have hpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  set i₀ : Fin n := ⟨0, hpos⟩ with hi₀
  have hmem : i₀ ∈ (univ : Finset (Fin n)) := mem_univ i₀
  have hne : (univ.erase i₀).Nonempty := by
    refine ⟨⟨1, lt_of_lt_of_le (by norm_num) hn⟩, ?_⟩
    simp [Finset.mem_erase, hi₀, Fin.ext_iff]
  have hrowlt : ∑ j, (inner ℝ (g i₀) (g j) : ℝ) < 1 + ((n : ℝ) - 1) * C := by
    have hsplit := Finset.add_sum_erase (univ : Finset (Fin n))
      (fun j => (inner ℝ (g i₀) (g j) : ℝ)) hmem
    have hdiag : (inner ℝ (g i₀) (g i₀) : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq, hg i₀]; norm_num
    have hoff : ∑ j ∈ univ.erase i₀, (inner ℝ (g i₀) (g j) : ℝ) < ((n : ℝ) - 1) * C := by
      calc ∑ j ∈ univ.erase i₀, (inner ℝ (g i₀) (g j) : ℝ)
          < ∑ _j ∈ univ.erase i₀, C :=
            Finset.sum_lt_sum_of_nonempty hne
              fun j hj => hC i₀ j (Ne.symm (Finset.ne_of_mem_erase hj))
        _ = ((n : ℝ) - 1) * C := by
            rw [Finset.sum_const, nsmul_eq_mul, card_erase_cast i₀]
    rw [← hsplit, hdiag]; linarith
  have hsum : ∑ i, ∑ j, (inner ℝ (g i) (g j) : ℝ) < ∑ _i : Fin n, (1 + ((n : ℝ) - 1) * C) :=
    Finset.sum_lt_sum (fun i _ => row_le g hg C (fun i j h => (hC i j h).le) i)
      ⟨i₀, mem_univ i₀, hrowlt⟩
  rw [sum_const_row C] at hsum
  linarith

/-! ## 2. `SEP` forces the inner products below `2t² − 1` -/

/-- `SEP` as written in Theorem 4.3.8: every pair of distinct faces subtends an angle exceeding
`2·arccos t + sep`, where the note takes `sep = 3πε/√(1−t²) ≥ 0`.  Angles are
`arccos ⟪gᵢ, gⱼ⟫`, the geodesic distance on the sphere. -/
def SEP {n : ℕ} (t sep : ℝ) (g : Fin n → E) : Prop :=
  ∀ i j, i ≠ j → 2 * Real.arccos t + sep < Real.arccos (inner ℝ (g i) (g j) : ℝ)

/-- Under `SEP` (with any `sep ≥ 0`) every pairwise inner product is `< 2t² − 1 = cos(2 arccos t)`:
the caps `cap(gᵢ,t)` are pairwise disjoint.  `sep` is simply discarded — keeping it would only
strengthen the conclusion. -/
theorem sep_inner_lt {n : ℕ} {t sep : ℝ} (ht : -1 ≤ t) (ht1 : t ≤ 1) (hsep : 0 ≤ sep)
    (g : Fin n → E) (hg : ∀ i, ‖g i‖ = 1) (h : SEP t sep g) :
    ∀ i j, i ≠ j → (inner ℝ (g i) (g j) : ℝ) < 2 * t ^ 2 - 1 := by
  intro i j hij
  set s : ℝ := inner ℝ (g i) (g j) with hs
  have habs : |s| ≤ 1 := by
    have := abs_real_inner_le_norm (g i) (g j)
    rwa [hg i, hg j, one_mul] at this
  have hs1 : -1 ≤ s := neg_le_of_abs_le habs
  have hs2 : s ≤ 1 := le_of_abs_le habs
  have hlt : 2 * Real.arccos t < Real.arccos s := by
    have := h i j hij; linarith
  have hnn : (0 : ℝ) ≤ 2 * Real.arccos t := by
    have := Real.arccos_nonneg t; linarith
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hnn (Real.arccos_le_pi s) hlt
  rwa [Real.cos_arccos hs1 hs2, Real.cos_two_mul, Real.cos_arccos ht ht1] at hcos

/-! ## 3. `SEP` is empty in the deployment regime -/

/-- **Main negative result.**  If `n + n(n−1)(2t²−1) ≤ 0` then no gallery of `n ≥ 2` unit vectors
satisfies `SEP`: the event has probability `0`, so `p_sep = 1` and Theorem 4.3.8's success
guarantee `1 − δ/2 − p_sep − n(n−1)Q_loc q` is negative, i.e. vacuous. -/
theorem sep_empty {n : ℕ} (hn : 2 ≤ n) {t sep : ℝ} (ht : -1 ≤ t) (ht1 : t ≤ 1) (hsep : 0 ≤ sep)
    (hbad : (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1) * (2 * t ^ 2 - 1) ≤ 0)
    (g : Fin n → E) (hg : ∀ i, ‖g i‖ = 1) : ¬ SEP t sep g := fun h => by
  have := gram_pairwise_lt hn g hg (2 * t ^ 2 - 1) (sep_inner_lt ht ht1 hsep g hg h)
  linarith

/-- **The `120°` obstruction.**  At a threshold `0 ≤ t ≤ 1/2` the caps have angular radius
`arccos t ≥ 60°`, so `SEP` demands pairwise angles `> 120°`, which at most two unit vectors can
achieve *in any dimension*.  Hence `SEP` is empty for every `n ≥ 3`.

At the draft's operating point `t = 0.2081` (`d_eff = 512`, `q = 10⁻⁶`), so this applies. -/
theorem sep_empty_of_thr_le_half {n : ℕ} (hn : 3 ≤ n) {t sep : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hsep : 0 ≤ sep) (g : Fin n → E) (hg : ∀ i, ‖g i‖ = 1) : ¬ SEP t sep g := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine sep_empty (le_trans (by norm_num) hn) (by linarith) (by linarith) hsep ?_ g hg
  have hC : 2 * t ^ 2 - 1 ≤ -(1 / 2) := by nlinarith
  have hnn : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hC hnn]

/-- **Quantitative form.**  If `SEP` is non-empty at gallery size `n ≥ 2` then
`0 < n + n(n−1)(2t²−1)`, i.e. `2(n−1)t² > n − 2`.  As `n → ∞` this forces `t > 1/√2`. -/
theorem sep_forces_thr {n : ℕ} (hn : 2 ≤ n) {t sep : ℝ} (ht : -1 ≤ t) (ht1 : t ≤ 1)
    (hsep : 0 ≤ sep) (g : Fin n → E) (hg : ∀ i, ‖g i‖ = 1) (h : SEP t sep g) :
    (0 : ℝ) < (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1) * (2 * t ^ 2 - 1) :=
  gram_pairwise_lt hn g hg (2 * t ^ 2 - 1) (sep_inner_lt ht ht1 hsep g hg h)

/-- For `n ≥ 3`, a non-empty `SEP` forces `t > 1/2`, hence a reach radius
`r_thr² = 2(1−t) < 1`. -/
theorem sep_forces_thr_gt_half {n : ℕ} (hn : 3 ≤ n) {t sep : ℝ} (ht : 0 ≤ t) (_ht1 : t ≤ 1)
    (hsep : 0 ≤ sep) (g : Fin n → E) (hg : ∀ i, ‖g i‖ = 1) (h : SEP t sep g) : 1 / 2 < t := by
  by_contra hcon
  push Not at hcon
  exact sep_empty_of_thr_le_half hn ht (by linarith) hsep g hg h

/-- **At the deployment gallery size `n ≥ 10⁴`**, a non-empty `SEP` forces `t > 0.7070`, hence a
reach radius `r_thr² = 2(1−t) < 0.586`.  Under the blind-prior cap bound
`μ₁ ≤ (2(1−t))^{(d_eff−1)/2}` (Lemma 3.1.1(a) + Proposition 3.2.1 of the draft, supplied here as
the labelled hypothesis `hmu` with `k = (d_eff−1)/2`) this gives `μ₁ ≤ 0.586^k`.

At `d_eff = 512`, `k = 255`: `μ₁ ≤ 0.586²⁵⁵ = 6.5·10⁻⁶⁰`, so Theorem 4.3.8's own search budget
`K = ⌈log(2n/δ)/q⌉` exceeds `10⁶⁰` queries.  `SEP` is satisfiable only where the theorem is
useless. -/
theorem sep_forces_tiny_reach {n : ℕ} (hn : 10 ^ 4 ≤ n) {t sep : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hsep : 0 ≤ sep) (g : Fin n → E) (hg : ∀ i, ‖g i‖ = 1) (h : SEP t sep g)
    {μ₁ : ℝ} {k : ℕ} (hmu : μ₁ ≤ (2 * (1 - t)) ^ k) :
    0.7070 < t ∧ 2 * (1 - t) < 0.586 ∧ μ₁ ≤ (0.586 : ℝ) ^ k := by
  have hn4 : (10 ^ 4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by norm_num at hn4 ⊢; linarith
  have key := sep_forces_thr (by omega) (by linarith) ht1 hsep g hg h
  set A : ℝ := 2 * t ^ 2 - 1 with hA
  -- `0 < n(1 + (n−1)A)` and `n > 0` give `(n−1)A > −1`
  have h1 : (-1 : ℝ) < ((n : ℝ) - 1) * A := by
    by_contra hc
    push Not at hc
    nlinarith [key, hnpos]
  -- hence `A > −1/9999`, so `t² > 0.49994`
  have hsq : 0.49994 < t ^ 2 := by
    by_cases hA0 : (0:ℝ) ≤ A
    · nlinarith [hA0]
    · push Not at hA0
      have hle : ((n : ℝ) - 1) * A ≤ 9999 * A := by nlinarith [hA0, hn4]
      nlinarith [h1, hle]
  have h2 : 0.7070 < t := by nlinarith [hsq, ht]
  have h3 : 2 * (1 - t) < 0.586 := by linarith
  exact ⟨h2, h3, hmu.trans (pow_le_pow_left₀ (by linarith) h3.le k)⟩

/-! ## 4. `SEP`'s role discharged: distinctness from the attribution test alone

Theorem 4.3.8 uses `SEP` only so that "a loud probe lies in one cap, and the attribution test
separates found from unfound faces".  The first half is what fails.  The second half — the
*conclusion* that the `m` outputs are `ε`-close to `m` **distinct** faces — needs no separation
at all: it follows from the attribution test being *sound* (`briefs/attacks/assumption-a.md`
§4.4). -/

/-- **Attribution soundness.**  If a unit probe `x` reaches the true face `g` (`⟪x,g⟫ > t`) and
`ĝ` is an `ε`-accurate estimate of `g`, then `x` fails the unattributed test `⟪x,ĝ⟫ ≤ t − ε`. -/
theorem attribution_sound {x g ĝ : E} {t ε : ℝ} (hx : ‖x‖ = 1) (hacc : ‖ĝ - g‖ ≤ ε)
    (hloud : t < (inner ℝ x g : ℝ)) : t - ε < (inner ℝ x ĝ : ℝ) := by
  have hsplit : (inner ℝ x ĝ : ℝ) = (inner ℝ x g : ℝ) + (inner ℝ x (ĝ - g) : ℝ) := by
    rw [inner_sub_right]; ring
  have hb : |(inner ℝ x (ĝ - g) : ℝ)| ≤ ε := by
    have hcs := abs_real_inner_le_norm x (ĝ - g)
    rw [hx, one_mul] at hcs
    exact hcs.trans hacc
  have := neg_le_of_abs_le hb
  rw [hsplit]; linarith

/-- **Distinctness without `SEP`.**  Suppose the attacker performs launches `a : Fin m` in order,
launch `a` starting from a unit probe `x a` that reaches face `f a`, every completed
localisation is `ε`-accurate, and each launch passed the unattributed test against all previously
output estimates.  Then the targets `f` are pairwise distinct — the conclusion `SEP` was invoked
for, with no separation hypothesis and no hypothesis on the gallery. -/
theorem launch_targets_injective {n m : ℕ} {t ε : ℝ} (g : Fin n → E) (x ĝ : Fin m → E)
    (f : Fin m → Fin n) (hx : ∀ a, ‖x a‖ = 1)
    (hacc : ∀ a, ‖ĝ a - g (f a)‖ ≤ ε)
    (hloud : ∀ a, t < (inner ℝ (x a) (g (f a)) : ℝ))
    (htest : ∀ a b, b < a → (inner ℝ (x a) (ĝ b) : ℝ) ≤ t - ε) :
    Function.Injective f := by
  have main : ∀ a b : Fin m, b < a → f b ≠ f a := by
    intro a b hba heq
    have hloud' : t < (inner ℝ (x a) (g (f b)) : ℝ) := by rw [heq]; exact hloud a
    have h1 := attribution_sound (hx a) (hacc b) hloud'
    have h2 := htest a b hba
    linarith
  intro a b hab
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd hab (main b a hlt)
  · exact heq
  · exact absurd hab.symm (main a b hgt)

end OracleBounds.Attacks.BlindMofN
