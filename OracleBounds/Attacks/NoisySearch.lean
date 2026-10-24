import OracleBounds.V6.Process
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Randomised posterior-median search under BSC(ρ) noise (`noisy-localise-proof.md`, Part I §1)

**Statements signed off by the administrator, 23 Sep 2026** (proof by subagent). Faithful to
Part I of `briefs/attacks/noisy-localise-proof.md` (the additive `Cap(ρ)` cost of a randomised
posterior-median search). Recorded limitations: bounds hold at a finite horizon `T`, uniformly in
`T` (the untruncated `E[N]` needs monotone convergence, not formalised); `thmN_d_budget` carries
the extra hypothesis `γ ≤ 1/2`, absent from the brief and genuinely needed; Theorem N(e) and the
geometric part (§§2–4 of the brief) are not formalised.

Formalisation of Lemmas N1–N3 and Theorem N of `briefs/attacks/noisy-localise-proof.md`: the
Burnashev–Zigangirov randomised posterior-median rule against a `BSC(ρ)` comparison oracle has
per-query log-odds drift at least `Cap(ρ) = log 2 − h(ρ)` and per-query MGF at most
`φ(λ) = 2^{−λ}(ρ^{1−λ} + (1−ρ)^{1−λ})`, *for every* true cell (no Bayes averaging).

## Model

`M ≥ 2` cells indexed by `ℕ` (a posterior is a function `q : ℕ → ℝ` supported on `range M`;
`PostInv M q` is the invariant "strictly positive on `range M`, zero off it, total mass `1`").  The
oracle is queried at a *cut* `c : ℕ`, separating cells `{i < c}` from `{i ≥ c}`; it answers
`true` ("the true cell is left of the cut") with probability `1 − ρ` if `x < c` and `ρ`
otherwise, independently at each query.

Each query consumes **two** rounds of the repo's adaptive one-bit process
`OracleBounds.V6.val`, exactly as `Attacks.Sieve` runs the sieve along a transcript:

* a *coin* round (`phase = false`), whose bit picks the left endpoint of the median cell with
  probability `α` (`alph`) and the right endpoint with probability `1 − α`;
* an *answer* round (`phase = true`), whose bit is the (noisy) oracle answer.

The coin round is the randomisation of §1.2 of the brief — it is what makes `E[a | F_n] = 1/2`
hold exactly — and the transcript alphabet of `val` is binary, so it is spent as its own round.
A horizon of `2 * T` rounds is therefore `T` queries.  As in `Attacks/Sieve.lean`, **every bound
is stated at a finite horizon `T`, uniformly in `T`**; no stopping-time or limit theory is used.

## What is proved

* `step_odds` (**Lemma N1**) — one Bayes step multiplies the odds `W = (1−p(x*))/p(x*)` by
  `mulHit ρ s = ((1−ρ) − sθ)/(1−ρ)` (probability `1 − ρ`) or by
  `mulMiss ρ s = (ρ + sθ)/ρ` (probability `ρ`), `θ = 1 − 2ρ`, `s` the separated fraction
  (`sepFrac`).  The normaliser cancels, so the factor depends on the posterior only through `s`.
  `step_logOdds` is the same in the brief's additive form `ΔL = Δ^±(s)`, and
  `abs_logOdds_incr_le` is `|ΔL| ≤ log((1−ρ)/ρ)`.
* `psi_zero`, `psi_half`, `psi_one`, `psi_mono`, `psi_convexOn`, `psi_tangent` and `Gmgf_half`,
  `Gmgf_anti`, `Gmgf_concaveOn`, `Gmgf_tangent` (**Lemma N2**) — `ψ(0) = 0`, `ψ(1/2) = Cap ρ`,
  `ψ(1) = KL_ρ`, `ψ` nondecreasing and convex; `G(1/2;λ) = φ(λ)`, `G(·;λ)` nonincreasing and
  concave.  The two `tangent` lemmas are the quantitative form actually used: a supporting line
  at `s = 1/2` with the right sign of slope, which replaces "Jensen + monotonicity" by a single
  affine bound.
* `median_sep` (**Lemma N3**) — `E[s | F_n] ≥ 1/2`, in the division-free form
  `α·F₁ + (1−α)·F₂ ≥ (1 − q x)/2`; `sepFrac_avg` is the quotient form.  The hard case reduces to
  `α(1−α) ≤ 1/4`, exactly as in the brief.
* `thmN_a`, `thmN_b` (**Theorem N(a),(b)**) — the per-query drift `E[ΔL | F_n] ≥ Cap(ρ)` and MGF
  `E[e^{−λΔL} | F_n] ≤ φ(λ)`, for *every* reachable state and every true cell `x < M` (no Bayes
  averaging).  `E2` is the one-query (two-round) conditional expectation.
* `thmN_c` (**Theorem N(c)**) — after `T` queries, `P[some cell ≠ x* carries at least as much
  mass as x*] ≤ (M−1)^λ φ(λ)^T`.
* `odds_mart`, `thmN_d_error`, `thmN_d_budget` (**Theorem N(d)**) — `W_n` is a martingale with
  `W_0 = M − 1`; the rule "stop as soon as some cell reaches mass `1 − γ`" (the `haltAt` freeze)
  outputs a wrong cell with probability `≤ (M−1)γ/(1−γ)`; and
  `Cap(ρ)·E[N ∧ T] ≤ log(M−1) + log((1−γ)/γ) + log((1−ρ)/ρ)` at every horizon `T`, where `N` is
  the number of completed queries (the `k` field of the state).

## Hypotheses

All explicit: `2 ≤ M`, `0 < ρ < 1/2`, `x < M`, `0 < λ < 1` (for the MGF branch),
`0 < γ < 1` (for `thmN_d_error`) and additionally `γ ≤ 1/2` for `thmN_d_budget` — the latter
because the budget's pathwise ceiling starts from `L_0 = −log(M−1) ≤ log((1−γ)/γ)`, which needs
`log((1−γ)/γ) ≥ 0`.  Nothing about martingale theory, optional stopping or Ville's inequality is
assumed: `val_mart`, `val_super2` and `val_sub2` are proved from the process recursion, exactly
as in `Attacks/Sieve.lean`.

## What is *not* formalised

Theorem N(e) (the tail `P[N > n] ≤ ((M−1)(1−γ)/γ)^λ φ(λ)^n`), and the `T → ∞` limits: the note's
untruncated `E[N]` and the a.s. finiteness of the stopping time follow from `thmN_d_budget` by
monotone convergence, which is not formalised.  §§2–4 of the brief (the geometric reduction to a
monotone threshold on a circle, Algorithm L2ρ and its budgets) are not formalised here; §1 is
independent of them.

No `sorry`s, no new axioms.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.Attacks

open Finset OracleBounds.V6

namespace NoisySearch

/-! ## §0. The scalar functions of Lemmas N1–N2 -/

/-- `Cap(ρ) = log 2 − h(ρ)`, the per-query drift. -/
noncomputable def Cap (ρ : ℝ) : ℝ := Real.log 2 + ρ * Real.log ρ + (1 - ρ) * Real.log (1 - ρ)

/-- `KL_ρ = (1−2ρ) log((1−ρ)/ρ)`. -/
noncomputable def KLrho (ρ : ℝ) : ℝ := (1 - 2 * ρ) * Real.log ((1 - ρ) / ρ)

/-- `φ(λ) = 2^{−λ}(ρ^{1−λ} + (1−ρ)^{1−λ})`. -/
noncomputable def phi (ρ lam : ℝ) : ℝ :=
  (2 : ℝ) ^ (-lam) * (ρ ^ (1 - lam) + (1 - ρ) ^ (1 - lam))

/-- `e^{−Δ⁺(s)} = ((1−ρ) − sθ)/(1−ρ)`: the factor the odds pick up on a correct answer. -/
noncomputable def mulHit (ρ s : ℝ) : ℝ := ((1 - ρ) - s * (1 - 2 * ρ)) / (1 - ρ)

/-- `e^{−Δ⁻(s)} = (ρ + sθ)/ρ`: the factor the odds pick up on a wrong answer. -/
noncomputable def mulMiss (ρ s : ℝ) : ℝ := (ρ + s * (1 - 2 * ρ)) / ρ

/-- `ψ(s) = (1−ρ)Δ⁺(s) + ρΔ⁻(s)`, the conditional drift of the log-odds given `s`. -/
noncomputable def psi (ρ s : ℝ) : ℝ :=
  -((1 - ρ) * Real.log (mulHit ρ s) + ρ * Real.log (mulMiss ρ s))

/-- `G(s;λ) = (1−ρ)e^{−λΔ⁺(s)} + ρ e^{−λΔ⁻(s)}`. -/
noncomputable def Gmgf (ρ lam s : ℝ) : ℝ :=
  (1 - ρ) * mulHit ρ s ^ lam + ρ * mulMiss ρ s ^ lam

section Scalar

variable {ρ lam s : ℝ}

/-! ### rpow housekeeping -/

lemma rpow_sub_one_mul {w : ℝ} (hw : 0 < w) : w ^ (lam - 1) * w = w ^ lam := by
  have h := Real.rpow_add hw (lam - 1) 1
  rw [Real.rpow_one, show lam - 1 + 1 = lam by ring] at h
  exact h.symm

lemma mul_div_rpow {w u : ℝ} (hw : 0 < w) (hu : 0 ≤ u) :
    w * (u / w) ^ lam = w ^ (1 - lam) * u ^ lam := by
  have hne : w ^ lam ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hw _)
  rw [Real.div_rpow hu hw.le, Real.rpow_sub hw, Real.rpow_one]
  field_simp

lemma half_rpow (t : ℝ) : ((1 : ℝ) / 2) ^ t = (2 : ℝ) ^ (-t) := by
  rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]

lemma rpow_quot {w v : ℝ} (hw : 0 < w) (hv : 0 < v) :
    w ^ (1 - lam) * v ^ (lam - 1) = (w / v) ^ (1 - lam) := by
  have hne : v ^ (1 - lam) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hv _)
  rw [Real.div_rpow hw.le hv.le, show lam - 1 = -(1 - lam) by ring, Real.rpow_neg hv.le]
  field_simp

/-! ### Positivity and range of the two multipliers -/

lemma hitNum_pos (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hs1 : s ≤ 1) :
    0 < (1 - ρ) - s * (1 - 2 * ρ) := by nlinarith

lemma missNum_pos (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hs0 : 0 ≤ s) :
    0 < ρ + s * (1 - 2 * ρ) := by nlinarith

lemma mulHit_pos (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hs1 : s ≤ 1) : 0 < mulHit ρ s :=
  div_pos (hitNum_pos hρ0 hρ1 hs1) (by linarith)

lemma mulMiss_pos (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hs0 : 0 ≤ s) : 0 < mulMiss ρ s :=
  div_pos (missNum_pos hρ0 hρ1 hs0) hρ0

/-- `mulHit ≤ 1`: a correct answer never increases the odds against `x*`. -/
lemma mulHit_le_one (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hs0 : 0 ≤ s) : mulHit ρ s ≤ 1 := by
  rw [mulHit, div_le_one (by linarith)]; nlinarith

/-- `mulHit ≥ ρ/(1−ρ)`: half of `|ΔL| ≤ log((1−ρ)/ρ)`. -/
lemma mulHit_ge (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hs1 : s ≤ 1) : ρ / (1 - ρ) ≤ mulHit ρ s := by
  rw [mulHit, div_le_div_iff_of_pos_right (by linarith)]; nlinarith

lemma mulMiss_ge_one (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hs0 : 0 ≤ s) : 1 ≤ mulMiss ρ s := by
  rw [mulMiss, le_div_iff₀ hρ0]; nlinarith

/-- `mulMiss ≤ (1−ρ)/ρ`: the other half of `|ΔL| ≤ log((1−ρ)/ρ)`. -/
lemma mulMiss_le (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hs1 : s ≤ 1) :
    mulMiss ρ s ≤ (1 - ρ) / ρ := by
  rw [mulMiss, div_le_div_iff_of_pos_right hρ0]; nlinarith

/-- The two factors average to `1`: this is the martingale property of the odds (Theorem N(d)). -/
lemma mul_avg (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    (1 - ρ) * mulHit ρ s + ρ * mulMiss ρ s = 1 := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := by linarith
  have h2 : ρ ≠ 0 := ne_of_gt hρ0
  rw [mulHit, mulMiss]
  field_simp
  ring

/-! ### Two tangent-line inequalities used throughout -/

/-- `log y ≤ log y₀ + (y − y₀)/y₀`. -/
lemma log_tangent {y y₀ : ℝ} (hy : 0 < y) (hy₀ : 0 < y₀) :
    Real.log y ≤ Real.log y₀ + (y - y₀) / y₀ := by
  have h := Real.log_le_sub_one_of_pos (x := y / y₀) (by positivity)
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hy₀)] at h
  have he : y / y₀ - 1 = (y - y₀) / y₀ := by field_simp
  rw [he] at h
  linarith

/-- `y^λ ≤ y₀^λ + λ y₀^{λ−1}(y − y₀)` for `0 ≤ λ ≤ 1`: the supporting line of `x ↦ x^λ`. -/
lemma rpow_tangent {y y₀ : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hy : 0 ≤ y) (hy₀ : 0 < y₀) :
    y ^ lam ≤ y₀ ^ lam + lam * y₀ ^ (lam - 1) * (y - y₀) := by
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hlam0 (by linarith : (0:ℝ) ≤ 1 - lam)
    hy hy₀.le (by ring)
  have hpos : (0 : ℝ) < y₀ ^ (lam - 1) := Real.rpow_pos_of_pos hy₀ _
  have hmul := mul_le_mul_of_nonneg_right hamgm hpos.le
  have e1 : y ^ lam * y₀ ^ (1 - lam) * y₀ ^ (lam - 1) = y ^ lam := by
    rw [mul_assoc, ← Real.rpow_add hy₀]
    norm_num
  have e2 : y₀ ^ (lam - 1) * y₀ = y₀ ^ lam := rpow_sub_one_mul hy₀
  rw [e1] at hmul
  calc y ^ lam ≤ (lam * y + (1 - lam) * y₀) * y₀ ^ (lam - 1) := hmul
    _ = lam * y₀ ^ (lam - 1) * y + (1 - lam) * (y₀ ^ (lam - 1) * y₀) := by ring
    _ = y₀ ^ lam + lam * y₀ ^ (lam - 1) * (y - y₀) := by
        rw [e2, ← e2]; ring

/-! ### Lemma N2: the two shape facts -/

/-- `ψ` with the normalisers pulled out. -/
lemma psi_eq (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    psi ρ s = -((1 - ρ) * Real.log ((1 - ρ) - s * (1 - 2 * ρ))
        + ρ * Real.log (ρ + s * (1 - 2 * ρ)))
      + ((1 - ρ) * Real.log (1 - ρ) + ρ * Real.log ρ) := by
  have hb : (0 : ℝ) < 1 - ρ := by linarith
  rw [psi, mulHit, mulMiss, Real.log_div (ne_of_gt (hitNum_pos hρ0 hρ1 hs1)) (ne_of_gt hb),
    Real.log_div (ne_of_gt (missNum_pos hρ0 hρ1 hs0)) (ne_of_gt hρ0)]
  ring

/-- `G` with the normalisers pulled out: `G(s;λ) = (1−ρ)^{1−λ}y^λ + ρ^{1−λ}z^λ`. -/
lemma Gmgf_eq (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Gmgf ρ lam s = (1 - ρ) ^ (1 - lam) * ((1 - ρ) - s * (1 - 2 * ρ)) ^ lam
      + ρ ^ (1 - lam) * (ρ + s * (1 - 2 * ρ)) ^ lam := by
  rw [Gmgf, mulHit, mulMiss, mul_div_rpow (by linarith : (0:ℝ) < 1 - ρ)
    (hitNum_pos hρ0 hρ1 hs1).le, mul_div_rpow hρ0 (missNum_pos hρ0 hρ1 hs0).le]

lemma psi_zero (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) : psi ρ 0 = 0 := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := by linarith
  have e2 : mulHit ρ 0 = 1 := by rw [mulHit]; field_simp; ring
  have e3 : mulMiss ρ 0 = 1 := by rw [mulMiss]; field_simp; ring
  rw [psi, e2, e3]; simp

lemma psi_one (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) : psi ρ 1 = KLrho ρ := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := by linarith
  have h2 : mulHit ρ 1 = ρ / (1 - ρ) := by rw [mulHit]; ring_nf
  have h3 : mulMiss ρ 1 = (1 - ρ) / ρ := by rw [mulMiss]; ring_nf
  rw [psi, h2, h3, Real.log_div (ne_of_gt hρ0) h1, KLrho, Real.log_div h1 (ne_of_gt hρ0)]
  ring

lemma psi_half (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) : psi ρ (1 / 2) = Cap ρ := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := by linarith
  have h2 : mulHit ρ (1 / 2) = (1 / 2) / (1 - ρ) := by rw [mulHit]; ring_nf
  have h3 : mulMiss ρ (1 / 2) = (1 / 2) / ρ := by rw [mulMiss]; ring_nf
  have hlog2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [psi, h2, h3, Real.log_div (by norm_num) h1, Real.log_div (by norm_num) (ne_of_gt hρ0), Cap,
    hlog2]
  ring

lemma Gmgf_half (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) : Gmgf ρ lam (1 / 2) = phi ρ lam := by
  have h1 : (0 : ℝ) < 1 - ρ := by linarith
  rw [Gmgf_eq hρ0 hρ1 (by norm_num) (by norm_num)]
  have ey : (1 - ρ) - (1 / 2 : ℝ) * (1 - 2 * ρ) = 1 / 2 := by ring
  have ez : ρ + (1 / 2 : ℝ) * (1 - 2 * ρ) = 1 / 2 := by ring
  rw [ey, ez, half_rpow, phi]
  ring

/-- **Lemma N2(i), quantitative:** `ψ` lies above its supporting line at `s = 1/2`, whose slope
`2θ²` is nonnegative.  With `median_sep` this is Theorem N(a). -/
lemma psi_tangent (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Cap ρ + (1 - 2 * ρ) ^ 2 * (2 * s - 1) ≤ psi ρ s := by
  have h1 : (0 : ℝ) < 1 - ρ := by linarith
  have hy : 0 < (1 - ρ) - s * (1 - 2 * ρ) := hitNum_pos hρ0 hρ1 hs1
  have hz : 0 < ρ + s * (1 - 2 * ρ) := missNum_pos hρ0 hρ1 hs0
  have ty := log_tangent hy (show (0:ℝ) < 1/2 by norm_num)
  have tz := log_tangent hz (show (0:ℝ) < 1/2 by norm_num)
  have hlog2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [hlog2] at ty tz
  rw [psi_eq hρ0 hρ1 hs0 hs1, Cap]
  nlinarith [mul_le_mul_of_nonneg_left ty h1.le, mul_le_mul_of_nonneg_left tz hρ0.le]

/-- The (nonnegative) slope of the supporting line of `G` at `s = 1/2`, up to sign. -/
noncomputable def Ktan (ρ lam : ℝ) : ℝ :=
  (2 : ℝ) ^ (1 - lam) * lam * (1 - 2 * ρ) * ((1 - ρ) ^ (1 - lam) - ρ ^ (1 - lam))

lemma Ktan_nonneg (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    0 ≤ Ktan ρ lam := by
  have hab : ρ ^ (1 - lam) ≤ (1 - ρ) ^ (1 - lam) :=
    Real.rpow_le_rpow hρ0.le (by linarith) (by linarith)
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (1 - lam) := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : (0 : ℝ) ≤ 1 - 2 * ρ := by linarith
  unfold Ktan
  have : (0:ℝ) ≤ (1 - ρ) ^ (1 - lam) - ρ ^ (1 - lam) := by linarith
  positivity

/-- **Lemma N2(ii), quantitative:** `G(·;λ)` lies below its supporting line at `s = 1/2`, whose
slope `−Ktan` is nonpositive.  With `median_sep` this is Theorem N(b). -/
lemma Gmgf_tangent (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Gmgf ρ lam s ≤ phi ρ lam + Ktan ρ lam * (1 / 2 - s) := by
  have h1 : (0 : ℝ) < 1 - ρ := by linarith
  have hy : 0 < (1 - ρ) - s * (1 - 2 * ρ) := hitNum_pos hρ0 hρ1 hs1
  have hz : 0 < ρ + s * (1 - 2 * ρ) := missNum_pos hρ0 hρ1 hs0
  have ty := rpow_tangent (lam := lam) hlam0 hlam1 hy.le (show (0:ℝ) < 1/2 by norm_num)
  have tz := rpow_tangent (lam := lam) hlam0 hlam1 hz.le (show (0:ℝ) < 1/2 by norm_num)
  have hh1 : ((1:ℝ)/2) ^ (lam - 1) = (2:ℝ) ^ (1 - lam) := by
    rw [half_rpow, show -(lam - 1) = 1 - lam by ring]
  have hh2 : ((1:ℝ)/2) ^ lam = (2:ℝ) ^ (-lam) := half_rpow lam
  rw [hh1, hh2] at ty tz
  have ha0 : (0:ℝ) ≤ (1 - ρ) ^ (1 - lam) := Real.rpow_nonneg h1.le _
  have hb0 : (0:ℝ) ≤ ρ ^ (1 - lam) := Real.rpow_nonneg hρ0.le _
  rw [Gmgf_eq hρ0 hρ1 hs0 hs1, phi, Ktan]
  nlinarith [mul_le_mul_of_nonneg_left ty ha0, mul_le_mul_of_nonneg_left tz hb0,
    Real.rpow_pos_of_pos (show (0:ℝ) < 2 by norm_num) (1 - lam),
    Real.rpow_pos_of_pos (show (0:ℝ) < 2 by norm_num) (-lam)]

/-- `ψ` is nondecreasing on `[0,1]` (Lemma N2(i)). -/
lemma psi_mono (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) {s₁ s₂ : ℝ} (h0 : 0 ≤ s₁) (h12 : s₁ ≤ s₂)
    (h1 : s₂ ≤ 1) : psi ρ s₁ ≤ psi ρ s₂ := by
  have hb : (0 : ℝ) < 1 - ρ := by linarith
  have hy1 : 0 < (1 - ρ) - s₁ * (1 - 2 * ρ) := hitNum_pos hρ0 hρ1 (by linarith)
  have hy2 : 0 < (1 - ρ) - s₂ * (1 - 2 * ρ) := hitNum_pos hρ0 hρ1 h1
  have hz1 : 0 < ρ + s₁ * (1 - 2 * ρ) := missNum_pos hρ0 hρ1 h0
  have hz2 : 0 < ρ + s₂ * (1 - 2 * ρ) := missNum_pos hρ0 hρ1 (by linarith)
  rw [psi_eq hρ0 hρ1 h0 (by linarith), psi_eq hρ0 hρ1 (by linarith) h1]
  have ty := log_tangent hy2 hy1
  have tz := log_tangent hz2 hz1
  set D := (s₂ - s₁) * (1 - 2 * ρ) with hD
  have hDnn : (0:ℝ) ≤ D := by rw [hD]; nlinarith
  have e1 : (1 - ρ) - s₂ * (1 - 2 * ρ) - ((1 - ρ) - s₁ * (1 - 2 * ρ)) = -D := by rw [hD]; ring
  have e2 : ρ + s₂ * (1 - 2 * ρ) - (ρ + s₁ * (1 - 2 * ρ)) = D := by rw [hD]; ring
  rw [e1] at ty
  rw [e2] at tz
  have hd1 : -D / ((1 - ρ) - s₁ * (1 - 2 * ρ)) = -(D / ((1 - ρ) - s₁ * (1 - 2 * ρ))) := by ring
  rw [hd1] at ty
  have hfrac : ρ * (D / (ρ + s₁ * (1 - 2 * ρ)))
      ≤ (1 - ρ) * (D / ((1 - ρ) - s₁ * (1 - 2 * ρ))) := by
    have hkey : ρ * ((1 - ρ) - s₁ * (1 - 2 * ρ)) ≤ (1 - ρ) * (ρ + s₁ * (1 - 2 * ρ)) := by
      nlinarith
    rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hkey hDnn]
  nlinarith [mul_le_mul_of_nonneg_left ty hb.le, mul_le_mul_of_nonneg_left tz hρ0.le, hfrac]

/-- `G(·;λ)` is nonincreasing on `[0,1]` (Lemma N2(ii)). -/
lemma Gmgf_anti (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    {s₁ s₂ : ℝ} (h0 : 0 ≤ s₁) (h12 : s₁ ≤ s₂) (h1 : s₂ ≤ 1) :
    Gmgf ρ lam s₂ ≤ Gmgf ρ lam s₁ := by
  have hb : (0 : ℝ) < 1 - ρ := by linarith
  have hy1 : 0 < (1 - ρ) - s₁ * (1 - 2 * ρ) := hitNum_pos hρ0 hρ1 (by linarith)
  have hy2 : 0 < (1 - ρ) - s₂ * (1 - 2 * ρ) := hitNum_pos hρ0 hρ1 h1
  have hz1 : 0 < ρ + s₁ * (1 - 2 * ρ) := missNum_pos hρ0 hρ1 h0
  have hz2 : 0 < ρ + s₂ * (1 - 2 * ρ) := missNum_pos hρ0 hρ1 (by linarith)
  rw [Gmgf_eq hρ0 hρ1 h0 (by linarith), Gmgf_eq hρ0 hρ1 (by linarith) h1]
  have ty := rpow_tangent (lam := lam) hlam0 hlam1 hy2.le hy1
  have tz := rpow_tangent (lam := lam) hlam0 hlam1 hz2.le hz1
  have ha0 : (0:ℝ) ≤ (1 - ρ) ^ (1 - lam) := Real.rpow_nonneg hb.le _
  have hb0 : (0:ℝ) ≤ ρ ^ (1 - lam) := Real.rpow_nonneg hρ0.le _
  set D := (s₂ - s₁) * (1 - 2 * ρ) with hD
  have hDnn : (0:ℝ) ≤ D := by rw [hD]; nlinarith
  have e1 : (1 - ρ) - s₂ * (1 - 2 * ρ) - ((1 - ρ) - s₁ * (1 - 2 * ρ)) = -D := by rw [hD]; ring
  have e2 : ρ + s₂ * (1 - 2 * ρ) - (ρ + s₁ * (1 - 2 * ρ)) = D := by rw [hD]; ring
  rw [e1] at ty
  rw [e2] at tz
  -- key sign: `ρ^{1−λ}z₁^{λ−1} ≤ (1−ρ)^{1−λ}y₁^{λ−1}`
  have hkey : ρ ^ (1 - lam) * (ρ + s₁ * (1 - 2 * ρ)) ^ (lam - 1)
      ≤ (1 - ρ) ^ (1 - lam) * ((1 - ρ) - s₁ * (1 - 2 * ρ)) ^ (lam - 1) := by
    rw [rpow_quot hρ0 hz1, rpow_quot hb hy1]
    refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
    rw [div_le_div_iff₀ hz1 hy1]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left ty ha0, mul_le_mul_of_nonneg_left tz hb0,
    mul_le_mul_of_nonneg_right hkey (mul_nonneg hlam0 hDnn)]

/-- `ψ(·)` is convex on `[0,1]` (Lemma N2(i)). -/
lemma psi_convexOn (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (psi ρ) := by
  have hb : (0 : ℝ) < 1 - ρ := by linarith
  refine ⟨convex_Icc _ _, ?_⟩
  intro t₁ ht₁ t₂ ht₂ u v hu hv huv
  have hy : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → 0 < (1 - ρ) - t * (1 - 2 * ρ) :=
    fun t ht => hitNum_pos hρ0 hρ1 ht.2
  have hz : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → 0 < ρ + t * (1 - 2 * ρ) :=
    fun t ht => missNum_pos hρ0 hρ1 ht.1
  have hmem : u * t₁ + v * t₂ ∈ Set.Icc (0:ℝ) 1 := by
    have := (convex_Icc (0:ℝ) 1) ht₁ ht₂ hu hv huv
    simpa using this
  have hlogy : u * Real.log ((1 - ρ) - t₁ * (1 - 2 * ρ)) + v * Real.log ((1 - ρ) - t₂ * (1 - 2 * ρ))
      ≤ Real.log ((1 - ρ) - (u * t₁ + v * t₂) * (1 - 2 * ρ)) := by
    have hc := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.2 (hy t₁ ht₁))
      (Set.mem_Ioi.2 (hy t₂ ht₂)) hu hv huv
    simp only [smul_eq_mul] at hc
    have heq : u * ((1 - ρ) - t₁ * (1 - 2 * ρ)) + v * ((1 - ρ) - t₂ * (1 - 2 * ρ))
        = (1 - ρ) - (u * t₁ + v * t₂) * (1 - 2 * ρ) := by nlinarith [huv]
    rwa [heq] at hc
  have hlogz : u * Real.log (ρ + t₁ * (1 - 2 * ρ)) + v * Real.log (ρ + t₂ * (1 - 2 * ρ))
      ≤ Real.log (ρ + (u * t₁ + v * t₂) * (1 - 2 * ρ)) := by
    have hc := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.2 (hz t₁ ht₁))
      (Set.mem_Ioi.2 (hz t₂ ht₂)) hu hv huv
    simp only [smul_eq_mul] at hc
    have heq : u * (ρ + t₁ * (1 - 2 * ρ)) + v * (ρ + t₂ * (1 - 2 * ρ))
        = ρ + (u * t₁ + v * t₂) * (1 - 2 * ρ) := by nlinarith [huv]
    rwa [heq] at hc
  have expand : u * psi ρ t₁ + v * psi ρ t₂ - psi ρ (u * t₁ + v * t₂)
      = (1 - ρ) * (Real.log ((1 - ρ) - (u * t₁ + v * t₂) * (1 - 2 * ρ))
          - (u * Real.log ((1 - ρ) - t₁ * (1 - 2 * ρ)) + v * Real.log ((1 - ρ) - t₂ * (1 - 2 * ρ))))
        + ρ * (Real.log (ρ + (u * t₁ + v * t₂) * (1 - 2 * ρ))
          - (u * Real.log (ρ + t₁ * (1 - 2 * ρ)) + v * Real.log (ρ + t₂ * (1 - 2 * ρ))))
        + (u + v - 1) * ((1 - ρ) * Real.log (1 - ρ) + ρ * Real.log ρ) := by
    rw [psi_eq hρ0 hρ1 ht₁.1 ht₁.2, psi_eq hρ0 hρ1 ht₂.1 ht₂.2, psi_eq hρ0 hρ1 hmem.1 hmem.2]
    ring
  rw [huv] at expand
  simp only [smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hlogy hb.le, mul_le_mul_of_nonneg_left hlogz hρ0.le,
    expand]

/-- `G(·;λ)` is concave on `[0,1]` (Lemma N2(ii)). -/
lemma Gmgf_concaveOn (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    ConcaveOn ℝ (Set.Icc (0:ℝ) 1) (Gmgf ρ lam) := by
  have hb : (0 : ℝ) < 1 - ρ := by linarith
  refine ⟨convex_Icc _ _, ?_⟩
  intro t₁ ht₁ t₂ ht₂ u v hu hv huv
  have hmH : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → 0 ≤ mulHit ρ t :=
    fun t ht => (mulHit_pos hρ0 hρ1 ht.2).le
  have hmM : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → 0 ≤ mulMiss ρ t :=
    fun t ht => (mulMiss_pos hρ0 hρ1 ht.1).le
  have hmem : u * t₁ + v * t₂ ∈ Set.Icc (0:ℝ) 1 := by
    have := (convex_Icc (0:ℝ) 1) ht₁ ht₂ hu hv huv
    simpa using this
  have haffH : mulHit ρ (u * t₁ + v * t₂) = u * mulHit ρ t₁ + v * mulHit ρ t₂ := by
    have hsum : u * mulHit ρ t₁ + v * mulHit ρ t₂
        = (u * ((1 - ρ) - t₁ * (1 - 2 * ρ)) + v * ((1 - ρ) - t₂ * (1 - 2 * ρ))) / (1 - ρ) := by
      rw [mulHit, mulHit]; ring
    rw [hsum, mulHit]
    congr 1
    linear_combination (ρ - 1) * huv
  have haffM : mulMiss ρ (u * t₁ + v * t₂) = u * mulMiss ρ t₁ + v * mulMiss ρ t₂ := by
    have hsum : u * mulMiss ρ t₁ + v * mulMiss ρ t₂
        = (u * (ρ + t₁ * (1 - 2 * ρ)) + v * (ρ + t₂ * (1 - 2 * ρ))) / ρ := by
      rw [mulMiss, mulMiss]; ring
    rw [hsum, mulMiss]
    congr 1
    linear_combination (-ρ) * huv
  have cc := Real.concaveOn_rpow (p := lam) hlam0 hlam1
  have hc1 := cc.2 (Set.mem_Ici.2 (hmH t₁ ht₁)) (Set.mem_Ici.2 (hmH t₂ ht₂)) hu hv huv
  have hc2 := cc.2 (Set.mem_Ici.2 (hmM t₁ ht₁)) (Set.mem_Ici.2 (hmM t₂ ht₂)) hu hv huv
  simp only [smul_eq_mul] at hc1 hc2
  simp only [smul_eq_mul, Gmgf, haffH, haffM]
  nlinarith [mul_le_mul_of_nonneg_left hc1 hb.le, mul_le_mul_of_nonneg_left hc2 hρ0.le]

end Scalar

/-! ## §1. Posteriors, the Bayes step (Lemma N1) and the median rule (Lemma N3) -/

/-- Cumulative posterior mass strictly left of the cut `c`. -/
noncomputable def cum (q : ℕ → ℝ) (c : ℕ) : ℝ := ∑ i ∈ Finset.range c, q i

/-- A posterior on the `M` cells: strictly positive on `range M`, zero off it, total mass `1`.
Strict positivity is preserved by the Bayes update (the likelihoods `ρ`, `1−ρ` are positive) and
is what makes the log-odds `L_n` finite. -/
structure PostInv (M : ℕ) (q : ℕ → ℝ) : Prop where
  pos : ∀ i, i < M → 0 < q i
  van : ∀ i, M ≤ i → q i = 0
  total : ∑ i ∈ Finset.range M, q i = 1

namespace PostInv

variable {M : ℕ} {q : ℕ → ℝ}

lemma nonneg (hq : PostInv M q) (i : ℕ) : 0 ≤ q i := by
  rcases lt_or_ge i M with h | h
  · exact (hq.pos i h).le
  · exact (hq.van i h).ge

lemma cum_nonneg (hq : PostInv M q) (c : ℕ) : 0 ≤ cum q c :=
  Finset.sum_nonneg fun i _ => hq.nonneg i

lemma cum_mono (hq : PostInv M q) {c c' : ℕ} (h : c ≤ c') : cum q c ≤ cum q c' := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hq.nonneg i
  intro i hi
  simp only [Finset.mem_range] at hi ⊢
  omega

lemma cum_M (hq : PostInv M q) : cum q M = 1 := hq.total

lemma cum_le_one (hq : PostInv M q) {c : ℕ} (h : c ≤ M) : cum q c ≤ 1 := by
  have := hq.cum_mono h; rwa [hq.cum_M] at this

lemma cum_succ (q : ℕ → ℝ) (c : ℕ) : cum q (c + 1) = cum q c + q c :=
  Finset.sum_range_succ q c

lemma single_le_cum (hq : PostInv M q) {x c : ℕ} (h : x < c) : q x ≤ cum q c := by
  exact Finset.single_le_sum (f := q) (fun i _ => hq.nonneg i) (Finset.mem_range.2 h)

/-- `q x + cum q c ≤ 1` when `x` is at or to the right of the cut. -/
lemma cum_add_single_le (hq : PostInv M q) {x c : ℕ} (hx : x < M) (hxc : c ≤ x) :
    cum q c + q x ≤ 1 := by
  have hsub : insert x (Finset.range c) ⊆ Finset.range M := by
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact Finset.mem_range.2 hx
    · exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) (le_trans hxc hx.le))
  have hnot : x ∉ Finset.range c := by simp only [Finset.mem_range]; omega
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hq.nonneg i)
  rw [Finset.sum_insert hnot, hq.total] at this
  rw [cum]; linarith

lemma pair_le_one (hq : PostInv M q) {i j : ℕ} (hij : i ≠ j) (hi : i < M) (hj : j < M) :
    q i + q j ≤ 1 := by
  have hsub : ({i, j} : Finset ℕ) ⊆ Finset.range M := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> exact Finset.mem_range.2 (by assumption)
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hq.nonneg k)
  rw [Finset.sum_pair hij, hq.total] at this
  linarith

lemma qx_lt_one (hq : PostInv M q) (hM : 2 ≤ M) {x : ℕ} (hx : x < M) : q x < 1 := by
  set y := if x = 0 then 1 else 0 with hy
  have hyM : y < M := by rw [hy]; split <;> omega
  have hyx : y ≠ x := by rw [hy]; split <;> omega
  have hsub : ({x, y} : Finset ℕ) ⊆ Finset.range M := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact Finset.mem_range.2 (by assumption)
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hq.nonneg i)
  rw [Finset.sum_pair (Ne.symm hyx), hq.total] at this
  linarith [hq.pos y hyM]

end PostInv

/-- `∑_{i < M} 1{i < c} q i = cum q c`, for a cut inside the range. -/
lemma cum_eq_sum {M : ℕ} {q : ℕ → ℝ} {c : ℕ} (hc : c ≤ M) :
    ∑ i ∈ Finset.range M, (if i < c then q i else 0) = cum q c := by
  rw [← Finset.sum_filter, cum]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma sum_split {M : ℕ} {q : ℕ → ℝ} (hq : PostInv M q) {c : ℕ} (hc : c ≤ M) (A B : ℝ) :
    ∑ i ∈ Finset.range M, q i * (if i < c then A else B) = A * cum q c + B * (1 - cum q c) := by
  have h1 : ∀ i ∈ Finset.range M,
      q i * (if i < c then A else B) = B * q i + (A - B) * (if i < c then q i else 0) := by
    intro i _
    by_cases h : i < c <;> simp [h] <;> ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hq.total, cum_eq_sum hc]
  ring

/-! ### The Bayes step -/

/-- Likelihood of cell `i` given the answer `b` at cut `c` (`b = true` means "left of the cut"). -/
noncomputable def lik (ρ : ℝ) (c : ℕ) (b : Bool) (i : ℕ) : ℝ :=
  if decide (i < c) = b then 1 - ρ else ρ

lemma lik_eq (ρ : ℝ) (c : ℕ) (b : Bool) (i : ℕ) :
    lik ρ c b i = if i < c then (if b then 1 - ρ else ρ) else (if b then ρ else 1 - ρ) := by
  unfold lik
  cases b <;> by_cases h : i < c <;> simp [h]

/-- The Bayes normaliser. -/
noncomputable def Zn (M : ℕ) (ρ : ℝ) (q : ℕ → ℝ) (c : ℕ) (b : Bool) : ℝ :=
  ∑ i ∈ Finset.range M, q i * lik ρ c b i

/-- The updated posterior. -/
noncomputable def post (M : ℕ) (ρ : ℝ) (q : ℕ → ℝ) (c : ℕ) (b : Bool) : ℕ → ℝ :=
  fun i => q i * lik ρ c b i / Zn M ρ q c b

/-- The mass of the side of the cut that does **not** contain the true cell `x` (the brief's
`F`). -/
noncomputable def sepMass (q : ℕ → ℝ) (x c : ℕ) : ℝ := if x < c then 1 - cum q c else cum q c

/-- The separated fraction `s = F/(1 − p_n(x*))` of §1.3. -/
noncomputable def sepFrac (q : ℕ → ℝ) (x c : ℕ) : ℝ := sepMass q x c / (1 - q x)

/-- The odds against the true cell, `W = (1 − p_n(x*))/p_n(x*)`. -/
noncomputable def Wodds (q : ℕ → ℝ) (x : ℕ) : ℝ := (1 - q x) / q x

/-- The log-odds `L_n = log(p_n(x*)/(1 − p_n(x*)))`. -/
noncomputable def logOdds (q : ℕ → ℝ) (x : ℕ) : ℝ := Real.log (q x / (1 - q x))

section Step

variable {M : ℕ} {ρ : ℝ} {q : ℕ → ℝ} {x c : ℕ}

lemma sepMass_nonneg (hq : PostInv M q) (hc : c ≤ M) : 0 ≤ sepMass q x c := by
  unfold sepMass
  split
  · linarith [hq.cum_le_one hc]
  · exact hq.cum_nonneg c

lemma sepMass_le (hq : PostInv M q) (hx : x < M) (hc : c ≤ M) : sepMass q x c ≤ 1 - q x := by
  unfold sepMass
  split
  · rename_i h; linarith [hq.single_le_cum h]
  · rename_i h; linarith [hq.cum_add_single_le (x := x) (c := c) hx (by omega)]

lemma sepFrac_nonneg (hq : PostInv M q) (hM : 2 ≤ M) (hx : x < M) (hc : c ≤ M) :
    0 ≤ sepFrac q x c :=
  div_nonneg (sepMass_nonneg hq hc) (by linarith [hq.qx_lt_one hM hx])

lemma sepFrac_le_one (hq : PostInv M q) (hM : 2 ≤ M) (hx : x < M) (hc : c ≤ M) :
    sepFrac q x c ≤ 1 := by
  rw [sepFrac, div_le_one (by linarith [hq.qx_lt_one hM hx])]
  exact sepMass_le hq hx hc

lemma sepFrac_mul (hq : PostInv M q) (hM : 2 ≤ M) (hx : x < M) :
    sepFrac q x c * (1 - q x) = sepMass q x c := by
  rw [sepFrac, div_mul_cancel₀]
  linarith [hq.qx_lt_one hM hx]

/-- The normaliser in terms of the two side masses. -/
lemma Zn_side (hq : PostInv M q) (hc : c ≤ M) (b : Bool) :
    Zn M ρ q c b = if decide (x < c) = b
      then (1 - ρ) * (1 - sepMass q x c) + ρ * sepMass q x c
      else (1 - ρ) * sepMass q x c + ρ * (1 - sepMass q x c) := by
  unfold Zn
  rw [Finset.sum_congr rfl (fun i _ => by rw [lik_eq]), sum_split hq hc]
  unfold sepMass
  cases b <;> by_cases hxc : x < c <;> simp [hxc] <;> ring

lemma Zn_pos (hq : PostInv M q) (hc : c ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hx : x < M)
    (b : Bool) : 0 < Zn M ρ q c b := by
  have h0 := sepMass_nonneg (x := x) hq hc
  have h1 : sepMass q x c ≤ 1 := le_trans (sepMass_le hq hx hc) (by linarith [hq.nonneg x])
  rw [Zn_side (x := x) hq hc b]
  split <;> nlinarith

lemma post_total (hq : PostInv M q) (hc : c ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hx : x < M)
    (b : Bool) : ∑ i ∈ Finset.range M, post M ρ q c b i = 1 := by
  have hZ := Zn_pos (x := x) hq hc hρ0 hρ1 hx b
  unfold post
  rw [← Finset.sum_div]
  rw [div_eq_one_iff_eq (ne_of_gt hZ)]
  rfl

/-- The Bayes update preserves the posterior invariant. -/
lemma post_inv (hq : PostInv M q) (hc : c ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hx : x < M)
    (b : Bool) : PostInv M (post M ρ q c b) := by
  have hZ := Zn_pos (x := x) hq hc hρ0 hρ1 hx b
  refine ⟨?_, ?_, post_total (x := x) hq hc hρ0 hρ1 hx b⟩
  · intro i hi
    have hl : 0 < lik ρ c b i := by unfold lik; split <;> linarith
    exact div_pos (mul_pos (hq.pos i hi) hl) hZ
  · intro i hi
    simp [post, hq.van i hi]

/-- **Lemma N1 (one step), odds form.**  A Bayes step multiplies the odds against the true cell
by `mulHit ρ s` if the answer agrees with the side `x` is on, and by `mulMiss ρ s` otherwise;
the normaliser cancels, and the factor depends on the posterior only through `s`. -/
theorem step_odds (hq : PostInv M q) (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hx : x < M) (hc : c ≤ M) (b : Bool) :
    Wodds (post M ρ q c b) x
      = Wodds q x * (if decide (x < c) = b then mulHit ρ (sepFrac q x c)
          else mulMiss ρ (sepFrac q x c)) := by
  have hqx : 0 < q x := hq.pos x hx
  have hu : 0 < 1 - q x := by linarith [hq.qx_lt_one hM hx]
  have hZ := Zn_pos (x := x) hq hc hρ0 hρ1 hx b
  have hZe := Zn_side (x := x) (ρ := ρ) hq hc b
  have hFu := sepFrac_mul (c := c) hq hM hx
  have hb : (1 : ℝ) - ρ ≠ 0 := by linarith
  have hr : ρ ≠ 0 := ne_of_gt hρ0
  have hpost : post M ρ q c b x = q x * lik ρ c b x / Zn M ρ q c b := rfl
  have hqx' : q x ≠ 0 := ne_of_gt hqx
  have hu' : (1 : ℝ) - q x ≠ 0 := ne_of_gt hu
  by_cases hm : decide (x < c) = b
  · have hlik : lik ρ c b x = 1 - ρ := by unfold lik; rw [if_pos hm]
    rw [if_pos hm] at hZe
    rw [hZe] at hZ
    have hD : (1 - ρ) * (1 - sepMass q x c) + ρ * sepMass q x c ≠ 0 := ne_of_gt hZ
    have h1 : Wodds (post M ρ q c b) x
        = ((1 - ρ) * (1 - sepMass q x c) + ρ * sepMass q x c - q x * (1 - ρ)) / (q x * (1 - ρ)) := by
      rw [Wodds, hpost, hlik, hZe]
      field_simp
    rw [h1, if_pos hm, Wodds, mulHit, sepFrac, ← hFu, sepFrac]
    field_simp
    ring
  · have hlik : lik ρ c b x = ρ := by unfold lik; rw [if_neg hm]
    rw [if_neg hm] at hZe
    rw [hZe] at hZ
    have hD : (1 - ρ) * sepMass q x c + ρ * (1 - sepMass q x c) ≠ 0 := ne_of_gt hZ
    have h1 : Wodds (post M ρ q c b) x
        = ((1 - ρ) * sepMass q x c + ρ * (1 - sepMass q x c) - q x * ρ) / (q x * ρ) := by
      rw [Wodds, hpost, hlik, hZe]
      field_simp
    rw [h1, if_neg hm, Wodds, mulMiss, sepFrac, ← hFu, sepFrac]
    field_simp
    ring

lemma Wodds_pos (hq : PostInv M q) (hM : 2 ≤ M) (hx : x < M) : 0 < Wodds q x :=
  div_pos (by linarith [hq.qx_lt_one hM hx]) (hq.pos x hx)

lemma logOdds_eq_neg_log (hq : PostInv M q) (hM : 2 ≤ M) (hx : x < M) :
    logOdds q x = -Real.log (Wodds q x) := by
  have hqx : 0 < q x := hq.pos x hx
  have hu : 0 < 1 - q x := by linarith [hq.qx_lt_one hM hx]
  rw [logOdds, Wodds, Real.log_div (ne_of_gt hqx) (ne_of_gt hu),
    Real.log_div (ne_of_gt hu) (ne_of_gt hqx)]
  ring

/-- **Lemma N1, additive form.**  `ΔL = Δ⁺(s)` on a correct answer, `Δ⁻(s)` on a wrong one. -/
theorem step_logOdds (hq : PostInv M q) (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hx : x < M) (hc : c ≤ M) (b : Bool) :
    logOdds (post M ρ q c b) x - logOdds q x
      = if decide (x < c) = b
        then Real.log ((1 - ρ) / ((1 - ρ) - sepFrac q x c * (1 - 2 * ρ)))
        else Real.log (ρ / (ρ + sepFrac q x c * (1 - 2 * ρ))) := by
  have hs0 := sepFrac_nonneg hq hM hx hc
  have hs1 := sepFrac_le_one hq hM hx hc
  have hW := Wodds_pos hq hM hx
  have hq' := post_inv (x := x) hq hc hρ0 hρ1 hx b
  have hstep := step_odds hq hM hρ0 hρ1 hx hc b
  rw [logOdds_eq_neg_log hq' hM hx, logOdds_eq_neg_log hq hM hx, hstep]
  by_cases hm : decide (x < c) = b
  · rw [if_pos hm, if_pos hm, Real.log_mul (ne_of_gt hW) (ne_of_gt (mulHit_pos hρ0 hρ1 hs1)),
      mulHit, Real.log_div (ne_of_gt (hitNum_pos hρ0 hρ1 hs1)) (by linarith),
      Real.log_div (by linarith) (ne_of_gt (hitNum_pos hρ0 hρ1 hs1))]
    ring
  · rw [if_neg hm, if_neg hm, Real.log_mul (ne_of_gt hW) (ne_of_gt (mulMiss_pos hρ0 hρ1 hs0)),
      mulMiss, Real.log_div (ne_of_gt (missNum_pos hρ0 hρ1 hs0)) (ne_of_gt hρ0),
      Real.log_div (ne_of_gt hρ0) (ne_of_gt (missNum_pos hρ0 hρ1 hs0))]
    ring

/-- **Lemma N1, last clause:** `|ΔL| ≤ log((1−ρ)/ρ)`. -/
theorem abs_logOdds_incr_le (hq : PostInv M q) (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hx : x < M) (hc : c ≤ M) (b : Bool) :
    |logOdds (post M ρ q c b) x - logOdds q x| ≤ Real.log ((1 - ρ) / ρ) := by
  have hs0 := sepFrac_nonneg hq hM hx hc
  have hs1 := sepFrac_le_one hq hM hx hc
  have hW := Wodds_pos hq hM hx
  have hq' := post_inv (x := x) hq hc hρ0 hρ1 hx b
  have hstep := step_odds hq hM hρ0 hρ1 hx hc b
  have hlog : logOdds (post M ρ q c b) x - logOdds q x
      = -Real.log (if decide (x < c) = b then mulHit ρ (sepFrac q x c)
          else mulMiss ρ (sepFrac q x c)) := by
    rw [logOdds_eq_neg_log hq' hM hx, logOdds_eq_neg_log hq hM hx, hstep]
    by_cases hm : decide (x < c) = b
    · rw [if_pos hm, Real.log_mul (ne_of_gt hW) (ne_of_gt (mulHit_pos hρ0 hρ1 hs1))]; ring
    · rw [if_neg hm, Real.log_mul (ne_of_gt hW) (ne_of_gt (mulMiss_pos hρ0 hρ1 hs0))]; ring
  rw [hlog, abs_neg, abs_le]
  have hr : 0 < Real.log ((1 - ρ) / ρ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hρ0]; linarith
  have hneg : Real.log (ρ / (1 - ρ)) = -Real.log ((1 - ρ) / ρ) := by
    rw [Real.log_div (ne_of_gt hρ0) (by linarith), Real.log_div (by linarith) (ne_of_gt hρ0)]
    ring
  by_cases hm : decide (x < c) = b
  · rw [if_pos hm]
    refine ⟨?_, ?_⟩
    · rw [← hneg]
      exact Real.log_le_log (div_pos hρ0 (by linarith)) (mulHit_ge hρ0 hρ1 hs1)
    · calc Real.log (mulHit ρ (sepFrac q x c)) ≤ Real.log 1 :=
            Real.log_le_log (mulHit_pos hρ0 hρ1 hs1) (mulHit_le_one hρ0 hρ1 hs0)
        _ = 0 := Real.log_one
        _ ≤ _ := hr.le
  · rw [if_neg hm]
    refine ⟨?_, ?_⟩
    · calc -Real.log ((1 - ρ) / ρ) ≤ 0 := by linarith
        _ = Real.log 1 := Real.log_one.symm
        _ ≤ _ := Real.log_le_log (by norm_num) (mulMiss_ge_one hρ0 hρ1 hs0)
    · exact Real.log_le_log (mulMiss_pos hρ0 hρ1 hs0) (mulMiss_le hρ0 hρ1 hs1)

/-- The two answers of one query, re-expressed through `s` (Lemma N1 averaged over the answer).
`b = true` is the answer "left of the cut"; the answer agrees with `x`'s side with probability
`1 − ρ` in both cases. -/
lemma answer_avg_f (hq : PostInv M q) (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hx : x < M) (hc : c ≤ M) (f : ℝ → ℝ) :
    (if x < c then 1 - ρ else ρ) * f (Wodds (post M ρ q c true) x)
      + (1 - (if x < c then 1 - ρ else ρ)) * f (Wodds (post M ρ q c false) x)
      = (1 - ρ) * f (Wodds q x * mulHit ρ (sepFrac q x c))
        + ρ * f (Wodds q x * mulMiss ρ (sepFrac q x c)) := by
  rw [step_odds hq hM hρ0 hρ1 hx hc true, step_odds hq hM hρ0 hρ1 hx hc false]
  by_cases hxc : x < c
  · rw [if_pos hxc, if_pos (show decide (x < c) = true by simp [hxc]),
      if_neg (show ¬(decide (x < c) = false) by simp [hxc])]
    ring
  · rw [if_neg hxc, if_neg (show ¬(decide (x < c) = true) by simp [hxc]),
      if_pos (show decide (x < c) = false by simp [hxc])]
    ring

end Step

/-! ### The randomised median rule (Lemma N3) -/

/-- The median cell: the least `j` with `p_n(0) + … + p_n(j) ≥ 1/2`. -/
noncomputable def medIdx (q : ℕ → ℝ) : ℕ := sInf {c : ℕ | 1 / 2 ≤ cum q (c + 1)}

/-- The randomisation weight `α = (A + p_n(j) − 1/2)/p_n(j)`, clamped to `[0,1]` so that it is a
valid probability for every function `q` (the clamp is inactive under `PostInv`, `alph_eq`). -/
noncomputable def alph (q : ℕ → ℝ) : ℝ :=
  max 0 (min 1 ((cum q (medIdx q + 1) - 1 / 2) / q (medIdx q)))

section Median

variable {M : ℕ} {q : ℕ → ℝ}

lemma alph_nonneg (q : ℕ → ℝ) : 0 ≤ alph q := le_max_left _ _

lemma alph_le_one (q : ℕ → ℝ) : alph q ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

lemma med_mem (hq : PostInv M q) (hM : 1 ≤ M) : (1 : ℝ) / 2 ≤ cum q (medIdx q + 1) := by
  have hne : {c : ℕ | 1 / 2 ≤ cum q (c + 1)}.Nonempty := by
    refine ⟨M - 1, ?_⟩
    simp only [Set.mem_setOf_eq]
    rw [show M - 1 + 1 = M by omega, hq.cum_M]
    norm_num
  exact Nat.sInf_mem hne

lemma med_lt (hq : PostInv M q) (hM : 1 ≤ M) : medIdx q < M := by
  have hmem : M - 1 ∈ {c : ℕ | 1 / 2 ≤ cum q (c + 1)} := by
    simp only [Set.mem_setOf_eq]
    rw [show M - 1 + 1 = M by omega, hq.cum_M]
    norm_num
  have h := Nat.sInf_le hmem
  rw [medIdx]
  omega

lemma med_le_half (hq : PostInv M q) (hM : 1 ≤ M) : cum q (medIdx q) ≤ 1 / 2 := by
  rcases Nat.eq_zero_or_pos (medIdx q) with h | h
  · rw [h]; simp [cum]
  · obtain ⟨k, hk⟩ : ∃ k, medIdx q = k + 1 := ⟨medIdx q - 1, by omega⟩
    have hnot := Nat.notMem_of_lt_sInf (s := {c : ℕ | 1 / 2 ≤ cum q (c + 1)}) (m := k)
      (by rw [← medIdx]; omega)
    simp only [Set.mem_setOf_eq, not_le] at hnot
    rw [hk]; linarith

lemma alph_eq (hq : PostInv M q) (hM : 1 ≤ M) :
    alph q = (cum q (medIdx q + 1) - 1 / 2) / q (medIdx q) := by
  have hp : 0 < q (medIdx q) := hq.pos _ (med_lt hq hM)
  have h1 : 0 ≤ (cum q (medIdx q + 1) - 1 / 2) / q (medIdx q) := by
    apply div_nonneg _ hp.le; linarith [med_mem hq hM]
  have h2 : (cum q (medIdx q + 1) - 1 / 2) / q (medIdx q) ≤ 1 := by
    rw [div_le_one hp, PostInv.cum_succ]
    linarith [med_le_half hq hM]
  rw [alph, min_eq_right h2, max_eq_right h1]

/-- The defining property of the randomised median rule: the mass strictly left of the query
point is `1/2` **in expectation** (display (1.1) of the brief). -/
lemma alph_split (hq : PostInv M q) (hM : 1 ≤ M) :
    alph q * cum q (medIdx q) + (1 - alph q) * cum q (medIdx q + 1) = 1 / 2 := by
  have hp : 0 < q (medIdx q) := hq.pos _ (med_lt hq hM)
  rw [alph_eq hq hM, PostInv.cum_succ]
  field_simp
  ring

/-- **Lemma N3.**  The randomised median rule separates at least half of the wrong mass:
`E[s | F_n] ≥ 1/2`, in the division-free form `E[F] ≥ (1 − p_n(x*))/2`.  The hard case
(`x* = j`) reduces to `α(1−α) ≤ 1/4`. -/
theorem median_sep (hq : PostInv M q) (hM : 2 ≤ M) {x : ℕ} (hx : x < M) :
    (1 - q x) / 2
      ≤ alph q * sepMass q x (medIdx q) + (1 - alph q) * sepMass q x (medIdx q + 1) := by
  have hM1 : 1 ≤ M := by omega
  have hjM := med_lt hq hM1
  have hsplit := alph_split hq hM1
  have hsucc := PostInv.cum_succ q (medIdx q)
  have ha0 := alph_nonneg q
  have ha1 := alph_le_one q
  have hqx := hq.nonneg x
  rcases lt_trichotomy x (medIdx q) with h | h | h
  · -- `x*` is left of the median cell under both options
    have e1 : sepMass q x (medIdx q) = 1 - cum q (medIdx q) := by
      rw [sepMass, if_pos h]
    have e2 : sepMass q x (medIdx q + 1) = 1 - cum q (medIdx q + 1) := by
      rw [sepMass, if_pos (by omega)]
    rw [e1, e2]
    nlinarith
  · -- the hard case: `x* = j`
    have hqe : q (medIdx q) = q x := by rw [h]
    rw [hqe] at hsucc
    have e1 : sepMass q x (medIdx q) = cum q (medIdx q) := by
      rw [sepMass, if_neg (by omega)]
    have e2 : sepMass q x (medIdx q + 1) = 1 - cum q (medIdx q + 1) := by
      rw [sepMass, if_pos (by omega)]
    rw [e1, e2]
    nlinarith [sq_nonneg (alph q - 1 / 2), hq.nonneg x]
  · -- `x*` is right of the median cell under both options
    have e1 : sepMass q x (medIdx q) = cum q (medIdx q) := by
      rw [sepMass, if_neg (by omega)]
    have e2 : sepMass q x (medIdx q + 1) = cum q (medIdx q + 1) := by
      rw [sepMass, if_neg (by omega)]
    rw [e1, e2]
    nlinarith

/-- Lemma N3 in the form used by Theorem N: `E[s | F_n] ≥ 1/2`. -/
theorem sepFrac_avg (hq : PostInv M q) (hM : 2 ≤ M) {x : ℕ} (hx : x < M) :
    1 / 2 ≤ alph q * sepFrac q x (medIdx q) + (1 - alph q) * sepFrac q x (medIdx q + 1) := by
  have hu : 0 < 1 - q x := by linarith [hq.qx_lt_one hM hx]
  have key : alph q * sepFrac q x (medIdx q) + (1 - alph q) * sepFrac q x (medIdx q + 1)
      = (alph q * sepMass q x (medIdx q) + (1 - alph q) * sepMass q x (medIdx q + 1))
        / (1 - q x) := by
    rw [sepFrac, sepFrac]; ring
  rw [key, le_div_iff₀ hu]
  linarith [median_sep hq hM hx]

end Median

/-! ## §2. The search as a two-rounds-per-query `val` process -/

section Process

/-- Generic two-round unfolding of `val`. -/
lemma val_succ2 {X : Type*} (p : X → ℝ) (probe : List Bool → X) (F : List Bool → ℝ)
    (r : ℕ) (h : List Bool) :
    val p probe F (r + 2) h =
      p (probe h) * (p (probe (h ++ [true])) * val p probe F r (h ++ [true] ++ [true])
        + (1 - p (probe (h ++ [true]))) * val p probe F r (h ++ [true] ++ [false]))
      + (1 - p (probe h)) * (p (probe (h ++ [false])) * val p probe F r (h ++ [false] ++ [true])
        + (1 - p (probe (h ++ [false]))) * val p probe F r (h ++ [false] ++ [false])) := by
  rw [show r + 2 = (r + 1) + 1 from rfl, val_succ, val_succ, val_succ]

/-- The state of the search: the current posterior, the cut the pending answer refers to, and
the phase (`false` = the next bit is the randomisation coin, `true` = it is the oracle's
answer). -/
structure St where
  /-- the current posterior -/
  q : ℕ → ℝ
  /-- the cut of the query awaiting its answer -/
  cut : ℕ
  /-- `false`: the next bit is the coin; `true`: the next bit is the answer -/
  phase : Bool
  /-- the number of completed queries -/
  k : ℕ

/-- The uniform prior on the `M` cells. -/
noncomputable def stInit (M : ℕ) : St :=
  ⟨fun i => if i < M then (M : ℝ)⁻¹ else 0, 0, false, 0⟩

/-- One round.  `halt` freezes the run at the start of a query (this is how the stopping rule of
Theorem N(d) is expressed at a finite horizon); `halt = fun _ => false` is the plain search. -/
noncomputable def step (M : ℕ) (ρ : ℝ) (halt : (ℕ → ℝ) → Bool) (s : St) (b : Bool) : St :=
  if s.phase then ⟨post M ρ s.q s.cut b, s.cut, false, s.k + 1⟩
  else if halt s.q then s
  else ⟨s.q, if b then medIdx s.q else medIdx s.q + 1, true, s.k⟩

/-- The state after a transcript. -/
noncomputable def state (M : ℕ) (ρ : ℝ) (halt : (ℕ → ℝ) → Bool) (h : List Bool) : St :=
  h.foldl (step M ρ halt) (stInit M)

/-- The per-round bias: `α` at a coin round, the oracle's answer probability at an answer
round (and an irrelevant `1/2` once the run has halted). -/
noncomputable def bias (M : ℕ) (ρ : ℝ) (halt : (ℕ → ℝ) → Bool) (x : ℕ) (s : St) : ℝ :=
  if s.phase then (if x < s.cut then 1 - ρ else ρ)
  else if halt s.q then 1 / 2
  else alph s.q

/-- The state invariant carried along the transcript. -/
structure Good (M : ℕ) (s : St) : Prop where
  /-- the posterior is a genuine posterior -/
  inv : PostInv M s.q
  /-- the pending cut is inside the range -/
  cut_le : s.cut ≤ M

variable {M : ℕ} {ρ : ℝ} {halt : (ℕ → ℝ) → Bool} {x : ℕ} {s : St}

lemma state_nil (M : ℕ) (ρ : ℝ) (halt : (ℕ → ℝ) → Bool) :
    state M ρ halt ([] : List Bool) = stInit M := rfl

lemma state_append (M : ℕ) (ρ : ℝ) (halt : (ℕ → ℝ) → Bool) (h : List Bool) (b : Bool) :
    state M ρ halt (h ++ [b]) = step M ρ halt (state M ρ halt h) b := by
  simp [state, List.foldl_append]

lemma step_answer (hph : s.phase = true) (b : Bool) :
    step M ρ halt s b = ⟨post M ρ s.q s.cut b, s.cut, false, s.k + 1⟩ := by
  rw [step, if_pos (by simp [hph])]

lemma step_halted (hph : s.phase = false) (hh : halt s.q = true) (b : Bool) :
    step M ρ halt s b = s := by
  rw [step, if_neg (by simp [hph]), if_pos (by simp [hh])]

lemma step_coin (hph : s.phase = false) (hh : halt s.q = false) (b : Bool) :
    step M ρ halt s b = ⟨s.q, if b then medIdx s.q else medIdx s.q + 1, true, s.k⟩ := by
  rw [step, if_neg (by simp [hph]), if_neg (by simp [hh])]

lemma bias_answer (hph : s.phase = true) :
    bias M ρ halt x s = if x < s.cut then 1 - ρ else ρ := by
  rw [bias, if_pos (by simp [hph])]

lemma bias_coin (hph : s.phase = false) (hh : halt s.q = false) :
    bias M ρ halt x s = alph s.q := by
  rw [bias, if_neg (by simp [hph]), if_neg (by simp [hh])]

lemma bias_mem (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (t : St) :
    0 ≤ bias M ρ halt x t ∧ bias M ρ halt x t ≤ 1 := by
  rw [bias]
  split
  · split <;> constructor <;> linarith
  · split
    · constructor <;> norm_num
    · exact ⟨alph_nonneg _, alph_le_one _⟩

/-- Two rounds from a coin-phase state land in a coin-phase state again. -/
lemma step_phase2 (hph : s.phase = false) (b b' : Bool) :
    (step M ρ halt (step M ρ halt s b) b').phase = false := by
  by_cases hh : halt s.q = true
  · rw [step_halted hph hh, step_halted hph hh, hph]
  · rw [Bool.not_eq_true] at hh
    rw [step_coin hph hh, step_answer rfl]

lemma good_init (hM : 2 ≤ M) : Good M (stInit M) := by
  have hM0 : (0 : ℝ) < (M : ℕ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hM
  refine ⟨⟨?_, ?_, ?_⟩, Nat.zero_le M⟩
  · intro i hi; simp only [stInit, if_pos hi]; positivity
  · intro i hi; simp only [stInit]; rw [if_neg (by omega)]
  · simp only [stInit]
    rw [Finset.sum_congr rfl (fun i hi => by rw [if_pos (Finset.mem_range.1 hi)]),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp

lemma good_step (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hg : Good M s) (b : Bool) :
    Good M (step M ρ halt s b) := by
  by_cases hph : s.phase = true
  · rw [step_answer hph]
    exact ⟨post_inv (x := 0) hg.inv hg.cut_le hρ0 hρ1 (by omega) b, hg.cut_le⟩
  · rw [Bool.not_eq_true] at hph
    by_cases hh : halt s.q = true
    · rw [step_halted hph hh]; exact hg
    · rw [Bool.not_eq_true] at hh
      rw [step_coin hph hh]
      refine ⟨hg.inv, ?_⟩
      have := med_lt hg.inv (by omega : 1 ≤ M)
      cases b <;> simp <;> omega

lemma good_foldl (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    ∀ (h : List Bool) (t : St), Good M t → Good M (h.foldl (step M ρ halt) t) := by
  intro h
  induction h with
  | nil => intro t ht; exact ht
  | cons b l ih => intro t ht; exact ih _ (good_step hM hρ0 hρ1 ht b)

lemma good_state (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (h : List Bool) :
    Good M (state M ρ halt h) :=
  good_foldl hM hρ0 hρ1 h _ (good_init hM)

/-! ### Martingale and two-round supermartingale principles (as in `Attacks/Sieve.lean`) -/

/-- **Martingale principle.**  A state function whose one-round average is itself has constant
expectation along the process, at every horizon. -/
lemma val_mart (M : ℕ) (ρ : ℝ) (halt : (ℕ → ℝ) → Bool) (x : ℕ) (W : St → ℝ)
    (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hone : ∀ t : St, Good M t → bias M ρ halt x t * W (step M ρ halt t true)
      + (1 - bias M ρ halt x t) * W (step M ρ halt t false) = W t) :
    ∀ (r : ℕ) (h : List Bool),
      val (bias M ρ halt x) (state M ρ halt) (fun h' => W (state M ρ halt h')) r h
        = W (state M ρ halt h) := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    have hb := ih (h ++ [true])
    have hf := ih (h ++ [false])
    rw [state_append] at hb hf
    rw [val_succ, hb, hf]
    exact hone _ (good_state hM hρ0 hρ1 h)

/-- The two-round (one-query) conditional expectation of a state function. -/
noncomputable def E2 (M : ℕ) (ρ : ℝ) (halt : (ℕ → ℝ) → Bool) (x : ℕ) (W : St → ℝ) (s : St) :
    ℝ :=
  bias M ρ halt x s *
      (bias M ρ halt x (step M ρ halt s true) * W (step M ρ halt (step M ρ halt s true) true)
        + (1 - bias M ρ halt x (step M ρ halt s true)) *
            W (step M ρ halt (step M ρ halt s true) false))
    + (1 - bias M ρ halt x s) *
      (bias M ρ halt x (step M ρ halt s false) * W (step M ρ halt (step M ρ halt s false) true)
        + (1 - bias M ρ halt x (step M ρ halt s false)) *
            W (step M ρ halt (step M ρ halt s false) false))

lemma E2_congr {W W' : St → ℝ} (M : ℕ) (ρ : ℝ) (halt : (ℕ → ℝ) → Bool) (x : ℕ) (s : St)
    (h : ∀ b b', W (step M ρ halt (step M ρ halt s b) b')
      = W' (step M ρ halt (step M ρ halt s b) b')) :
    E2 M ρ halt x W s = E2 M ρ halt x W' s := by
  unfold E2
  rw [h true true, h true false, h false true, h false false]

/-- **Two-round supermartingale principle.**  If one query multiplies `W` by at most `φ` in
conditional expectation, then `T` queries (that is, `2T` rounds) multiply it by at most `φ^T`. -/
lemma val_super2 (M : ℕ) (ρ : ℝ) (halt : (ℕ → ℝ) → Bool) (x : ℕ) (W : St → ℝ) (φ : ℝ)
    (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hφ : 0 ≤ φ)
    (hone : ∀ t : St, Good M t → t.phase = false → E2 M ρ halt x W t ≤ φ * W t) :
    ∀ (T : ℕ) (h : List Bool), (state M ρ halt h).phase = false →
      val (bias M ρ halt x) (state M ρ halt) (fun h' => W (state M ρ halt h')) (2 * T) h
        ≤ φ ^ T * W (state M ρ halt h) := by
  intro T
  induction T with
  | zero => intro h _; simp
  | succ T ih =>
    intro h hph
    have hstep2 : ∀ b b' : Bool,
        state M ρ halt (h ++ [b] ++ [b'])
          = step M ρ halt (step M ρ halt (state M ρ halt h) b) b' := by
      intro b b'; rw [state_append, state_append]
    have hph2 : ∀ b b' : Bool, (state M ρ halt (h ++ [b] ++ [b'])).phase = false := by
      intro b b'; rw [hstep2]; exact step_phase2 hph b b'
    have key : ∀ b b' : Bool,
        val (bias M ρ halt x) (state M ρ halt) (fun h' => W (state M ρ halt h')) (2 * T)
            (h ++ [b] ++ [b'])
          ≤ φ ^ T * W (step M ρ halt (step M ρ halt (state M ρ halt h) b) b') := by
      intro b b'
      have := ih (h ++ [b] ++ [b']) (hph2 b b')
      rwa [hstep2] at this
    have hpT : (0 : ℝ) ≤ φ ^ T := pow_nonneg hφ T
    have hb0 := bias_mem (M := M) (halt := halt) (x := x) hρ0 hρ1 (state M ρ halt h)
    have hb1 := bias_mem (M := M) (halt := halt) (x := x) hρ0 hρ1
      (step M ρ halt (state M ρ halt h) true)
    have hb2 := bias_mem (M := M) (halt := halt) (x := x) hρ0 hρ1
      (step M ρ halt (state M ρ halt h) false)
    have hE := hone (state M ρ halt h) (good_state hM hρ0 hρ1 h) hph
    rw [show 2 * (T + 1) = 2 * T + 2 by ring, val_succ2]
    have hsa : ∀ b : Bool, state M ρ halt (h ++ [b]) = step M ρ halt (state M ρ halt h) b :=
      fun b => state_append M ρ halt h b
    rw [hsa true, hsa false]
    have k1 := key true true
    have k2 := key true false
    have k3 := key false true
    have k4 := key false false
    have hin1 : bias M ρ halt x (step M ρ halt (state M ρ halt h) true) *
          val (bias M ρ halt x) (state M ρ halt) (fun h' => W (state M ρ halt h')) (2 * T)
            (h ++ [true] ++ [true])
        + (1 - bias M ρ halt x (step M ρ halt (state M ρ halt h) true)) *
          val (bias M ρ halt x) (state M ρ halt) (fun h' => W (state M ρ halt h')) (2 * T)
            (h ++ [true] ++ [false])
        ≤ φ ^ T * (bias M ρ halt x (step M ρ halt (state M ρ halt h) true) *
            W (step M ρ halt (step M ρ halt (state M ρ halt h) true) true)
          + (1 - bias M ρ halt x (step M ρ halt (state M ρ halt h) true)) *
            W (step M ρ halt (step M ρ halt (state M ρ halt h) true) false)) := by
      nlinarith [mul_le_mul_of_nonneg_left k1 hb1.1,
        mul_le_mul_of_nonneg_left k2 (by linarith [hb1.2] : (0:ℝ) ≤ 1 - bias M ρ halt x
          (step M ρ halt (state M ρ halt h) true))]
    have hin2 : bias M ρ halt x (step M ρ halt (state M ρ halt h) false) *
          val (bias M ρ halt x) (state M ρ halt) (fun h' => W (state M ρ halt h')) (2 * T)
            (h ++ [false] ++ [true])
        + (1 - bias M ρ halt x (step M ρ halt (state M ρ halt h) false)) *
          val (bias M ρ halt x) (state M ρ halt) (fun h' => W (state M ρ halt h')) (2 * T)
            (h ++ [false] ++ [false])
        ≤ φ ^ T * (bias M ρ halt x (step M ρ halt (state M ρ halt h) false) *
            W (step M ρ halt (step M ρ halt (state M ρ halt h) false) true)
          + (1 - bias M ρ halt x (step M ρ halt (state M ρ halt h) false)) *
            W (step M ρ halt (step M ρ halt (state M ρ halt h) false) false)) := by
      nlinarith [mul_le_mul_of_nonneg_left k3 hb2.1,
        mul_le_mul_of_nonneg_left k4 (by linarith [hb2.2] : (0:ℝ) ≤ 1 - bias M ρ halt x
          (step M ρ halt (state M ρ halt h) false))]
    have hE2 : E2 M ρ halt x W (state M ρ halt h) ≤ φ * W (state M ρ halt h) := hE
    rw [E2] at hE2
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hin1 hb0.1,
      mul_le_mul_of_nonneg_left hin2 (by linarith [hb0.2] : (0:ℝ) ≤ 1 - bias M ρ halt x
        (state M ρ halt h)),
      mul_le_mul_of_nonneg_left hE2 hpT]

end Process

/-! ### Theorem N -/

section ThmN

variable {M : ℕ} {ρ lam : ℝ} {halt : (ℕ → ℝ) → Bool} {x : ℕ} {s : St}

/-- One query, unfolded: the coin picks one of the two endpoints of the median cell, and the
answer then multiplies the odds by `mulHit`/`mulMiss` at the corresponding separated fraction. -/
lemma E2_of_fun (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hx : x < M)
    (hg : Good M s) (hph : s.phase = false) (hh : halt s.q = false) (f : ℝ → ℝ) :
    E2 M ρ halt x (fun t => f (Wodds t.q x)) s
      = alph s.q * ((1 - ρ) * f (Wodds s.q x * mulHit ρ (sepFrac s.q x (medIdx s.q)))
            + ρ * f (Wodds s.q x * mulMiss ρ (sepFrac s.q x (medIdx s.q))))
        + (1 - alph s.q) *
          ((1 - ρ) * f (Wodds s.q x * mulHit ρ (sepFrac s.q x (medIdx s.q + 1)))
            + ρ * f (Wodds s.q x * mulMiss ρ (sepFrac s.q x (medIdx s.q + 1)))) := by
  have hjM : medIdx s.q < M := med_lt hg.inv (by omega)
  have hc1 : medIdx s.q ≤ M := by omega
  have hc2 : medIdx s.q + 1 ≤ M := by omega
  have s1 : step M ρ halt s true = ⟨s.q, medIdx s.q, true, s.k⟩ := by
    rw [step_coin hph hh]; simp
  have s2 : step M ρ halt s false = ⟨s.q, medIdx s.q + 1, true, s.k⟩ := by
    rw [step_coin hph hh]; simp
  have t1 : ∀ (c : ℕ) (b' : Bool), step M ρ halt (⟨s.q, c, true, s.k⟩ : St) b'
      = ⟨post M ρ s.q c b', c, false, s.k + 1⟩ := fun c b' => step_answer rfl b'
  rw [E2, bias_coin hph hh, s1, s2, bias_answer (s := (⟨s.q, medIdx s.q, true, s.k⟩ : St)) rfl,
    bias_answer (s := (⟨s.q, medIdx s.q + 1, true, s.k⟩ : St)) rfl,
    t1 (medIdx s.q) true, t1 (medIdx s.q) false, t1 (medIdx s.q + 1) true,
    t1 (medIdx s.q + 1) false]
  simp only []
  rw [answer_avg_f hg.inv hM hρ0 hρ1 hx hc1 f, answer_avg_f hg.inv hM hρ0 hρ1 hx hc2 f]

/-- **Theorem N(a) (drift).**  `E[L_{n+1} − L_n | F_n] ≥ Cap(ρ)`, for every true cell. -/
theorem thmN_a (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hx : x < M)
    (hg : Good M s) (hph : s.phase = false) (hh : halt s.q = false) :
    logOdds s.q x + Cap ρ ≤ E2 M ρ halt x (fun t => logOdds t.q x) s := by
  have hW := Wodds_pos hg.inv hM hx
  have hjM : medIdx s.q < M := med_lt hg.inv (by omega)
  have hu1a := sepFrac_nonneg hg.inv hM hx (show medIdx s.q ≤ M by omega)
  have hu1b := sepFrac_le_one hg.inv hM hx (show medIdx s.q ≤ M by omega)
  have hu2a := sepFrac_nonneg hg.inv hM hx (show medIdx s.q + 1 ≤ M by omega)
  have hu2b := sepFrac_le_one hg.inv hM hx (show medIdx s.q + 1 ≤ M by omega)
  have hcong : E2 M ρ halt x (fun t => logOdds t.q x) s
      = E2 M ρ halt x (fun t => -Real.log (Wodds t.q x)) s := by
    refine E2_congr M ρ halt x s (fun b b' => ?_)
    exact logOdds_eq_neg_log
      (good_step hM hρ0 hρ1 (good_step hM hρ0 hρ1 hg b) b').inv hM hx
  have key : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (1 - ρ) * (-Real.log (Wodds s.q x * mulHit ρ u))
        + ρ * (-Real.log (Wodds s.q x * mulMiss ρ u))
        = -Real.log (Wodds s.q x) + psi ρ u := by
    intro u hu0 hu1
    rw [Real.log_mul (ne_of_gt hW) (ne_of_gt (mulHit_pos hρ0 hρ1 hu1)),
      Real.log_mul (ne_of_gt hW) (ne_of_gt (mulMiss_pos hρ0 hρ1 hu0)), psi]
    ring
  rw [hcong, E2_of_fun hM hρ0 hρ1 hx hg hph hh (fun w => -Real.log w)]
  rw [key _ hu1a hu1b, key _ hu2a hu2b, logOdds_eq_neg_log hg.inv hM hx]
  have hp1 := psi_tangent hρ0 hρ1 hu1a hu1b
  have hp2 := psi_tangent hρ0 hρ1 hu2a hu2b
  have havg := sepFrac_avg hg.inv hM hx
  have ha0 := alph_nonneg s.q
  have ha1 := alph_le_one s.q
  nlinarith [mul_le_mul_of_nonneg_left hp1 ha0,
    mul_le_mul_of_nonneg_left hp2 (by linarith : (0:ℝ) ≤ 1 - alph s.q),
    mul_le_mul_of_nonneg_left havg (sq_nonneg (1 - 2 * ρ))]

/-- **Theorem N(b) (MGF).**  `E[e^{−λ ΔL} | F_n] ≤ φ(λ)`, for every true cell. -/
theorem thmN_b (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hx : x < M) (hg : Good M s) (hph : s.phase = false) (hh : halt s.q = false) :
    E2 M ρ halt x (fun t => Wodds t.q x ^ lam) s ≤ phi ρ lam * Wodds s.q x ^ lam := by
  have hW := Wodds_pos hg.inv hM hx
  have hWp : (0 : ℝ) < Wodds s.q x ^ lam := Real.rpow_pos_of_pos hW lam
  have hjM : medIdx s.q < M := med_lt hg.inv (by omega)
  have hu1a := sepFrac_nonneg hg.inv hM hx (show medIdx s.q ≤ M by omega)
  have hu1b := sepFrac_le_one hg.inv hM hx (show medIdx s.q ≤ M by omega)
  have hu2a := sepFrac_nonneg hg.inv hM hx (show medIdx s.q + 1 ≤ M by omega)
  have hu2b := sepFrac_le_one hg.inv hM hx (show medIdx s.q + 1 ≤ M by omega)
  have key : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (1 - ρ) * (Wodds s.q x * mulHit ρ u) ^ lam + ρ * (Wodds s.q x * mulMiss ρ u) ^ lam
        = Wodds s.q x ^ lam * Gmgf ρ lam u := by
    intro u hu0 hu1
    rw [Real.mul_rpow hW.le (mulHit_pos hρ0 hρ1 hu1).le,
      Real.mul_rpow hW.le (mulMiss_pos hρ0 hρ1 hu0).le, Gmgf]
    ring
  rw [E2_of_fun hM hρ0 hρ1 hx hg hph hh (fun w => w ^ lam)]
  rw [key _ hu1a hu1b, key _ hu2a hu2b]
  have hG1 := Gmgf_tangent hρ0 hρ1 hlam0.le hlam1.le hu1a hu1b
  have hG2 := Gmgf_tangent hρ0 hρ1 hlam0.le hlam1.le hu2a hu2b
  have havg := sepFrac_avg hg.inv hM hx
  have hK := Ktan_nonneg hρ0 hρ1 hlam0.le hlam1.le
  have ha0 := alph_nonneg s.q
  have ha1 := alph_le_one s.q
  have hAB : alph s.q * Gmgf ρ lam (sepFrac s.q x (medIdx s.q))
      + (1 - alph s.q) * Gmgf ρ lam (sepFrac s.q x (medIdx s.q + 1)) ≤ phi ρ lam := by
    nlinarith [mul_le_mul_of_nonneg_left hG1 ha0,
      mul_le_mul_of_nonneg_left hG2 (by linarith : (0:ℝ) ≤ 1 - alph s.q),
      mul_le_mul_of_nonneg_left havg hK]
  nlinarith [mul_le_mul_of_nonneg_left hAB hWp.le]

lemma phi_nonneg (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) : 0 ≤ phi ρ lam := by
  have h1 : (0 : ℝ) ≤ ρ ^ (1 - lam) := Real.rpow_nonneg hρ0.le _
  have h2 : (0 : ℝ) ≤ (1 - ρ) ^ (1 - lam) := Real.rpow_nonneg (by linarith) _
  have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ (-lam) := Real.rpow_nonneg (by norm_num) _
  unfold phi
  positivity

lemma Wodds_init (hM : 2 ≤ M) (hx : x < M) : Wodds (stInit M).q x = (M : ℝ) - 1 := by
  have hM0 : (0 : ℝ) < (M : ℕ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hM
  simp only [stInit, Wodds, if_pos hx]
  field_simp

open Classical in
/-- **Theorem N(c) (fixed budget).**  After `T` queries (that is, `2T` rounds of the process),
the probability that some cell other than `x*` carries at least as much posterior mass as `x*`
is at most `(M−1)^λ φ(λ)^T`. -/
theorem thmN_c (M : ℕ) (hM : 2 ≤ M) (ρ lam : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (x : ℕ) (hx : x < M) (T : ℕ) :
    val (bias M ρ (fun _ => false) x) (state M ρ (fun _ => false))
        (fun h => if ∃ i, i < M ∧ i ≠ x ∧ (state M ρ (fun _ => false) h).q x
              ≤ (state M ρ (fun _ => false) h).q i then (1 : ℝ) else 0) (2 * T) []
      ≤ ((M : ℝ) - 1) ^ lam * phi ρ lam ^ T := by
  set halt : (ℕ → ℝ) → Bool := fun _ => false with hhalt
  have hp : ∀ t : St, 0 ≤ bias M ρ halt x t ∧ bias M ρ halt x t ≤ 1 :=
    fun t => bias_mem hρ0 hρ1 t
  have hdom : ∀ h' : List Bool,
      (if ∃ i, i < M ∧ i ≠ x ∧ (state M ρ halt h').q x ≤ (state M ρ halt h').q i then (1 : ℝ)
        else 0) ≤ Wodds (state M ρ halt h').q x ^ lam := by
    intro h'
    have hg := good_state (halt := halt) hM hρ0 hρ1 h'
    have hW := Wodds_pos hg.inv hM hx
    split
    · rename_i hex
      obtain ⟨i, hiM, hix, hle⟩ := hex
      have hpair := hg.inv.pair_le_one (Ne.symm hix) hx hiM
      have h1 : (1 : ℝ) ≤ Wodds (state M ρ halt h').q x := by
        rw [Wodds, le_div_iff₀ (hg.inv.pos x hx)]
        linarith
      calc (1 : ℝ) = (1 : ℝ) ^ lam := (Real.one_rpow lam).symm
        _ ≤ _ := Real.rpow_le_rpow (by norm_num) h1 hlam0.le
    · exact Real.rpow_nonneg hW.le lam
  have hsup := val_super2 M ρ halt x (fun t => Wodds t.q x ^ lam) (phi ρ lam) hM hρ0 hρ1
    (phi_nonneg hρ0 hρ1) (fun t hg hph => thmN_b hM hρ0 hρ1 hlam0 hlam1 hx hg hph rfl) T [] rfl
  rw [state_nil] at hsup
  calc val (bias M ρ halt x) (state M ρ halt)
        (fun h => if ∃ i, i < M ∧ i ≠ x ∧ (state M ρ halt h).q x ≤ (state M ρ halt h).q i
          then (1 : ℝ) else 0) (2 * T) []
      ≤ val (bias M ρ halt x) (state M ρ halt)
          (fun h' => Wodds (state M ρ halt h').q x ^ lam) (2 * T) [] :=
        val_mono (state M ρ halt) hp (2 * T) [] (fun h' _ => hdom h')
    _ ≤ phi ρ lam ^ T * Wodds (stInit M).q x ^ lam := hsup
    _ = ((M : ℝ) - 1) ^ lam * phi ρ lam ^ T := by rw [Wodds_init hM hx]; ring

/-- **Theorem N(d), martingale.**  `W_n = (1 − p_n(x*))/p_n(x*)` is a martingale with
`W_0 = M − 1`, for every `halt` rule and at every horizon. -/
theorem odds_mart (M : ℕ) (hM : 2 ≤ M) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (halt : (ℕ → ℝ) → Bool) (x : ℕ) (hx : x < M) (T : ℕ) :
    val (bias M ρ halt x) (state M ρ halt) (fun h => Wodds (state M ρ halt h).q x) T []
      = (M : ℝ) - 1 := by
  have hone : ∀ t : St, Good M t →
      bias M ρ halt x t * Wodds (step M ρ halt t true).q x
        + (1 - bias M ρ halt x t) * Wodds (step M ρ halt t false).q x
        = Wodds t.q x := by
    intro t hg
    by_cases hph : t.phase = true
    · rw [bias_answer hph, step_answer hph true, step_answer hph false]
      simp only []
      rw [answer_avg_f hg.inv hM hρ0 hρ1 hx hg.cut_le (fun w => w)]
      have hu0 := sepFrac_nonneg hg.inv hM hx hg.cut_le
      have hu1 := sepFrac_le_one hg.inv hM hx hg.cut_le
      have hma := mul_avg (ρ := ρ) (s := sepFrac t.q x t.cut) hρ0 hρ1
      linear_combination Wodds t.q x * hma
    · rw [Bool.not_eq_true] at hph
      by_cases hh : halt t.q = true
      · rw [step_halted hph hh, step_halted hph hh]; ring
      · rw [Bool.not_eq_true] at hh
        rw [step_coin hph hh, step_coin hph hh]
        simp only []
        ring
  have := val_mart M ρ halt x (fun t => Wodds t.q x) hM hρ0 hρ1 hone T []
  rw [state_nil, Wodds_init hM hx] at this
  exact this

open Classical in
/-- The stopping rule of Theorem N(d): halt as soon as some cell carries mass `≥ 1 − γ`. -/
noncomputable def haltAt (M : ℕ) (γ : ℝ) (q : ℕ → ℝ) : Bool :=
  if ∃ i, i < M ∧ 1 - γ ≤ q i then true else false

open Classical in
lemma haltAt_true {M : ℕ} {γ : ℝ} {q : ℕ → ℝ} (h : haltAt M γ q = true) :
    ∃ i, i < M ∧ 1 - γ ≤ q i := by
  unfold haltAt at h
  by_cases hc : ∃ i, i < M ∧ 1 - γ ≤ q i
  · exact hc
  · rw [if_neg hc] at h; exact absurd h (by simp)

open Classical in
/-- **Theorem N(d), error probability.**  The rule "stop as soon as some cell has posterior mass
`≥ 1 − γ` and output that cell" outputs a cell other than `x*` with probability at most
`(M−1)γ/(1−γ)`, at every horizon `T` (so, uniformly over all stopping times bounded by `T`). -/
theorem thmN_d_error (M : ℕ) (hM : 2 ≤ M) (ρ γ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (x : ℕ) (hx : x < M) (T : ℕ) :
    val (bias M ρ (haltAt M γ) x) (state M ρ (haltAt M γ))
        (fun h => if haltAt M γ (state M ρ (haltAt M γ) h).q = true
            ∧ ¬ (1 - γ ≤ (state M ρ (haltAt M γ) h).q x) then (1 : ℝ) else 0) T []
      ≤ ((M : ℝ) - 1) * γ / (1 - γ) := by
  set halt : (ℕ → ℝ) → Bool := haltAt M γ with hhalt
  have hp : ∀ t : St, 0 ≤ bias M ρ halt x t ∧ bias M ρ halt x t ≤ 1 :=
    fun t => bias_mem hρ0 hρ1 t
  have hdom : ∀ h' : List Bool,
      (if halt (state M ρ halt h').q = true ∧ ¬ (1 - γ ≤ (state M ρ halt h').q x) then (1 : ℝ)
        else 0) ≤ 0 + (γ / (1 - γ)) * Wodds (state M ρ halt h').q x := by
    intro h'
    have hg := good_state (halt := halt) hM hρ0 hρ1 h'
    have hW := Wodds_pos hg.inv hM hx
    have hqx := hg.inv.pos x hx
    split
    · rename_i hc
      obtain ⟨i, hiM, hile⟩ := haltAt_true hc.1
      have hix : i ≠ x := by
        intro hcon; exact hc.2 (hcon ▸ hile)
      have hpair := hg.inv.pair_le_one hix hiM hx
      have hle : (state M ρ halt h').q x ≤ γ := by linarith
      have hWge : (1 - γ) / γ ≤ Wodds (state M ρ halt h').q x := by
        rw [Wodds, div_le_div_iff₀ hγ0 hqx]
        nlinarith
      have hpos : (0 : ℝ) < γ / (1 - γ) := div_pos hγ0 (by linarith)
      have h3 : γ / (1 - γ) * ((1 - γ) / γ) = 1 := by
        field_simp
        exact div_self (by linarith : (1 : ℝ) - γ ≠ 0)
      rw [zero_add]
      calc (1 : ℝ) = γ / (1 - γ) * ((1 - γ) / γ) := h3.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hWge hpos.le
    · have : (0 : ℝ) ≤ γ / (1 - γ) * Wodds (state M ρ halt h').q x := by
        apply mul_nonneg (le_of_lt (div_pos hγ0 (by linarith))) hW.le
      linarith
  have hmart := odds_mart M hM ρ hρ0 hρ1 halt x hx T
  calc val (bias M ρ halt x) (state M ρ halt)
        (fun h => if halt (state M ρ halt h).q = true ∧ ¬ (1 - γ ≤ (state M ρ halt h).q x)
          then (1 : ℝ) else 0) T []
      ≤ val (bias M ρ halt x) (state M ρ halt)
          (fun h' => 0 + (γ / (1 - γ)) * Wodds (state M ρ halt h').q x) T [] :=
        val_mono (state M ρ halt) hp T [] (fun h' _ => hdom h')
    _ = 0 + (γ / (1 - γ)) * ((M : ℝ) - 1) := by
        rw [val_affine, hmart]
    _ = ((M : ℝ) - 1) * γ / (1 - γ) := by ring

end ThmN

/-! ### Theorem N(d), the query budget

The drift bound `thmN_a` is turned into a bound on the expected number of queries by optional
stopping.  Since the whole development lives at a finite horizon, "optional stopping" here is
just the submartingale principle `val_sub2` applied to `L_n − Cap(ρ)·N_n` at horizon `2T`; the
pathwise ceiling `L_n ≤ log((1−γ)/γ) + log((1−ρ)/ρ)` is the invariant `Ceil`, which holds because
the run is frozen as soon as some cell reaches mass `1 − γ`, and one answer moves `L` by at most
`log((1−ρ)/ρ)` (`abs_logOdds_incr_le`). -/

section Budget

variable {M : ℕ} {ρ γ : ℝ} {x : ℕ} {s : St}

/-- Shifting a state function by a constant shifts its one-query expectation by that constant
(the four branch weights sum to `1`). -/
lemma E2_shift (M : ℕ) (ρ : ℝ) (halt : (ℕ → ℝ) → Bool) (x : ℕ) (W : St → ℝ) (c : ℝ) (t : St) :
    E2 M ρ halt x (fun u => W u - c) t = E2 M ρ halt x W t - c := by
  simp only [E2]
  ring

/-- **Two-round submartingale principle.** -/
lemma val_sub2 (M : ℕ) (ρ : ℝ) (halt : (ℕ → ℝ) → Bool) (x : ℕ) (W : St → ℝ) (P : St → Prop)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hP : ∀ t b, P t → P (step M ρ halt t b))
    (hone : ∀ t : St, P t → t.phase = false → W t ≤ E2 M ρ halt x W t) :
    ∀ (T : ℕ) (h : List Bool), P (state M ρ halt h) → (state M ρ halt h).phase = false →
      W (state M ρ halt h)
        ≤ val (bias M ρ halt x) (state M ρ halt) (fun h' => W (state M ρ halt h')) (2 * T) h := by
  intro T
  induction T with
  | zero => intro h _ _; simp
  | succ T ih =>
    intro h hP0 hph
    have hstep2 : ∀ b b' : Bool,
        state M ρ halt (h ++ [b] ++ [b'])
          = step M ρ halt (step M ρ halt (state M ρ halt h) b) b' := by
      intro b b'; rw [state_append, state_append]
    have key : ∀ b b' : Bool,
        W (step M ρ halt (step M ρ halt (state M ρ halt h) b) b')
          ≤ val (bias M ρ halt x) (state M ρ halt) (fun h' => W (state M ρ halt h')) (2 * T)
              (h ++ [b] ++ [b']) := by
      intro b b'
      have hPb : P (state M ρ halt (h ++ [b] ++ [b'])) := by
        rw [hstep2]; exact hP _ b' (hP _ b hP0)
      have hphb : (state M ρ halt (h ++ [b] ++ [b'])).phase = false := by
        rw [hstep2]; exact step_phase2 hph b b'
      have := ih (h ++ [b] ++ [b']) hPb hphb
      rwa [hstep2] at this
    have hb0 := bias_mem (M := M) (halt := halt) (x := x) hρ0 hρ1 (state M ρ halt h)
    have hb1 := bias_mem (M := M) (halt := halt) (x := x) hρ0 hρ1
      (step M ρ halt (state M ρ halt h) true)
    have hb2 := bias_mem (M := M) (halt := halt) (x := x) hρ0 hρ1
      (step M ρ halt (state M ρ halt h) false)
    have hE := hone (state M ρ halt h) hP0 hph
    rw [E2] at hE
    rw [show 2 * (T + 1) = 2 * T + 2 by ring, val_succ2]
    have hsa : ∀ b : Bool, state M ρ halt (h ++ [b]) = step M ρ halt (state M ρ halt h) b :=
      fun b => state_append M ρ halt h b
    rw [hsa true, hsa false]
    nlinarith [mul_le_mul_of_nonneg_left (key true true) hb1.1,
      mul_le_mul_of_nonneg_left (key true false)
        (by linarith [hb1.2] : (0:ℝ) ≤ 1 - bias M ρ halt x
          (step M ρ halt (state M ρ halt h) true)),
      mul_le_mul_of_nonneg_left (key false true) hb2.1,
      mul_le_mul_of_nonneg_left (key false false)
        (by linarith [hb2.2] : (0:ℝ) ≤ 1 - bias M ρ halt x
          (step M ρ halt (state M ρ halt h) false)),
      hb0.1, hb0.2, hE]

open Classical in
lemma haltAt_false {M : ℕ} {γ : ℝ} {q : ℕ → ℝ} (h : haltAt M γ q = false) :
    ∀ i, i < M → q i < 1 - γ := by
  intro i hi
  by_contra hcon
  push_neg at hcon
  unfold haltAt at h
  rw [if_pos ⟨i, hi, hcon⟩] at h
  exact absurd h (by simp)

/-- The pathwise ceiling on the log-odds carried along the stopped process. -/
structure Ceil (M : ℕ) (ρ γ : ℝ) (x : ℕ) (s : St) : Prop where
  /-- the posterior invariant -/
  good : Good M s
  /-- before a query the log-odds are below `log((1−γ)/γ)`; after one answer, below that plus
  one increment -/
  bound : logOdds s.q x ≤ (if s.phase then Real.log ((1 - γ) / γ)
    else Real.log ((1 - γ) / γ) + Real.log ((1 - ρ) / ρ))

lemma log_ratio_nonneg (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) : 0 ≤ Real.log ((1 - ρ) / ρ) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ hρ0]; linarith

lemma ceil_init (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hγ0 : 0 < γ) (hγ2 : γ ≤ 1 / 2)
    (hx : x < M) : Ceil M ρ γ x (stInit M) := by
  have hg := good_init (M := M) hM
  refine ⟨hg, ?_⟩
  have hM1 : (1 : ℝ) ≤ (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hl : logOdds (stInit M).q x = -Real.log ((M : ℝ) - 1) := by
    rw [logOdds_eq_neg_log hg.inv hM hx, Wodds_init hM hx]
  have h1 : (0 : ℝ) ≤ Real.log ((M : ℝ) - 1) := Real.log_nonneg hM1
  have h2 : (0 : ℝ) ≤ Real.log ((1 - γ) / γ) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hγ0]; linarith
  have h3 := log_ratio_nonneg hρ0 hρ1
  rw [hl]
  have : (stInit M).phase = false := rfl
  rw [this]
  simp only [Bool.false_eq_true, if_false]
  linarith

lemma ceil_step (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hx : x < M) (ht : Ceil M ρ γ x s) (b : Bool) :
    Ceil M ρ γ x (step M ρ (haltAt M γ) s b) := by
  refine ⟨good_step hM hρ0 hρ1 ht.good b, ?_⟩
  by_cases hph : s.phase = true
  · -- an answer round: one increment of at most `log((1−ρ)/ρ)`
    rw [step_answer hph]
    have hinc := abs_logOdds_incr_le (q := s.q) (c := s.cut) ht.good.inv hM hρ0 hρ1 hx
      ht.good.cut_le b
    have hb := ht.bound
    rw [hph] at hb
    simp only [if_true] at hb
    have := (abs_le.1 hinc).2
    simp only [Bool.false_eq_true, if_false]
    linarith
  · rw [Bool.not_eq_true] at hph
    by_cases hh : haltAt M γ s.q = true
    · rw [step_halted hph hh]; exact ht.bound
    · rw [Bool.not_eq_true] at hh
      rw [step_coin hph hh]
      simp only [if_true]
      -- not halted: `q x < 1 − γ`, so `L ≤ log((1−γ)/γ)`
      have hqx : s.q x < 1 - γ := haltAt_false hh x hx
      have hpos : 0 < s.q x := ht.good.inv.pos x hx
      have hu : 0 < 1 - s.q x := by linarith [ht.good.inv.qx_lt_one hM hx]
      rw [logOdds]
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ hu hγ0]
      nlinarith

lemma ceil_foldl (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hx : x < M) :
    ∀ (h : List Bool) (t : St), Ceil M ρ γ x t →
      Ceil M ρ γ x (h.foldl (step M ρ (haltAt M γ)) t) := by
  intro h
  induction h with
  | nil => intro t ht; exact ht
  | cons b l ih => intro t ht; exact ih _ (ceil_step hM hρ0 hρ1 hγ0 hγ1 hx ht b)

lemma ceil_state (hM : 2 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγ2 : γ ≤ 1 / 2) (hx : x < M) (h : List Bool) :
    Ceil M ρ γ x (state M ρ (haltAt M γ) h) :=
  ceil_foldl hM hρ0 hρ1 hγ0 hγ1 hx h _ (ceil_init hM hρ0 hρ1 hγ0 hγ2 hx)

/-- **Theorem N(d), query budget.**  `Cap(ρ)·E[N ∧ T] ≤ log(M−1) + log((1−γ)/γ) + log((1−ρ)/ρ)`
at every horizon `T`, where `N` counts completed queries and the run is frozen as soon as some
cell reaches posterior mass `1 − γ`.  (The note's `E[N] ≤ (…)/Cap(ρ)` is the `T → ∞` limit of
this, by monotone convergence, which is not formalised here.) -/
theorem thmN_d_budget (M : ℕ) (hM : 2 ≤ M) (ρ γ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hγ0 : 0 < γ) (hγ2 : γ ≤ 1 / 2) (x : ℕ) (hx : x < M) (T : ℕ) :
    Cap ρ * val (bias M ρ (haltAt M γ) x) (state M ρ (haltAt M γ))
        (fun h => ((state M ρ (haltAt M γ) h).k : ℝ)) (2 * T) []
      ≤ Real.log ((M : ℝ) - 1) + Real.log ((1 - γ) / γ) + Real.log ((1 - ρ) / ρ) := by
  have hγ1 : γ < 1 := by linarith
  set halt : (ℕ → ℝ) → Bool := haltAt M γ with hhalt
  set Vd : St → ℝ := fun t => logOdds t.q x - Cap ρ * (t.k : ℝ) with hVd
  have hp : ∀ t : St, 0 ≤ bias M ρ halt x t ∧ bias M ρ halt x t ≤ 1 :=
    fun t => bias_mem hρ0 hρ1 t
  -- the one-query submartingale property of `L_n − Cap(ρ)·N_n`
  have hone : ∀ t : St, Ceil M ρ γ x t → t.phase = false → Vd t ≤ E2 M ρ halt x Vd t := by
    intro t ht hph
    by_cases hh : halt t.q = true
    · have hs : ∀ b : Bool, step M ρ halt t b = t := fun b => step_halted hph hh b
      have e : E2 M ρ halt x Vd t = Vd t := by
        rw [E2]
        simp only [hs]
        ring
      rw [e]
    · rw [Bool.not_eq_true] at hh
      have hk : ∀ b b' : Bool, (step M ρ halt (step M ρ halt t b) b').k = t.k + 1 := by
        intro b b'
        rw [step_coin hph hh, step_answer rfl]
      have hcong : E2 M ρ halt x Vd t
          = E2 M ρ halt x (fun u => logOdds u.q x - Cap ρ * ((t.k : ℝ) + 1)) t := by
        refine E2_congr M ρ halt x t (fun b b' => ?_)
        rw [hVd]
        simp only [hk b b']
        push_cast
        ring
      rw [hcong, E2_shift M ρ halt x (fun u => logOdds u.q x) (Cap ρ * ((t.k : ℝ) + 1)) t]
      have hdrift := thmN_a hM hρ0 hρ1 hx ht.good hph hh
      rw [hVd]
      linarith
  have hPstep : ∀ (t : St) (b : Bool), Ceil M ρ γ x t → Ceil M ρ γ x (step M ρ halt t b) :=
    fun t b ht => ceil_step hM hρ0 hρ1 hγ0 hγ1 hx ht b
  have hsub := val_sub2 M ρ halt x Vd (Ceil M ρ γ x) hρ0 hρ1 hPstep hone T []
    (by rw [state_nil]; exact ceil_init hM hρ0 hρ1 hγ0 hγ2 hx) rfl
  rw [state_nil] at hsub
  -- split the expectation
  have hfun : (fun h => Vd (state M ρ halt h))
      = fun h => logOdds (state M ρ halt h).q x
          + (0 + (-(Cap ρ)) * ((state M ρ halt h).k : ℝ)) := by
    funext h; rw [hVd]; ring
  have hsplit : val (bias M ρ halt x) (state M ρ halt) (fun h => Vd (state M ρ halt h)) (2 * T) []
      = val (bias M ρ halt x) (state M ρ halt)
            (fun h => logOdds (state M ρ halt h).q x) (2 * T) []
        + (0 + (-(Cap ρ)) * val (bias M ρ halt x) (state M ρ halt)
            (fun h => ((state M ρ halt h).k : ℝ)) (2 * T) []) := by
    rw [hfun, val_add, val_affine]
  -- the pathwise ceiling
  have hceil : val (bias M ρ halt x) (state M ρ halt)
      (fun h => logOdds (state M ρ halt h).q x) (2 * T) []
      ≤ Real.log ((1 - γ) / γ) + Real.log ((1 - ρ) / ρ) := by
    have hdom : ∀ h' : List Bool, logOdds (state M ρ halt h').q x
        ≤ Real.log ((1 - γ) / γ) + Real.log ((1 - ρ) / ρ) := by
      intro h'
      have hc := ceil_state hM hρ0 hρ1 hγ0 hγ1 hγ2 hx h'
      have hb := hc.bound
      have h3 := log_ratio_nonneg hρ0 hρ1
      rcases Bool.eq_false_or_eq_true (state M ρ halt h').phase with he | he <;>
        rw [he] at hb <;> simp only [Bool.false_eq_true, if_false, if_true] at hb <;> linarith
    calc val (bias M ρ halt x) (state M ρ halt)
          (fun h => logOdds (state M ρ halt h).q x) (2 * T) []
        ≤ val (bias M ρ halt x) (state M ρ halt)
            (fun _ => Real.log ((1 - γ) / γ) + Real.log ((1 - ρ) / ρ)) (2 * T) [] :=
          val_mono (state M ρ halt) hp (2 * T) [] (fun h' _ => hdom h')
      _ = _ := val_const _ _ _ _ _
  have hk0 : ((stInit M).k : ℝ) = 0 := by norm_num [stInit]
  have hV0 : Vd (stInit M) = -Real.log ((M : ℝ) - 1) := by
    show logOdds (stInit M).q x - Cap ρ * ((stInit M).k : ℝ) = -Real.log ((M : ℝ) - 1)
    rw [logOdds_eq_neg_log (good_init hM).inv hM hx, Wodds_init hM hx, hk0]
    ring
  rw [hsplit, hV0] at hsub
  linarith

end Budget

end NoisySearch

end OracleBounds.Attacks
