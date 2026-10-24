import OracleBounds.V6.Process
import OracleBounds.V6.Geometry

/-!
# Operational theorems for one face of a planted gallery (v6 Cor 4.2, Thm 7.1, Prop 7.3,
# Thm 6.1 (3), Thm 10.1)

All proved, no `sorry`s.

**Setting (`FaceSetting`).** Fix face `i` and its environment `Eᵢ = (U = u, W₋ᵢ, V⁽⁻ⁱ⁾)`.
* `S` — the caps still free for face `i` (`[M] ∖ W₋ᵢ`); given `Eᵢ`, `Wᵢ` is uniform on `S`, so the
  plant probability of an event is the average over `w ∈ S` (we bound `(∑_{w∈S} P_w[·]) / |S|`).
* `z w` — cap centres; `g w` — face `i`'s template when it sits in cap `w` (any fine index; the bounds
  hold for every choice, hence also averaged over `V⁽ⁱ⁾`), with `‖g w − z w‖ ≤ r₀`.
* `κ s` — probability of answer bit 1 at score `s`, `ζ`-band-null w.r.t. `ν₀` below `thr = τ − δ`.
* `m x` — the maximum score over the other `n − 1` faces (a function of `Eᵢ`).
* true response probability at probe `x`: `κ (max ⟨x, g w⟩ (m x))`; ghost: `κ (m x)`.
* reach of cap `w`: `⟨x, z w⟩ > thr − r₀ = t₀`.
Coverage `#{w ∈ S : x ∈ reach w} ≤ μ₁M` and `|S| = M − n + 1` are hypotheses of each theorem.
Probes and outputs are unit vectors (`Sph E`).

**What differs from v6.** The proofs here bound "hit, or some output lands near cap `w`" by a
union bound under the ghost law (`ghost_union_bound`) instead of conditioning on the unhit caps.
This needs neither the unhit-cap count `≥ M/2` (false in general; F2) nor `Q ≤ 1/(4μ₁)`, and it
recovers v6's *stated* constants under condition (1) `2n ≤ M`:
* Cor 4.2: `2μ₁Q + 2Qζ` (as stated).
* Thm 7.1: `2μ₁(Q + k_out) + 2Qζ` under `2n ≤ M` only (v6 assumed `8n ≤ M`, `4μ₁Q ≤ 1`).
* Prop 7.3 / Thm 6.1 (3): `2μ₁Q + 2k_out/M + 2Qζ` per face (v6: same with `8Qζ`; F2's proposed
  constant change is unnecessary).
* Thm 10.1: `≥ 3/8·(1 − 2μ₁Q − 2k_out/M − 2Qζ)`, which is `≥ 1/5` under v6's hypotheses.
-/

namespace OracleBounds.V6

open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Cap : Type*}

/-- Unit vectors: probes and outputs live on the sphere. -/
abbrev Sph (E : Type*) [NormedAddCommGroup E] := {x : E // ‖x‖ = 1}

/-- One face of a planted gallery with its environment fixed (see module docstring). -/
structure FaceSetting (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Cap : Type*) where
  S : Finset Cap
  z : Cap → E
  g : Cap → E
  thr : ℝ
  r₀ : ℝ
  κ : ℝ → ℝ
  ν₀ : ℝ
  ζ : ℝ
  m : E → ℝ
  hg : ∀ w ∈ S, ‖g w - z w‖ ≤ r₀
  hκ : ∀ s, 0 ≤ κ s ∧ κ s ≤ 1
  hband : ∀ s ≤ thr, |κ s - ν₀| ≤ ζ

namespace FaceSetting

variable (F : FaceSetting E Cap)

/-- Reach of cap `w`: `R_w = {x : ⟨x, z_w⟩ > t₀}`, `t₀ = τ − δ − r₀`. -/
def reach (w : Cap) (x : Sph E) : Prop := F.thr - F.r₀ < inner ℝ x.1 (F.z w)

/-- True response probability (face `i` in cap `w`). -/
noncomputable def pT (w : Cap) (x : Sph E) : ℝ := F.κ (max (inner ℝ x.1 (F.g w)) (F.m x.1))

/-- Ghost response probability (face `i` deleted). -/
noncomputable def pG (x : Sph E) : ℝ := F.κ (F.m x.1)

lemma ζ_nonneg : 0 ≤ F.ζ := (abs_nonneg _).trans (F.hband F.thr le_rfl)

lemma pT_mem (w : Cap) (x : Sph E) : 0 ≤ F.pT w x ∧ F.pT w x ≤ 1 := F.hκ _
lemma pG_mem (x : Sph E) : 0 ≤ F.pG x ∧ F.pG x ≤ 1 := F.hκ _

/-- Locality: off the reach of `w`, true and ghost responses are within `2ζ`. -/
lemma loc : ∀ w ∈ F.S, ∀ x, ¬ F.reach w x → |F.pT w x - F.pG x| ≤ 2 * F.ζ := by
  intro w hw x hx
  apply kernel_locality F.κ F.ν₀ F.ζ F.thr F.hband
  by_contra h
  push Not at h
  exact hx (reach_of_match x.2 (F.hg w hw) h)

end FaceSetting

/-- Averaging step used by every theorem below: under condition (1) `2n ≤ M` and
`|S| = M − n + 1`, a sum bound `Σ ≤ T + a·|S|` (`T ≥ 0`) becomes the average bound
`Σ/|S| ≤ 2T/M + a`. This is where v6's `M/(M − n + 1) ≤ 2` (Cor 4.2) enters. -/
lemma avg_le {M n : ℕ} {s σ T a : ℝ} (hM : 0 < M) (hn : 2 * n ≤ M) (hs : s = M - n + 1)
    (hT : 0 ≤ T) (h : σ ≤ T + a * s) : σ / s ≤ 2 * T / M + a := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hn' : (2 * n : ℝ) ≤ M := by exact_mod_cast hn
  have hs' : (M : ℝ) / 2 ≤ s := by rw [hs]; linarith
  have hspos : 0 < s := by linarith
  have h1 : σ / s ≤ T / s + a := by
    rw [div_add' _ _ _ hspos.ne', div_le_div_iff_of_pos_right hspos]; linarith
  have h2 : T / s ≤ 2 * T / M := by
    rw [div_le_div_iff₀ hspos hM']; nlinarith
  linarith

open Classical

namespace FaceSetting

variable (F : FaceSetting E Cap)

/-- **Corollary 4.2 (hitting).** Averaged over `Wᵢ` uniform on the free caps,
`P[T⁽ⁱ⁾ ≤ Q] ≤ 2μ₁Q + 2Qζ`, for every adaptive attacker and every horizon `Q`. -/
theorem cor42_hitting (probe : List Bool → Sph E) (Q M n : ℕ) (μ : ℝ) (hM : 0 < M)
    (hn : 2 * n ≤ M) (hcard : (F.S.card : ℝ) = M - n + 1) (hμ : 0 ≤ μ)
    (hcov : ∀ x, ((F.S.filter (F.reach · x)).card : ℝ) ≤ μ * M) :
    (∑ w ∈ F.S, val (F.pT w) probe (hitInd F.reach probe w) Q []) / F.S.card
      ≤ 2 * μ * Q + 2 * Q * F.ζ := by
  have hb := ghost_union_bound F.S F.reach probe F.pT F.pG F.ζ (μ * M) 0 Q
    (hitInd F.reach probe) (fun _ _ => 0) F.pT_mem F.pG_mem F.ζ_nonneg F.loc hcov
    (fun _ _ => by norm_num) (fun _ _ => by simp) (fun _ _ _ _ => by simp)
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  refine le_trans (avg_le (T := Q * (μ * M)) (a := 2 * Q * F.ζ) hM hn hcard
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hμ (Nat.cast_nonneg _))) (by linarith)) (le_of_eq ?_)
  field_simp

/-- **Theorem 7.1 (impersonation).** Say `x` *matches* face `i` if `⟨x, g⟩ > τ − δ`. Averaged over
`Wᵢ`, the probability that some probe or some output point matches face `i` is at most
`2μ₁(Q + k_out) + 2Qζ`. Hypotheses: condition (1) only — v6's `n ≤ M/8` and `Q ≤ 1/(4μ₁)` are not
needed. -/
theorem thm71_impersonation (probe : List Bool → Sph E) (kout : ℕ)
    (out : List Bool → Fin kout → Sph E) (Q M n : ℕ) (μ : ℝ) (hM : 0 < M) (hn : 2 * n ≤ M)
    (hcard : (F.S.card : ℝ) = M - n + 1) (hμ : 0 ≤ μ)
    (hcov : ∀ x, ((F.S.filter (F.reach · x)).card : ℝ) ≤ μ * M) :
    (∑ w ∈ F.S, val (F.pT w) probe (fun h =>
        if (∃ k < h.length, F.thr < inner ℝ (probe (h.take k)).1 (F.g w)) ∨
          (∃ j, F.thr < inner ℝ (out h j).1 (F.g w)) then 1 else 0) Q []) / F.S.card
      ≤ 2 * μ * (Q + kout) + 2 * Q * F.ζ := by
  set A : Cap → List Bool → ℝ := fun w h =>
    if (∃ k < h.length, F.thr < inner ℝ (probe (h.take k)).1 (F.g w)) ∨
      (∃ j, F.thr < inner ℝ (out h j).1 (F.g w)) then 1 else 0 with hA
  set Eout : Cap → List Bool → ℝ := fun w h => if ∃ j, F.reach w (out h j) then 1 else 0 with hEout
  have hE01 : ∀ w h, 0 ≤ Eout w h ∧ Eout w h ≤ 1 := by
    intro w h; simp only [hEout]; split_ifs <;> norm_num
  have hK : ∀ h : List Bool, h.length = Q → ∑ w ∈ F.S, Eout w h ≤ kout * (μ * M) := by
    intro h _
    have := card_reached_le F.S F.reach (μ * M) hcov (Finset.univ : Finset (Fin kout)) (out h)
    rw [Finset.card_univ, Fintype.card_fin] at this
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun w _ => ?_)) this
    by_cases hx : ∃ j, F.reach w (out h j) <;> simp [hEout, hx]
  have hAle : ∀ w ∈ F.S, ∀ h : List Bool, h.length = Q →
      A w h ≤ 1 - (1 - hitInd F.reach probe w h) * (1 - Eout w h) := by
    intro w hw h _
    have hit01 : 0 ≤ hitInd F.reach probe w h ∧ hitInd F.reach probe w h ≤ 1 := by
      unfold hitInd; split_ifs <;> norm_num
    have := hE01 w h
    simp only [hA]
    split_ifs with hcase
    · rcases hcase with ⟨k, hk, hm⟩ | ⟨j, hm⟩
      · have h1 : hitInd F.reach probe w h = 1 := by
          unfold hitInd
          rw [if_pos ⟨k, hk, reach_of_match (probe (h.take k)).2 (F.hg w hw) hm⟩]
        rw [h1]; simp
      · have h1 : Eout w h = 1 := by
          simp only [hEout]; rw [if_pos ⟨j, reach_of_match (out h j).2 (F.hg w hw) hm⟩]
        rw [h1]; simp
    · nlinarith
  have hb := ghost_union_bound F.S F.reach probe F.pT F.pG F.ζ (μ * M) (kout * (μ * M)) Q
    A Eout F.pT_mem F.pG_mem F.ζ_nonneg F.loc hcov hE01 hK hAle
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  refine le_trans (avg_le (T := (Q + kout) * (μ * M)) (a := 2 * Q * F.ζ) hM hn hcard
    (mul_nonneg (by positivity) (mul_nonneg hμ (Nat.cast_nonneg _))) (by linarith)) (le_of_eq ?_)
  field_simp

/-- Indicator that some output point lies within `1/2` of the centre of cap `w`. -/
noncomputable def nearInd {k : ℕ} (out : List Bool → Fin k → Sph E) (w : Cap) (h : List Bool) : ℝ :=
  if ∃ j, ‖(out h j).1 - F.z w‖ ≤ 1 / 2 then 1 else 0

lemma nearInd_mem {k : ℕ} (out : List Bool → Fin k → Sph E) (w : Cap) (h : List Bool) :
    0 ≤ F.nearInd out w h ∧ F.nearInd out w h ≤ 1 := by
  unfold nearInd; split_ifs <;> norm_num

/-- Sum bound for "some output lands within `1/2` of the true cap centre". -/
theorem near_sum_bound (probe : List Bool → Sph E) (kout : ℕ)
    (out : List Bool → Fin kout → Sph E)
    (hz : ∀ w ∈ F.S, ‖F.z w‖ = 1) (hsep : ∀ w ∈ F.S, ∀ w' ∈ F.S, w ≠ w' → 1 ≤ ‖F.z w - F.z w'‖)
    (Q : ℕ) (c : ℝ) (hcov : ∀ x, ((F.S.filter (F.reach · x)).card : ℝ) ≤ c) :
    ∑ w ∈ F.S, val (F.pT w) probe (F.nearInd out w) Q [] ≤ Q * c + kout + 2 * Q * F.ζ * F.S.card := by
  have hK : ∀ h : List Bool, h.length = Q → ∑ w ∈ F.S, F.nearInd out w h ≤ kout := by
    intro h _
    have := card_near_le F.S F.z hz hsep (fun j => (out h j).1) (fun j => (out h j).2)
    simp only [nearInd, Finset.sum_boole]
    exact_mod_cast this
  exact ghost_union_bound F.S F.reach probe F.pT F.pG F.ζ c kout Q
    (F.nearInd out) (F.nearInd out) F.pT_mem F.pG_mem F.ζ_nonneg F.loc hcov (F.nearInd_mem out) hK
    (by
      intro w _ h _
      have := F.nearInd_mem out w h
      have : 0 ≤ hitInd F.reach probe w h ∧ hitInd F.reach probe w h ≤ 1 := by
        unfold hitInd; split_ifs <;> norm_num
      nlinarith)

/-- **Proposition 7.3 / Theorem 6.1 (3), one face.** If `ε + r₀ ≤ 1/2` (e.g. `ε ≤ 3/8`,
`r₀ ≤ 1/8`), centres are unit and 1-separated, then averaged over `Wᵢ`,
`P[face i recovered at precision ε] ≤ 2μ₁Q + 2k_out/M + 2Qζ`. Summing over the `n` faces (and
using `P ≤ 1`) gives `E[N_ε(Q)] ≤ n·min{1, 2μ₁Q + 2k_out/M + 2Qζ}`, which implies v6's (3). -/
theorem prop73_coarse_recovery (probe : List Bool → Sph E) (kout : ℕ)
    (out : List Bool → Fin kout → Sph E) (ε : ℝ) (hε : ε + F.r₀ ≤ 1 / 2)
    (hz : ∀ w ∈ F.S, ‖F.z w‖ = 1) (hsep : ∀ w ∈ F.S, ∀ w' ∈ F.S, w ≠ w' → 1 ≤ ‖F.z w - F.z w'‖)
    (Q M n : ℕ) (μ : ℝ) (hM : 0 < M) (hn : 2 * n ≤ M)
    (hcard : (F.S.card : ℝ) = M - n + 1) (hμ : 0 ≤ μ)
    (hcov : ∀ x, ((F.S.filter (F.reach · x)).card : ℝ) ≤ μ * M) :
    (∑ w ∈ F.S, val (F.pT w) probe (fun h =>
        if ∃ j, ‖(out h j).1 - F.g w‖ ≤ ε then 1 else 0) Q []) / F.S.card
      ≤ 2 * μ * Q + 2 * kout / M + 2 * Q * F.ζ := by
  have hb := F.near_sum_bound probe kout out hz hsep Q (μ * M) hcov
  have hle : ∀ w ∈ F.S, val (F.pT w) probe (fun h => if ∃ j, ‖(out h j).1 - F.g w‖ ≤ ε then 1 else 0)
      Q [] ≤ val (F.pT w) probe (F.nearInd out w) Q [] := by
    intro w hw
    apply val_mono probe (F.pT_mem w)
    intro h _
    unfold nearInd
    split_ifs with h1 h2
    · exact le_rfl
    · obtain ⟨j, hj⟩ := h1; exact absurd ⟨j, near_of_close hj (F.hg w hw) hε⟩ h2
    · norm_num
    · exact le_rfl
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  refine le_trans (avg_le (T := Q * (μ * M) + kout) (a := 2 * Q * F.ζ) hM hn hcard
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hμ (Nat.cast_nonneg _)))
      (Nat.cast_nonneg _))
    (by linarith [Finset.sum_le_sum hle])) (le_of_eq ?_)
  field_simp

/-- **Theorem 10.1 (per-specified-face plateau), general form.** With `r₀ ≤ 1/8`, unit
1-separated centres and `k_out = k + 1` outputs, averaged over `Wᵢ`,
`E[min_j ‖ĝ_j − g⁽ⁱ⁾‖] ≥ 3/8 · (1 − 2μ₁Q − 2k_out/M − 2Qζ)`. -/
theorem thm101_plateau (probe : List Bool → Sph E) (k : ℕ)
    (out : List Bool → Fin (k + 1) → Sph E) (hr : F.r₀ ≤ 1 / 8)
    (hz : ∀ w ∈ F.S, ‖F.z w‖ = 1) (hsep : ∀ w ∈ F.S, ∀ w' ∈ F.S, w ≠ w' → 1 ≤ ‖F.z w - F.z w'‖)
    (Q M n : ℕ) (μ : ℝ) (hM : 0 < M) (hn : 2 * n ≤ M)
    (hcard : (F.S.card : ℝ) = M - n + 1) (hμ : 0 ≤ μ)
    (hcov : ∀ x, ((F.S.filter (F.reach · x)).card : ℝ) ≤ μ * M) :
    3 / 8 * (1 - (2 * μ * Q + 2 * ((k + 1 : ℕ) : ℝ) / M + 2 * Q * F.ζ)) ≤
    (∑ w ∈ F.S, val (F.pT w) probe (fun h =>
        Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out h j).1 - F.g w‖)) Q []) / F.S.card := by
  have hb := F.near_sum_bound probe (k + 1) out hz hsep Q (μ * M) hcov
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have havg := avg_le (σ := ∑ w ∈ F.S, val (F.pT w) probe (F.nearInd out w) Q [])
    (T := Q * (μ * M) + ((k + 1 : ℕ) : ℝ)) (a := 2 * Q * F.ζ) hM hn hcard
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hμ (Nat.cast_nonneg _)))
      (Nat.cast_nonneg _)) (by linarith)
  have hT : 2 * (Q * (μ * M) + ((k + 1 : ℕ) : ℝ)) / M = 2 * μ * Q + 2 * ((k + 1 : ℕ) : ℝ) / M := by
    field_simp
  rw [hT] at havg
  -- pathwise: loss ≥ 3/8 · (1 − nearInd)
  have hmono : ∀ w ∈ F.S, 3 / 8 * (1 - val (F.pT w) probe (F.nearInd out w) Q []) ≤
      val (F.pT w) probe (fun h =>
        Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out h j).1 - F.g w‖)) Q [] := by
    intro w hw
    have := val_mono probe (F.pT_mem w) (F := fun h => 3 / 8 + (-3 / 8) * F.nearInd out w h)
      (G := fun h => Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out h j).1 - F.g w‖)) Q []
      (by
        intro h _
        simp only [nearInd]
        split_ifs with hc
        · simp only [Finset.le_inf'_iff]; intros; norm_num
        · push Not at hc
          simp only [Finset.le_inf'_iff]
          intro j _
          have := far_of_not_near (hc j) (F.hg w hw) hr
          linarith)
    rw [val_affine] at this
    linarith
  have hpos : (0 : ℝ) < F.S.card := by
    have hn' : (2 * n : ℝ) ≤ M := by exact_mod_cast hn
    rw [hcard]; linarith
  have hsum := Finset.sum_le_sum hmono
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  rw [le_div_iff₀ hpos]
  have h2 : ∑ w ∈ F.S, val (F.pT w) probe (F.nearInd out w) Q [] ≤
      (2 * μ * Q + 2 * ((k + 1 : ℕ) : ℝ) / M + 2 * Q * F.ζ) * F.S.card := by
    rwa [div_le_iff₀ hpos] at havg
  nlinarith

/-- **Theorem 10.1 as stated** (`ζ = 0`, `16n ≤ M`, `16μ₁Q ≤ 1`, `16k_out ≤ M`): the average
nearest-output distance to face `i` is at least `1/5` (in fact `≥ 9/32` by this argument). -/
theorem thm101_as_stated (probe : List Bool → Sph E) (k : ℕ)
    (out : List Bool → Fin (k + 1) → Sph E) (hr : F.r₀ ≤ 1 / 8) (hζ : F.ζ = 0)
    (hz : ∀ w ∈ F.S, ‖F.z w‖ = 1) (hsep : ∀ w ∈ F.S, ∀ w' ∈ F.S, w ≠ w' → 1 ≤ ‖F.z w - F.z w'‖)
    (Q M n : ℕ) (μ : ℝ) (hM : 0 < M) (hn : 16 * n ≤ M) (hQ : 16 * μ * Q ≤ 1)
    (hk : 16 * (k + 1) ≤ M)
    (hcard : (F.S.card : ℝ) = M - n + 1) (hμ : 0 ≤ μ)
    (hcov : ∀ x, ((F.S.filter (F.reach · x)).card : ℝ) ≤ μ * M) :
    1 / 5 ≤ (∑ w ∈ F.S, val (F.pT w) probe (fun h =>
        Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out h j).1 - F.g w‖)) Q []) / F.S.card := by
  have h := F.thm101_plateau probe k out hr hz hsep Q M n μ hM (by omega) hcard hμ hcov
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hk' : ((16 * (k + 1) : ℕ) : ℝ) ≤ M := by exact_mod_cast hk
  push_cast at hk'
  have hkM : 2 * ((k + 1 : ℕ) : ℝ) / M ≤ 1 / 8 := by
    rw [div_le_iff₀ hM']; push_cast; linarith
  rw [hζ] at h
  refine le_trans ?_ h
  nlinarith

end FaceSetting

end OracleBounds.V6
