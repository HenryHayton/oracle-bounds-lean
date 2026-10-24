import OracleBounds.GeneralPrior.Corollaries

/-!
# Density priors: the dimension law (`n-face-general-prior-v2` §13; P1 Cor P.1, P.2)

v2 §13 turns the abstract prior parameters into explicit functions of the effective dimension
`d_eff`, the thresholds and `ε`, for a prior with density `≤ D` on the unit sphere of a
`d_eff`-dimensional subspace `Kᵢ`. Two ingredients:

1. **Projection** (elementary, proved here): a reach cap, acceptance cap or chordal ball of the
   ambient sphere meets `S(Kᵢ)` inside a cap/ball of the same kind *centred on `S(Kᵢ)`*
   (`proj_inner_ge`, `proj_ball`). v2 proves the ball case with radius `2ε`; the projection
   gives radius `ε` (`proj_ball`) — a factor `2^{d_eff−1}` in `p(ε)`, i.e.
   `(d_eff−1)·log 2` nats in `Λ(ε)`.
2. **Cap measure** (v2 Lemma 13.0 with the density bound): `πᵢ(B̄(y′, r)) ≤ D·r^{d_eff−1}` for
   centres `y′ ∈ S(Kᵢ)`. Per the repo convention for sphere geometry this enters as the labelled
   hypothesis `hcapD`, required only for radii `r ≥ r_min`: a continuous density prior has
   `r_min = 0`; a finite prior (an empirical pool, a fine discretisation) satisfies it above its
   resolution, which is all the theorems use.

Results: `density_params` (v2 Prop 13.1, with `ε` for `2ε`), `blind_counts` (P.1),
`blind_m_of_n` (P.2 / Cor 6.3 Q₁), `blind_staircase` (P.2(i)), `blind_risk_floor` (v2 Cor 13.2,
with `½` for `¼`).

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Projection onto the face subspace -/

section Projection

variable (K : Submodule ℝ E) [K.HasOrthogonalProjection]

/-- The normalised projection of `y` onto `K` (a point of `S(K)` when `Py ≠ 0`). -/
noncomputable def projUnit (y : E) : E := ‖K.starProjection y‖⁻¹ • K.starProjection y

lemma inner_proj_eq (y g : E) (hg : g ∈ K) : inner ℝ (K.starProjection y) g = inner ℝ y g := by
  have h := K.starProjection_inner_eq_zero y g hg
  rw [inner_sub_left] at h
  linarith

/-- **Projection lemma.** If `⟨y, g⟩ ≥ t > 0` for a unit `g ∈ K` and `‖y‖ ≤ 1`, then the projection
of `y` is nonzero, its normalisation lies on `S(K)`, and `⟨projUnit y, g⟩ ≥ ⟨y, g⟩`. -/
lemma proj_inner_ge (y g : E) (hy : ‖y‖ ≤ 1) (hg : g ∈ K) (hpos : 0 < inner ℝ y g) :
    K.starProjection y ≠ 0 ∧ projUnit K y ∈ K ∧ ‖projUnit K y‖ = 1 ∧
      inner ℝ y g ≤ inner ℝ (projUnit K y) g := by
  have hPy : inner ℝ (K.starProjection y) g = inner ℝ y g := inner_proj_eq K y g hg
  have hne : K.starProjection y ≠ 0 := by
    intro h0; rw [h0, inner_zero_left] at hPy; linarith
  have hn0 : 0 < ‖K.starProjection y‖ := norm_pos_iff.2 hne
  have hn1 : ‖K.starProjection y‖ ≤ 1 := (K.norm_starProjection_apply_le y).trans hy
  refine ⟨hne, K.smul_mem _ (K.starProjection_apply_mem y), ?_, ?_⟩
  · unfold projUnit
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn0.ne']
  · unfold projUnit
    rw [real_inner_smul_left, hPy]
    rw [le_inv_mul_iff₀ hn0]
    nlinarith

/-- **Balls, radius `ε` (not `2ε`).** A unit `g ∈ K` within chordal distance `ε < √2` of a unit
`y` is within `ε` of `projUnit y ∈ S(K)`. -/
lemma proj_ball (y g : E) (hy : ‖y‖ = 1) (hg : g ∈ K) (hgn : ‖g‖ = 1) (ε : ℝ)
    (hε : ε ^ 2 < 2) (hd : ‖y - g‖ ≤ ε) : ‖projUnit K y - g‖ ≤ ε := by
  have hsq : ∀ u : E, ‖u‖ = 1 → ‖u - g‖ ^ 2 = 2 * (1 - inner ℝ u g) := fun u hu => by
    rw [norm_sub_sq_real, hu, hgn]; ring
  have h1 : 1 - ε ^ 2 / 2 ≤ inner ℝ y g := by
    have := hsq y hy
    have : ‖y - g‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    linarith
  obtain ⟨-, -, hu, hge⟩ := proj_inner_ge K y g hy.le hg (by linarith)
  have h2 : ‖projUnit K y - g‖ ^ 2 ≤ ε ^ 2 := by rw [hsq _ hu]; linarith
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hd
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε0 (by norm_num)).1 h2

end Projection

/-! ### Prop 13.1 for the gallery -/

/-- Mass comparison: if every positive-mass atom satisfying `P` satisfies `R`, the `P`-mass is at
most the `R`-mass. -/
lemma mass_mono {Fine : Type*} [Fintype Fine] (π : Fine → ℝ) (hπ : ∀ l, 0 ≤ π l)
    (P R : Fine → Prop) [DecidablePred P] [DecidablePred R]
    (h : ∀ l, 0 < π l → P l → R l) :
    (∑ l ∈ Finset.univ.filter P, π l) ≤ ∑ l ∈ Finset.univ.filter R, π l := by
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hP : P l
  · rcases eq_or_lt_of_le (hπ l) with h0 | h0
    · rw [← h0]; split_ifs <;> rfl
    · rw [if_pos hP, if_pos (h l h0 hP)]
  · rw [if_neg hP]; split_ifs
    · exact hπ l
    · exact le_rfl

variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]

namespace Gallery

variable (G : Gallery E ι Fine)

/-- **Standing assumptions of v2 §13**, finite-prior form: face `i` lives on `S(Kᵢ)`, and its
ball masses about centres on `S(Kᵢ)` obey `D·r^{d_eff−1}` for `r ≥ r_min` (density `≤ D` plus
v2 Lemma 13.0; labelled hypothesis). -/
structure DensityHyp (K : ι → Submodule ℝ E) (deff : ℕ) (D rmin : ℝ) : Prop where
  hD : 1 ≤ D
  hdeff : 2 ≤ deff
  hsupp : ∀ i l, 0 < G.π i l → G.g l ∈ K i
  hcapD : ∀ i (y : E), y ∈ K i → ‖y‖ = 1 → ∀ r, rmin ≤ r →
    (∑ l ∈ Finset.univ.filter (fun l => ‖y - G.g l‖ ≤ r), G.π i l) ≤ D * r ^ (deff - 1)

open Classical in
/-- **v2 Prop 13.1 (sharpened).** Under the density hypothesis, with `r_t = √(2(1−t))`:
`μ₁ ≤ D·r_thr^{d_eff−1} = D(2(1−thr))^{(d_eff−1)/2}`, `μ_acc ≤ D·r_{τacc}^{d_eff−1}`, and
`p(ε) ≤ D·ε^{d_eff−1}` (v2: `D(2ε)^{d_eff−1}`). -/
theorem density_params (K : ι → Submodule ℝ E) [∀ i, (K i).HasOrthogonalProjection]
    (deff : ℕ) (D rmin : ℝ) (H : G.DensityHyp K deff D rmin) (hthr : 0 < G.thr) :
    (rmin ≤ Face.chordRad G.thr → ∀ i (x : Sph E),
      (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ D * Face.chordRad G.thr ^ (deff - 1)) ∧
    (rmin ≤ Face.chordRad G.τacc → ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (G.acceptsG · y), G.π i l) ≤ D * Face.chordRad G.τacc ^ (deff - 1)) ∧
    (∀ ε, 0 ≤ ε → rmin ≤ ε → ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ D * ε ^ (deff - 1)) := by
  have hcap_cap : ∀ (t : ℝ), 0 < t → rmin ≤ Face.chordRad t → ∀ i (y : Sph E)
      (P : Fine → Prop) [DecidablePred P], (∀ l, P l → t ≤ inner ℝ y.1 (G.g l)) →
      (∑ l ∈ Finset.univ.filter P, G.π i l) ≤ D * Face.chordRad t ^ (deff - 1) := by
    intro t ht hr i y P _ hP
    set y' := projUnit (K i) y.1
    -- every positive-mass atom in `P` is within `r_t` of `y' ∈ S(Kᵢ)`
    by_cases hex : ∃ l, 0 < G.π i l ∧ P l
    · obtain ⟨l₀, hl₀, hPl₀⟩ := hex
      have hK0 := H.hsupp i l₀ hl₀
      obtain ⟨-, hy'K, hy'n, -⟩ := proj_inner_ge (K i) y.1 (G.g l₀) y.2.le hK0
        (by linarith [hP l₀ hPl₀])
      refine le_trans (mass_mono (G.π i) (G.hπ0 i) P (fun l => ‖y' - G.g l‖ ≤ Face.chordRad t)
        fun l hl hPl => ?_) (H.hcapD i y' hy'K hy'n _ hr)
      have hKl := H.hsupp i l hl
      have hge := (proj_inner_ge (K i) y.1 (G.g l) y.2.le hKl
        (by linarith [hP l hPl])).2.2.2
      have hsq : ‖y' - G.g l‖ ^ 2 = 2 * (1 - inner ℝ y' (G.g l)) := by
        rw [norm_sub_sq_real, hy'n, G.hg l]; ring
      unfold Face.chordRad
      rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (by rw [hsq]; linarith [hP l hPl])
    · push Not at hex
      calc (∑ l ∈ Finset.univ.filter P, G.π i l) = 0 :=
            Finset.sum_eq_zero fun l hl =>
              le_antisymm (not_lt.1 fun h => absurd (Finset.mem_filter.1 hl).2 (hex l h)) (G.hπ0 i l)
        _ ≤ D * Face.chordRad t ^ (deff - 1) :=
            mul_nonneg (by linarith [H.hD]) (pow_nonneg (Real.sqrt_nonneg _) _)
  refine ⟨fun hr i x => hcap_cap G.thr hthr hr i x _ fun l hl => le_of_lt hl,
    fun hr i y => hcap_cap G.τacc (hthr.trans G.hτ) hr i y _ fun l hl => hl,
    fun ε hε0 hε i y => ?_⟩
  by_cases hbig : 2 ≤ ε ^ 2
  · -- trivial range: `D ε^{d−1} ≥ 1 ≥` any mass
    have hε1 : 1 ≤ ε := by nlinarith
    calc (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l)
        ≤ ∑ l, G.π i l := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun l _ _ => G.hπ0 i l
      _ = 1 := G.hπ1 i
      _ ≤ D * ε ^ (deff - 1) := by nlinarith [one_le_pow₀ (n := deff - 1) hε1, H.hD]
  · push Not at hbig
    by_cases hex : ∃ l, 0 < G.π i l ∧ ‖y.1 - G.g l‖ ≤ ε
    · obtain ⟨l₀, hl₀, hd₀⟩ := hex
      obtain ⟨-, hy'K, hy'n, -⟩ := proj_inner_ge (K i) y.1 (G.g l₀) y.2.le (H.hsupp i l₀ hl₀)
        (by
          have := proj_ball (K i) y.1 (G.g l₀) y.2 (H.hsupp i l₀ hl₀) (G.hg l₀) ε hbig hd₀
          have hsq : ‖y.1 - G.g l₀‖ ^ 2 = 2 * (1 - inner ℝ y.1 (G.g l₀)) := by
            rw [norm_sub_sq_real, y.2, G.hg l₀]; ring
          nlinarith [pow_le_pow_left₀ (norm_nonneg _) hd₀ 2])
      exact le_trans (mass_mono (G.π i) (G.hπ0 i) _
        (fun l => ‖projUnit (K i) y.1 - G.g l‖ ≤ ε)
        fun l hl hd => proj_ball (K i) y.1 (G.g l) y.2 (H.hsupp i l hl) (G.hg l) ε hbig hd)
        (H.hcapD i _ hy'K hy'n ε hε)
    · push Not at hex
      calc (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) = 0 :=
            Finset.sum_eq_zero fun l hl =>
              le_antisymm (not_lt.1 fun h =>
                absurd (Finset.mem_filter.1 hl).2 (not_le.2 (hex l h))) (G.hπ0 i l)
        _ ≤ D * ε ^ (deff - 1) := mul_nonneg (by linarith [H.hD]) (pow_nonneg hε0 _)

/-- `Λ(ε)` for the density prior: `log(1/(k·D·ε^{d−1})) = (d−1)·log(1/ε) − log(k·D)`. -/
lemma Lambda_density {k D ε : ℝ} (hk : 0 < k) (hD : 0 < D) (hε : 0 < ε) (d : ℕ) :
    Real.log (1 / (k * (D * ε ^ d))) = d * Real.log (1 / ε) - Real.log (k * D) := by
  rw [one_div, Real.log_inv, one_div, Real.log_inv, ← mul_assoc,
    Real.log_mul (by positivity) (by positivity), Real.log_pow]
  ring

variable [Nonempty ι] [Nonempty Fine] (probe : List Bool → Sph E) {Q : ℕ} {kout : ℕ}
  (out : (Fin Q → Bool) → Fin kout → Sph E)

open Classical in
/-- **P1 Cor P.1 (blind attacker: recovery counts).** With `μ̂₁ = D·r_thr^{d−1}` and
`p(ε) ≤ D·ε^{d−1}`: `E[N_ε] ≤ n(Q(μ̂₁+2ζ) + k·D·ε^{d−1})`, and if `k·D·ε^{d−1} < 1`,
`x·((d−1)log(1/ε) − log(kD)) ≤ B_best(Q) + n·h(min{x/n, ½})`. -/
theorem blind_counts (K : ι → Submodule ℝ E) [∀ i, (K i).HasOrthogonalProjection]
    (deff : ℕ) (D rmin : ℝ) (H : G.DensityHyp K deff D rmin) (hthr : 0 < G.thr)
    (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ) (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar)
    (hrthr : rmin ≤ Face.chordRad G.thr) (hk : 1 ≤ kout) (ε : ℝ) (hε : 0 < ε) (hrε : rmin ≤ ε) :
    G.EN probe out ε ≤ Fintype.card ι *
        (Q * (D * Face.chordRad G.thr ^ (deff - 1) + 2 * G.ζ) + kout * (D * ε ^ (deff - 1))) ∧
    ((kout : ℝ) * (D * ε ^ (deff - 1)) < 1 →
      G.EN probe out ε * (((deff - 1 : ℕ) : ℝ) * Real.log (1 / ε) - Real.log (kout * D)) ≤
        Bbest (Fintype.card ι) (D * Face.chordRad G.thr ^ (deff - 1)) G.ζ G.ν₀ βstar Q +
          (Fintype.card ι : ℝ) *
            Real.binEntropy (min (G.EN probe out ε / Fintype.card ι) (1 / 2))) := by
  obtain ⟨hcov, -, hball⟩ := G.density_params K deff D rmin H hthr
  have hμ : 0 ≤ D * Face.chordRad G.thr ^ (deff - 1) :=
    mul_nonneg (by linarith [H.hD]) (pow_nonneg (Real.sqrt_nonneg _) _)
  have hp : 0 ≤ D * ε ^ (deff - 1) := mul_nonneg (by linarith [H.hD]) (by positivity)
  refine ⟨G.thm61_3 probe out _ ε _ hμ hp (hcov hrthr) (hball ε hε.le hrε), fun hkp => ?_⟩
  have h4 := G.thm61_4 probe out hν βstar hβ _ hμ (hcov hrthr) ε _ hp hkp (hball ε hε.le hrε)
  rwa [Lambda_density (by exact_mod_cast hk) (by linarith [H.hD]) hε] at h4

open Classical in
/-- **P1 Cor P.2(i) (blind attacker, staircase).** If `P[N_ε ≥ m] ≥ ½` and
`n·k·D·ε^{d−1} ≤ m/8`, then `nQ(D·r_thr^{d−1} + 2ζ) ≥ 3m/8`. -/
theorem blind_staircase (K : ι → Submodule ℝ E) [∀ i, (K i).HasOrthogonalProjection]
    (deff : ℕ) (D rmin : ℝ) (H : G.DensityHyp K deff D rmin) (hthr : 0 < G.thr)
    (hrthr : rmin ≤ Face.chordRad G.thr) (ε : ℝ) (hε : 0 < ε) (hrε : rmin ≤ ε)
    (m : ℝ) (hm : 1 ≤ m) (hPN : 1 / 2 ≤ G.PN probe out ε m)
    (htail : Fintype.card ι * kout * (D * ε ^ (deff - 1)) ≤ m / 8) :
    3 * m / 8 ≤ Fintype.card ι * Q * (D * Face.chordRad G.thr ^ (deff - 1) + 2 * G.ζ) := by
  obtain ⟨hcov, -, hball⟩ := G.density_params K deff D rmin H hthr
  have hμ : 0 ≤ D * Face.chordRad G.thr ^ (deff - 1) :=
    mul_nonneg (by linarith [H.hD]) (pow_nonneg (Real.sqrt_nonneg _) _)
  have hp : 0 ≤ D * ε ^ (deff - 1) := mul_nonneg (by linarith [H.hD]) (by positivity)
  exact (G.cor62_i probe out _ ε _ hμ hp (hcov hrthr) (hball ε hε.le hrε) m hm hPN).2.1 htail

open Classical in
/-- **P1 Cor P.2(ii) + Cor 6.3 Q₁ (blind attacker: the dimension law).** If `P[N_ε ≥ m] ≥ ½`,
`1 ≤ m ≤ n`, `k·D·ε^{d−1} < 1` and `(d−1)log(1/ε) − log(kD) ≥ L := log(2en/m)`:

  `B_best(Q) ≥ (m/2)·((d−1)·log(1/ε) − log(kD) − L)`,
  `Q ≥ m/(2β*)·((d−1)·log(1/ε) − log(kD) − L)`.

(v2/P1 have `log(1/(2ε))`; the projection lemma removes the `2`.) -/
theorem blind_m_of_n (K : ι → Submodule ℝ E) [∀ i, (K i).HasOrthogonalProjection]
    (deff : ℕ) (D rmin : ℝ) (H : G.DensityHyp K deff D rmin) (hthr : 0 < G.thr)
    (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ) (hβpos : 0 < βstar)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar)
    (hrthr : rmin ≤ Face.chordRad G.thr) (hk : 1 ≤ kout) (ε : ℝ) (hε : 0 < ε) (hrε : rmin ≤ ε)
    (hkp : (kout : ℝ) * (D * ε ^ (deff - 1)) < 1)
    (m : ℝ) (hm : 1 ≤ m) (hmn : m ≤ Fintype.card ι) (hPN : 1 / 2 ≤ G.PN probe out ε m)
    (hL : Real.log (2 * Real.exp 1 * Fintype.card ι / m) ≤
      ((deff - 1 : ℕ) : ℝ) * Real.log (1 / ε) - Real.log (kout * D)) :
    m / 2 * (((deff - 1 : ℕ) : ℝ) * Real.log (1 / ε) - Real.log (kout * D) -
        Real.log (2 * Real.exp 1 * Fintype.card ι / m)) ≤
      Bbest (Fintype.card ι) (D * Face.chordRad G.thr ^ (deff - 1)) G.ζ G.ν₀ βstar Q ∧
    m / (2 * βstar) * (((deff - 1 : ℕ) : ℝ) * Real.log (1 / ε) - Real.log (kout * D) -
        Real.log (2 * Real.exp 1 * Fintype.card ι / m)) ≤ Q := by
  obtain ⟨hcov, -, hball⟩ := G.density_params K deff D rmin H hthr
  have hμ : 0 ≤ D * Face.chordRad G.thr ^ (deff - 1) :=
    mul_nonneg (by linarith [H.hD]) (pow_nonneg (Real.sqrt_nonneg _) _)
  have hp : 0 ≤ D * ε ^ (deff - 1) := mul_nonneg (by linarith [H.hD]) (by positivity)
  have hΛ := Lambda_density (k := (kout : ℝ)) (D := D) (by exact_mod_cast hk) (by linarith [H.hD]) hε
    (deff - 1)
  have hB := (G.cor62_ii probe out hν βstar hβ _ hμ (hcov hrthr) ε _ hp hkp
    (hball ε hε.le hrε) m hm hmn hPN).2 (by rw [hΛ]; exact hL)
  rw [hΛ] at hB
  refine ⟨by linarith, ?_⟩
  have hB1 : Bbest (Fintype.card ι) (D * Face.chordRad G.thr ^ (deff - 1)) G.ζ G.ν₀ βstar Q ≤
      Q * βstar := min_le_left _ _
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

variable [NeZero kout]

open Classical in
/-- **v2 Cor 13.2 (exponential risk floor), sharpened.** With
`ε* := exp(−(3B_best(Q)/n + 2 + log(kD))/(d−1))` and `r_min < ε*`:

  `E[R] ≥ ε*/2 = ½·exp(−(3B_best/n + 2 + log(kD))/(d−1))`

(v2: `¼·exp(…)`, from the `2ε` radius). -/
theorem blind_risk_floor (K : ι → Submodule ℝ E) [∀ i, (K i).HasOrthogonalProjection]
    (deff : ℕ) (D rmin : ℝ) (H : G.DensityHyp K deff D rmin) (hthr : 0 < G.thr)
    (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ) (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar)
    (hrthr : rmin ≤ Face.chordRad G.thr)
    (hrmin : rmin < Real.exp (-((3 * Bbest (Fintype.card ι) (D * Face.chordRad G.thr ^ (deff - 1))
      G.ζ G.ν₀ βstar Q / Fintype.card ι + 2 + Real.log (kout * D)) / ((deff - 1 : ℕ) : ℝ)))) :
    Real.exp (-((3 * Bbest (Fintype.card ι) (D * Face.chordRad G.thr ^ (deff - 1))
      G.ζ G.ν₀ βstar Q / Fintype.card ι + 2 + Real.log (kout * D)) / ((deff - 1 : ℕ) : ℝ))) / 2
      ≤ G.ER probe out := by
  set B := Bbest (Fintype.card ι) (D * Face.chordRad G.thr ^ (deff - 1)) G.ζ G.ν₀ βstar Q
  set d1 : ℝ := ((deff - 1 : ℕ) : ℝ) with hd1
  set A := 3 * B / Fintype.card ι + 2 with hA
  set es := Real.exp (-((A + Real.log (kout * D)) / d1)) with hes
  obtain ⟨hcov, -, hball⟩ := G.density_params K deff D rmin H hthr
  have hμ : 0 ≤ D * Face.chordRad G.thr ^ (deff - 1) :=
    mul_nonneg (by linarith [H.hD]) (pow_nonneg (Real.sqrt_nonneg _) _)
  have hd1pos : 1 ≤ d1 := by
    rw [hd1]; have := H.hdeff; exact_mod_cast (by omega : 1 ≤ deff - 1)
  have hk : (1 : ℝ) ≤ kout := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne kout)
  have hes0 : 0 < es := Real.exp_pos _
  -- every `ε ∈ (max(r_min, 0), ε*)` has `E[R] > ε/2`
  have key : ∀ ε, 0 < ε → rmin ≤ ε → ε < es → ε / 2 < G.ER probe out := by
    intro ε hε hrε hεs
    have hp : 0 ≤ D * ε ^ (deff - 1) := mul_nonneg (by linarith [H.hD]) (by positivity)
    have hΛ := Lambda_density (k := (kout : ℝ)) (D := D) (by linarith) (by linarith [H.hD]) hε (deff - 1)
    have hlog : Real.log ε < Real.log es := Real.log_lt_log hε hεs
    rw [hes, Real.log_exp] at hlog
    have hlog1 : Real.log (1 / ε) = -Real.log ε := by rw [one_div, Real.log_inv]
    have hmul : d1 * Real.log ε < -(A + Real.log (kout * D)) := by
      have := mul_lt_mul_of_pos_left hlog (by linarith : (0 : ℝ) < d1)
      rwa [show d1 * (-((A + Real.log (kout * D)) / d1)) = -(A + Real.log (kout * D)) by
        field_simp] at this
    have hbig : A < d1 * Real.log (1 / ε) - Real.log (kout * D) := by
      rw [hlog1]; linarith
    have hB0 : 0 ≤ B := (G.jointInfo_nonneg probe).trans
      (G.info_le_Bbest hν βstar hβ _ hμ (hcov hrthr) probe Q)
    have hA0 : 0 < A := by rw [hA]; positivity
    have hkp : (kout : ℝ) * (D * ε ^ (deff - 1)) < 1 := by
      have hpos : 0 < (kout : ℝ) * (D * ε ^ (deff - 1)) := by
        have := H.hD; positivity
      have h0 : 0 < Real.log (1 / ((kout : ℝ) * (D * ε ^ (deff - 1)))) := by
        rw [hΛ]; linarith
      by_contra hc
      push Not at hc
      have : Real.log (1 / ((kout : ℝ) * (D * ε ^ (deff - 1)))) ≤ 0 :=
        Real.log_nonpos (by positivity) (by rw [div_le_one hpos]; exact hc)
      linarith
    exact (G.cor81_decay probe out hν βstar hβ _ hμ (hcov hrthr) ε _ hε hp hkp
      (hball ε hε.le hrε) (by rw [hΛ]; linarith)).2
  by_contra hcon
  push Not at hcon
  have hER := G.ER_nonneg probe out
  set ε := (max rmin (2 * G.ER probe out) + es) / 2 with hεdef
  have hm1 : max rmin (2 * G.ER probe out) < es := max_lt hrmin (by linarith)
  have h1 := key ε (by
      have := le_max_right rmin (2 * G.ER probe out); rw [hεdef]; linarith)
    (by have := le_max_left rmin (2 * G.ER probe out); rw [hεdef]; linarith)
    (by rw [hεdef]; linarith)
  have := le_max_right rmin (2 * G.ER probe out)
  rw [hεdef] at h1
  linarith

end Gallery

end OracleBounds.GeneralPrior
