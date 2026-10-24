import Mathlib
import OracleBounds.GeneralPrior.DensityGlue

/-!
# Sharp spherical cap measure and the reach rate of a density-bounded prior

Statements signed off by the administrator, 22 Sep 2026 (proof by subagent). Faithful to the
annex's reach convention (strict `>`), normalised `σ_K`, and `SurfaceDensity.hdens`.

Replaces the chordal-ball route (`cap_measure_le`, v11 change request E) for the reach rate:
the annex's `μ₁ ≤ D·(2(1−thr))^{(d_eff−1)/2}` exceeds `1` for every `thr ≤ 1/2`.

* `cap_measure_sharp` — on the unit sphere of a `k`-dimensional real inner product space
  (`k ≥ 2`), with Mathlib's `volume.toSphere` (the same measure as `cap_measure_le`), for a unit
  `u` and `t ∈ [0,1]`:
  `σ({g : ⟪u,g⟫ ≥ t}) ≤ ½ (1 − t²)^{(k−1)/2} · σ(S^{k−1})`.
  (`cap_measure_sharp_sqrt`: the same with `√(1−t²)^{k−1}`; `cap_measure_sharp_lt`: open cap.)
* `sigmaK_reach_le`, `reach_rate_sharp`, `SurfaceDensity.reach_rate_sharp` — for `ν ≤ D·σ_K`
  (`σ_K` = `sigmaK`, normalised surface measure on `S(K)`, `dim K = k ≥ 2`), any `‖x‖ ≤ 1`,
  `thr ∈ [0,1]`: `ν({g : ⟪x,g⟫ > thr}) ≤ (D/2)(1 − thr²)^{(k−1)/2}`.

Proof (paper: `briefs/attacks/cap-measure-sharp.md`). `σ(cap)/σ(S) = vol(C)/vol(B)`, `C` the cone
over the cap truncated to the unit ball. In coordinates `(h, y) = (⟪u,x⟫, x_⊥)`, the slice of `C`
at `y` lies in `[t|y|/s, √(1−|y|²)]`, `s = √(1−t²)`. Substituting `y = s z` (Jacobian `s^{k−1}`),
the slice length at `sz` is `≤ √(1−s²|z|²) − t|z| ≤ √(1−|z|²)`, half the ball's slice at `z`.
Fubini gives `vol(C) ≤ s^{k−1}·vol(B)/2`. `t = 1` by squeezing.
-/

namespace OracleBounds.GeneralPrior

open MeasureTheory Metric
open scoped Pointwise RealInnerProductSpace

namespace CapSharp

/-- Sum of squares on `Fin n → ℝ`. -/
noncomputable def sqSum {n : ℕ} (y : Fin n → ℝ) : ℝ := ∑ j, y j ^ 2

lemma sqSum_nonneg {n : ℕ} (y : Fin n → ℝ) : 0 ≤ sqSum y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sqSum_smul {n : ℕ} (s : ℝ) (y : Fin n → ℝ) : sqSum (s • y) = s ^ 2 * sqSum y := by
  simp [sqSum, Finset.mul_sum, mul_pow]

lemma continuous_sqSum {n : ℕ} : Continuous (sqSum (n := n)) := by
  unfold sqSum; fun_prop

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- Coordinates adapted to an orthonormal basis: `x ↦ (⟪b 0, x⟫, (⟪b (j+1), x⟫)_j)`. -/
lemma coord_measurePreserving {n : ℕ} (b : OrthonormalBasis (Fin (n + 1)) ℝ F) :
    MeasurePreserving (fun x : F => (⟪b 0, x⟫, fun j : Fin n => ⟪b j.succ, x⟫))
      volume ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
  have h1 := b.measurePreserving_repr
  have h2 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n + 1))
  have h3 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) 0
  have := (h3.comp h2).comp h1
  convert this using 1
  · funext x
    simp [MeasurableEquiv.piFinSuccAbove_apply, b.repr_apply_apply]
    funext j; simp [Fin.tail, b.repr_apply_apply]
  · rfl

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
lemma coord_norm_sq {n : ℕ} (b : OrthonormalBasis (Fin (n + 1)) ℝ F) (x : F) :
    ‖x‖ ^ 2 = ⟪b 0, x⟫ ^ 2 + sqSum (fun j : Fin n => ⟪b j.succ, x⟫) := by
  rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp [sqSum, b.repr_apply_apply]

/-- Linear change of variables `y = s • z` on `Fin n → ℝ` for a lower integral. -/
lemma lintegral_eq_smul {n : ℕ} (f : (Fin n → ℝ) → ENNReal) (hf : Measurable f) {s : ℝ}
    (hs : 0 < s) :
    ∫⁻ y, f y = ENNReal.ofReal (s ^ n) * ∫⁻ z, f (s • z) := by
  have hmap := Measure.map_addHaar_smul (volume : Measure (Fin n → ℝ)) hs.ne'
  rw [Module.finrank_fin_fun] at hmap
  have : ∫⁻ z, f (s • z) = ENNReal.ofReal (|(s ^ n)⁻¹|) * ∫⁻ y, f y := by
    rw [← lintegral_map hf (measurable_const_smul s), hmap, lintegral_smul_measure]
    rfl
  rw [this, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

/-- Scalar core of the shear: `√(1 − s²v²) − t v ≤ √(1 − v²)` when `s² = 1 − t²`. -/
lemma shear_core {s t v : ℝ} (ht : 0 ≤ t) (hs : s ^ 2 = 1 - t ^ 2) (hv : 0 ≤ v) :
    Real.sqrt (1 - s ^ 2 * v ^ 2) - t * v ≤ Real.sqrt (1 - v ^ 2) := by
  have hw := Real.sqrt_nonneg (1 - v ^ 2)
  rw [sub_le_iff_le_add, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rcases le_or_gt (v ^ 2) 1 with h | h
  · have hw2 := Real.sq_sqrt (show 0 ≤ 1 - v ^ 2 by linarith)
    nlinarith [mul_nonneg (mul_nonneg hw ht) hv]
  · rw [Real.sqrt_eq_zero'.2 (by linarith)]
    nlinarith

/-- The slab/cone region in coordinates. -/
def coneSet (n : ℕ) (t : ℝ) : Set (ℝ × (Fin n → ℝ)) :=
  {p | p.1 ^ 2 + sqSum p.2 < 1 ∧ t * Real.sqrt (p.1 ^ 2 + sqSum p.2) ≤ p.1}

/-- The unit ball in coordinates. -/
def ballSet (n : ℕ) : Set (ℝ × (Fin n → ℝ)) := {p | p.1 ^ 2 + sqSum p.2 < 1}

lemma coneSet_slice {n : ℕ} {t s : ℝ} (ht : 0 ≤ t) (hs0 : 0 < s) (hs : s ^ 2 = 1 - t ^ 2)
    (y : Fin n → ℝ) :
    (fun h => (h, y)) ⁻¹' coneSet n t ⊆
      Set.Icc (t * Real.sqrt (sqSum y) / s) (Real.sqrt (1 - sqSum y)) := by
  rintro h ⟨h1, h2⟩
  simp only at h1 h2
  have hq := sqSum_nonneg y
  have hh0 : 0 ≤ h := le_trans (by positivity) h2
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hs0]
    have hsq : (t * Real.sqrt (h ^ 2 + sqSum y)) ^ 2 ≤ h ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
    have : (t * Real.sqrt (sqSum y)) ^ 2 ≤ (h * s) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hq, hs]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by nlinarith) two_ne_zero).1 this
  · exact Real.le_sqrt_of_sq_le (by linarith)

lemma ballSet_slice {n : ℕ} (z : Fin n → ℝ) :
    Set.Ioo (-Real.sqrt (1 - sqSum z)) (Real.sqrt (1 - sqSum z)) ⊆
      (fun h => (h, z)) ⁻¹' ballSet n := by
  rintro h ⟨h1, h2⟩
  show h ^ 2 + sqSum z < 1
  have ha : 0 < Real.sqrt (1 - sqSum z) := by linarith
  have h1' : 0 < 1 - sqSum z := Real.sqrt_pos.1 ha
  have : h ^ 2 < Real.sqrt (1 - sqSum z) ^ 2 := sq_lt_sq' h1 h2
  rw [Real.sq_sqrt h1'.le] at this
  linarith

/-- **Core volume bound** (`t < 1`): the cone region has at most `s^n/2` of the ball's volume. -/
lemma coneSet_volume_le {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) (coneSet n t) ≤
      ENNReal.ofReal (Real.sqrt (1 - t ^ 2) ^ n / 2) *
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) (ballSet n) := by
  set s := Real.sqrt (1 - t ^ 2) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 (by nlinarith)
  have hs : s ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  have hcm : MeasurableSet (coneSet n t) := by
    have hc : Continuous fun p : ℝ × (Fin n → ℝ) => p.1 ^ 2 + sqSum p.2 :=
      (continuous_fst.pow 2).add (continuous_sqSum.comp continuous_snd)
    exact (isOpen_lt hc continuous_const).measurableSet.inter
      (isClosed_le (continuous_const.mul (Real.continuous_sqrt.comp hc))
        continuous_fst).measurableSet
  have hbm : MeasurableSet (ballSet n) := by
    have hc : Continuous fun p : ℝ × (Fin n → ℝ) => p.1 ^ 2 + sqSum p.2 :=
      (continuous_fst.pow 2).add (continuous_sqSum.comp continuous_snd)
    exact (isOpen_lt hc continuous_const).measurableSet
  set g : (Fin n → ℝ) → ENNReal :=
    fun y => ENNReal.ofReal (Real.sqrt (1 - sqSum y) - t * Real.sqrt (sqSum y) / s)
  have hg : Measurable g := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    have := continuous_sqSum (n := n)
    fun_prop
  rw [Measure.prod_apply_symm hcm, Measure.prod_apply_symm hbm]
  calc ∫⁻ y, volume ((fun h => (h, y)) ⁻¹' coneSet n t)
      ≤ ∫⁻ y, g y := by
        refine lintegral_mono fun y => ?_
        refine (measure_mono (coneSet_slice ht hs0 hs y)).trans ?_
        rw [Real.volume_Icc]
    _ = ENNReal.ofReal (s ^ n) * ∫⁻ z, g (s • z) := lintegral_eq_smul g hg hs0
    _ ≤ ENNReal.ofReal (s ^ n) * ∫⁻ z, ENNReal.ofReal (1 / 2) *
          ENNReal.ofReal (2 * Real.sqrt (1 - sqSum z)) := by
        gcongr with z
        rw [← ENNReal.ofReal_mul (by norm_num), ← mul_assoc, one_div,
          inv_mul_cancel₀ (two_ne_zero), one_mul]
        refine ENNReal.ofReal_le_ofReal ?_
        have hq := sqSum_nonneg z
        have hv := Real.sqrt_nonneg (sqSum z)
        have e1 : sqSum (s • z) = s ^ 2 * Real.sqrt (sqSum z) ^ 2 := by
          rw [sqSum_smul, Real.sq_sqrt hq]
        have e2 : Real.sqrt (sqSum (s • z)) = s * Real.sqrt (sqSum z) := by
          rw [sqSum_smul, Real.sqrt_mul (by positivity), Real.sqrt_sq hs0.le]
        rw [e2, e1, show t * (s * Real.sqrt (sqSum z)) / s = t * Real.sqrt (sqSum z) by
          field_simp]
        have := shear_core ht hs hv
        rw [Real.sq_sqrt hq] at this ⊢; exact this
    _ = ENNReal.ofReal (s ^ n) * (ENNReal.ofReal (1 / 2) *
          ∫⁻ z, ENNReal.ofReal (2 * Real.sqrt (1 - sqSum z))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (s ^ n) * (ENNReal.ofReal (1 / 2) *
          ∫⁻ z, volume ((fun h => (h, z)) ⁻¹' ballSet n)) := by
        gcongr with z
        refine le_trans (le_of_eq ?_) (measure_mono (ballSet_slice z))
        rw [Real.volume_Ioo]; congr 1; ring
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2; ring

omit [MeasurableSpace F] [BorelSpace F] in
/-- An orthonormal basis whose `0`-th vector is the given unit vector. -/
lemma exists_basis_zero {n : ℕ} (hn : Module.finrank ℝ F = n + 1) {u : F} (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (n + 1)) ℝ F, b 0 = u := by
  have hon : Orthonormal ℝ (Set.restrict ({0} : Set (Fin (n + 1))) (fun _ => u)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have : i = j := Subtype.ext (i.2.trans j.2.symm)
    subst this
    simp [hu]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (ι := Fin (n + 1)) (by simp [hn]) hon
  exact ⟨b, hb 0 rfl⟩

/-- The sharp bound for `0 ≤ t < 1`, in `√` form. -/
lemma cap_sharp_lt_one (hm : 2 ≤ Module.finrank ℝ F) {u : F} (hu : ‖u‖ = 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (volume : Measure F).toSphere {x : sphere (0 : F) 1 | t ≤ ⟪u, (x : F)⟫} ≤
      ENNReal.ofReal (Real.sqrt (1 - t ^ 2) ^ (Module.finrank ℝ F - 1) / 2) *
        (volume : Measure F).toSphere Set.univ := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℝ F = n + 1 := ⟨Module.finrank ℝ F - 1, by omega⟩
  obtain ⟨b, hb0⟩ := exists_basis_zero hn hu
  have hΦ := coord_measurePreserving b
  set Φ := fun x : F => (⟪b 0, x⟫, fun j : Fin n => ⟪b j.succ, x⟫) with hΦdef
  have hnorm : ∀ x : F, (Φ x).1 ^ 2 + sqSum (Φ x).2 = ‖x‖ ^ 2 := fun x =>
    (coord_norm_sq b x).symm
  have hcap : MeasurableSet {x : sphere (0 : F) 1 | t ≤ ⟪u, (x : F)⟫} :=
    (isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)).measurableSet
  have hcm : MeasurableSet (coneSet n t) := by
    have hc : Continuous fun p : ℝ × (Fin n → ℝ) => p.1 ^ 2 + sqSum p.2 :=
      (continuous_fst.pow 2).add (continuous_sqSum.comp continuous_snd)
    exact (isOpen_lt hc continuous_const).measurableSet.inter
      (isClosed_le (continuous_const.mul (Real.continuous_sqrt.comp hc))
        continuous_fst).measurableSet
  have hbm : MeasurableSet (ballSet n) := by
    have hc : Continuous fun p : ℝ × (Fin n → ℝ) => p.1 ^ 2 + sqSum p.2 :=
      (continuous_fst.pow 2).add (continuous_sqSum.comp continuous_snd)
    exact (isOpen_lt hc continuous_const).measurableSet
  have hsub : Set.Ioo (0 : ℝ) 1 • ((↑) '' {x : sphere (0 : F) 1 | t ≤ ⟪u, (x : F)⟫} : Set F)
      ⊆ Φ ⁻¹' coneSet n t := by
    rintro y ⟨r, hr, _, ⟨g, hg, rfl⟩, rfl⟩
    have hg1 : ‖(g : F)‖ = 1 := norm_eq_of_mem_sphere g
    have hny : ‖r • (g : F)‖ = r := by rw [norm_smul, hg1, mul_one, Real.norm_of_nonneg hr.1.le]
    show (Φ (r • (g : F))).1 ^ 2 + sqSum (Φ (r • (g : F))).2 < 1 ∧
      t * Real.sqrt ((Φ (r • (g : F))).1 ^ 2 + sqSum (Φ (r • (g : F))).2) ≤ (Φ (r • (g : F))).1
    rw [hnorm, hny, Real.sqrt_sq hr.1.le]
    refine ⟨by nlinarith [hr.1, hr.2], ?_⟩
    show t * r ≤ ⟪b 0, r • (g : F)⟫
    rw [hb0, real_inner_smul_right]
    have : t ≤ ⟪u, (g : F)⟫ := hg
    nlinarith [hr.1]
  have hball : Φ ⁻¹' ballSet n = ball (0 : F) 1 := by
    ext x
    show (Φ x).1 ^ 2 + sqSum (Φ x).2 < 1 ↔ x ∈ ball (0 : F) 1
    rw [hnorm, mem_ball_zero_iff]
    constructor
    · intro h; nlinarith [norm_nonneg x]
    · intro h; nlinarith [norm_nonneg x]
  have hvol := coneSet_volume_le (n := n) ht0 ht1
  rw [← hΦ.measure_preimage hcm.nullMeasurableSet,
    ← hΦ.measure_preimage hbm.nullMeasurableSet, hball] at hvol
  rw [Measure.toSphere_apply' _ hcap, Measure.toSphere_apply_univ, hn, Nat.add_sub_cancel]
  calc ((n + 1 : ℕ) : ENNReal) * volume (Set.Ioo (0 : ℝ) 1 •
        ((↑) '' {x : sphere (0 : F) 1 | t ≤ ⟪u, (x : F)⟫} : Set F))
      ≤ ((n + 1 : ℕ) : ENNReal) * (ENNReal.ofReal (Real.sqrt (1 - t ^ 2) ^ n / 2) *
          volume (ball (0 : F) 1)) := by
        gcongr
        exact (measure_mono hsub).trans hvol
    _ = _ := by ring

/-- `√x ^ n = x ^ (n/2)` for `x ≥ 0`. -/
lemma sqrt_pow_eq_rpow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt x ^ n = x ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1; ring

end CapSharp

open CapSharp

/-- **Sharp cap lemma, `√` form.** For `2 ≤ m = dim F`, `‖u‖ = 1`, `t ∈ [0,1]`:
`σ({g ∈ S^{m−1} : ⟪u,g⟫ ≥ t}) ≤ ½·√(1−t²)^{m−1}·σ(S^{m−1})`. -/
theorem cap_measure_sharp_sqrt {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (hm : 2 ≤ Module.finrank ℝ F) (u : F) (hu : ‖u‖ = 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume : Measure F).toSphere {x : sphere (0 : F) 1 | t ≤ ⟪u, (x : F)⟫} ≤
      ENNReal.ofReal (Real.sqrt (1 - t ^ 2) ^ (Module.finrank ℝ F - 1) / 2) *
        (volume : Measure F).toSphere Set.univ := by
  rcases ht1.lt_or_eq with ht1 | rfl
  · exact cap_sharp_lt_one hm hu ht0 ht1
  · -- `t = 1`: squeeze with caps at levels `√(1 − δ²)`, `δ ↓ 0`.
    set T := (volume : Measure F).toSphere Set.univ
    set a := (volume : Measure F).toSphere {x : sphere (0 : F) 1 | 1 ≤ ⟪u, (x : F)⟫}
    have hTtop : T ≠ ⊤ := by
      simp only [T]
      rw [Measure.toSphere_apply_univ]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
    have hbound : ∀ δ ∈ Set.Ioo (0 : ℝ) 1, a ≤ ENNReal.ofReal δ * T := by
      intro δ hδ
      set t' := Real.sqrt (1 - δ ^ 2)
      have hδ2 : 0 ≤ 1 - δ ^ 2 := by nlinarith [hδ.1, hδ.2]
      have ht'2 : t' ^ 2 = 1 - δ ^ 2 := Real.sq_sqrt hδ2
      have ht'0 : 0 ≤ t' := Real.sqrt_nonneg _
      have ht'1 : t' < 1 := by
        rw [Real.sqrt_lt' one_pos]; nlinarith [hδ.1]
      have hmono : a ≤ (volume : Measure F).toSphere
          {x : sphere (0 : F) 1 | t' ≤ ⟪u, (x : F)⟫} :=
        measure_mono fun x hx => by
          simp only [Set.mem_setOf_eq] at hx ⊢; linarith
      refine hmono.trans ((cap_sharp_lt_one hm hu ht'0 ht'1).trans ?_)
      gcongr
      rw [ht'2, show 1 - (1 - δ ^ 2) = δ ^ 2 by ring, Real.sqrt_sq hδ.1.le]
      calc δ ^ (Module.finrank ℝ F - 1) / 2 ≤ δ ^ (Module.finrank ℝ F - 1) := by
            linarith [pow_nonneg hδ.1.le (Module.finrank ℝ F - 1)]
        _ ≤ δ := pow_le_of_le_one hδ.1.le hδ.2.le (by omega)
    have hlim : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal δ * T) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (ENNReal.ofReal 0 * T)) :=
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal
        (tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id)) (Or.inr hTtop)
    have ha : a ≤ ENNReal.ofReal 0 * T :=
      ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) hbound)
    refine ha.trans (le_of_eq ?_)
    congr 1
    rw [show (1 : ℝ) - 1 ^ 2 = 0 by norm_num, Real.sqrt_zero,
      zero_pow (by omega), zero_div]

/-- **Sharp cap lemma** (the requested form). For `k = dim F ≥ 2`, `‖u‖ = 1`, `t ∈ [0,1]`,
with `σ = volume.toSphere` and `σ(S)` the total mass,
`σ({g : ⟪u,g⟫ ≥ t}) ≤ ½ (1 − t²)^{(k−1)/2} · σ(S)`. -/
theorem cap_measure_sharp {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (hm : 2 ≤ Module.finrank ℝ F) (u : F) (hu : ‖u‖ = 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume : Measure F).toSphere {x : sphere (0 : F) 1 | t ≤ ⟪u, (x : F)⟫} ≤
      ENNReal.ofReal ((1 - t ^ 2) ^ (((Module.finrank ℝ F - 1 : ℕ) : ℝ) / 2) / 2) *
        (volume : Measure F).toSphere Set.univ := by
  rw [← sqrt_pow_eq_rpow (by nlinarith)]
  exact cap_measure_sharp_sqrt hm u hu t ht0 ht1

/-- The open cap `⟪u,g⟫ > t` (as in the statement of the Lemma). -/
theorem cap_measure_sharp_lt {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (hm : 2 ≤ Module.finrank ℝ F) (u : F) (hu : ‖u‖ = 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume : Measure F).toSphere {x : sphere (0 : F) 1 | t < ⟪u, (x : F)⟫} ≤
      ENNReal.ofReal ((1 - t ^ 2) ^ (((Module.finrank ℝ F - 1 : ℕ) : ℝ) / 2) / 2) *
        (volume : Measure F).toSphere Set.univ :=
  (measure_mono fun _ hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢; exact hx.le).trans (cap_measure_sharp hm u hu t ht0 ht1)

/-! ### Corollary: the reach rate of a density-bounded prior -/

section Reach

open OracleBounds.V6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The normalised surface measure `σ_K` of the reach set `{g : ⟪x,g⟫ > thr}`, for any `x` with
`‖x‖ ≤ 1` (in particular any probe `x ∈ S^{d−1}`), is at most `½ (1 − thr²)^{(k−1)/2}`,
`k = dim K`. -/
theorem sigmaK_reach_le (K : Submodule ℝ E) (hK : 2 ≤ Module.finrank ℝ K) (x : E)
    (hx : ‖x‖ ≤ 1) (thr : ℝ) (h0 : 0 ≤ thr) (h1 : thr ≤ 1) :
    sigmaK K {g : Sph E | thr < ⟪x, g.1⟫} ≤
      ENNReal.ofReal ((1 - thr ^ 2) ^ (((Module.finrank ℝ K - 1 : ℕ) : ℝ) / 2) / 2) := by
  set A : Set (Sph E) := {g | thr < ⟪x, g.1⟫}
  have hA : MeasurableSet A :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)).measurableSet
  obtain ⟨hT0, hTtop⟩ := toSphere_univ_pos_ne_top K hK
  unfold sigmaK
  rw [Measure.smul_apply, Measure.map_apply (sphIncl_measurable _) hA, smul_eq_mul]
  set P : E := K.starProjection x
  have hPK : P ∈ K := K.starProjection_apply_mem x
  have hinner : ∀ z : E, z ∈ K → ⟪x, z⟫ = ⟪P, z⟫ := fun z hz => by
    rw [K.inner_starProjection_left_eq_right, K.starProjection_eq_self_iff.2 hz]
  have hP1 : ‖P‖ ≤ 1 := (K.norm_starProjection_apply_le x).trans hx
  by_cases hP : P = 0
  · have : sphIncl K ⁻¹' A = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_setOf_eq, A, sphIncl, Set.mem_empty_iff_false,
        iff_false, not_lt]
      rw [hinner _ (z : K).2, hP, inner_zero_left]; exact h0
    rw [this, measure_empty, mul_zero]; exact zero_le
  · have hPn : 0 < ‖P‖ := norm_pos_iff.2 hP
    set u : K := ⟨‖P‖⁻¹ • P, K.smul_mem _ hPK⟩
    have hu : ‖u‖ = 1 := by
      show ‖‖P‖⁻¹ • P‖ = 1
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hPn.ne']
    have hsub : sphIncl K ⁻¹' A ⊆ {z : sphere (0 : K) 1 | thr ≤ ⟪u, (z : K)⟫} := by
      intro z hz
      have hz' : thr < ⟪x, ((z : K) : E)⟫ := hz
      rw [hinner _ (z : K).2] at hz'
      show thr ≤ ⟪(u : E), ((z : K) : E)⟫
      show thr ≤ ⟪‖P‖⁻¹ • P, ((z : K) : E)⟫
      rw [real_inner_smul_left]
      rw [le_inv_mul_iff₀ hPn]
      nlinarith
    have hcap := cap_measure_sharp (F := K) hK u hu thr h0 h1
    calc ((volume : Measure K).toSphere Set.univ)⁻¹ *
          (volume : Measure K).toSphere (sphIncl K ⁻¹' A)
        ≤ ((volume : Measure K).toSphere Set.univ)⁻¹ *
          (ENNReal.ofReal ((1 - thr ^ 2) ^ (((Module.finrank ℝ K - 1 : ℕ) : ℝ) / 2) / 2) *
            (volume : Measure K).toSphere Set.univ) :=
          by gcongr; exact (measure_mono hsub).trans hcap
      _ = _ := by rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel hT0 hTtop, mul_one]

/-- **Corollary (reach rate).** If `ν ≤ D·σ_K` on measurable sets (`K` a subspace of
dimension `k ≥ 2`), then for every `x` with `‖x‖ ≤ 1` and `thr ∈ [0,1]`,
`ν({g : ⟪x,g⟫ > thr}) ≤ (D/2)(1 − thr²)^{(k−1)/2}`. -/
theorem reach_rate_sharp (K : Submodule ℝ E) (hK : 2 ≤ Module.finrank ℝ K)
    (ν : Measure (Sph E)) (D : ℝ) (hD : 0 ≤ D)
    (hdens : ∀ A : Set (Sph E), MeasurableSet A → ν A ≤ ENNReal.ofReal D * sigmaK K A)
    (x : E) (hx : ‖x‖ ≤ 1) (thr : ℝ) (h0 : 0 ≤ thr) (h1 : thr ≤ 1) :
    ν {g : Sph E | thr < ⟪x, g.1⟫} ≤
      ENNReal.ofReal (D / 2 * (1 - thr ^ 2) ^ (((Module.finrank ℝ K - 1 : ℕ) : ℝ) / 2)) := by
  have hA : MeasurableSet {g : Sph E | thr < ⟪x, g.1⟫} :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)).measurableSet
  have hσ := sigmaK_reach_le K hK x hx thr h0 h1
  calc ν {g : Sph E | thr < ⟪x, g.1⟫} ≤ ENNReal.ofReal D * sigmaK K {g : Sph E | thr < ⟪x, g.1⟫} :=
        hdens _ hA
    _ ≤ ENNReal.ofReal D *
          ENNReal.ofReal ((1 - thr ^ 2) ^ (((Module.finrank ℝ K - 1 : ℕ) : ℝ) / 2) / 2) := by
        gcongr
    _ = _ := by rw [← ENNReal.ofReal_mul hD]; congr 1; ring

/-- The same, in the `SurfaceDensity` packaging (`μ₁ ≤ (D/2)(1 − thr²)^{(d_eff−1)/2}`). -/
theorem SurfaceDensity.reach_rate_sharp {ι : Type*} [Fintype ι] {Ks : ι → Submodule ℝ E}
    {deff : ℕ} {D : ℝ} {ν : ι → Measure (Sph E)} [∀ i, IsProbabilityMeasure (ν i)]
    (H : SurfaceDensity Ks deff D ν) (i : ι) (x : E) (hx : ‖x‖ ≤ 1) (thr : ℝ) (h0 : 0 ≤ thr)
    (h1 : thr ≤ 1) :
    (ν i {g : Sph E | thr < ⟪x, g.1⟫}).toReal ≤
      D / 2 * (1 - thr ^ 2) ^ (((deff - 1 : ℕ) : ℝ) / 2) := by
  have h := OracleBounds.GeneralPrior.reach_rate_sharp (Ks i) (by rw [H.hdim i]; exact H.hdeff)
    (ν i) D (by linarith [H.hD]) (H.hdens i) x hx thr h0 h1
  rw [H.hdim i] at h
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans (le_of_eq ?_)
  exact ENNReal.toReal_ofReal (mul_nonneg (by linarith [H.hD]) (Real.rpow_nonneg (by nlinarith) _))

end Reach

end OracleBounds.GeneralPrior
