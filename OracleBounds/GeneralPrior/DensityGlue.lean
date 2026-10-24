import OracleBounds.GeneralPrior.Continuous
import OracleBounds.GeneralPrior.CapMeasure

/-!
# From a surface density to the cap hypothesis (closing v2 §13)

v2 §13's standing assumption: face `i`'s prior `νᵢ` is supported on `S(Kᵢ)` for a
`d_eff`-dimensional subspace `Kᵢ`, with `νᵢ ≤ D·σᵢ`, `σᵢ` the normalised surface measure on
`S(Kᵢ)`. Here `σᵢ` is Mathlib's `volume.toSphere` on the unit sphere of `Kᵢ` (as an inner product
space in its own right), normalised and pushed into the ambient sphere.

`SurfaceDensity.toContDensityHyp` derives `ContDensityHyp` — the cap-mass hypothesis used by
`cont_blind_m_of_n` / `cont_blind_nominated` — from this, using v2 Lemma 13.0
(`cap_measure_le`). With it, the continuous dimension laws rest on no labelled geometric
hypothesis.

No `sorry`s (given `cap_measure_le`).
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open MeasureTheory Metric OracleBounds.V6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The unit sphere of a subspace `K`, included in the ambient unit sphere. -/
def sphIncl (K : Submodule ℝ E) (x : sphere (0 : K) 1) : Sph E :=
  ⟨((x : K) : E), mem_sphere_zero_iff_norm.1 x.2⟩

lemma sphIncl_measurable (K : Submodule ℝ E) : Measurable (sphIncl K) :=
  (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _).measurable

/-- Normalised surface measure on `S(K)`, as a measure on the ambient sphere. -/
noncomputable def sigmaK (K : Submodule ℝ E) : Measure (Sph E) :=
  ((volume : Measure K).toSphere Set.univ)⁻¹ • (volume : Measure K).toSphere.map (sphIncl K)

variable {ι : Type*} [Fintype ι]

/-- **v2 §13 standing assumptions, measure form.** -/
structure SurfaceDensity (Ks : ι → Submodule ℝ E) (deff : ℕ) (D : ℝ)
    (ν : ι → Measure (Sph E)) : Prop where
  hD : 1 ≤ D
  hdeff : 2 ≤ deff
  hdim : ∀ i, Module.finrank ℝ (Ks i) = deff
  hsupp : ∀ i, ν i {g : Sph E | g.1 ∉ Ks i} = 0
  hdens : ∀ i (A : Set (Sph E)), MeasurableSet A → ν i A ≤ ENNReal.ofReal D * sigmaK (Ks i) A

lemma toSphere_univ_pos_ne_top (K : Submodule ℝ E) (hK : 2 ≤ Module.finrank ℝ K) :
    (volume : Measure K).toSphere Set.univ ≠ 0 ∧ (volume : Measure K).toSphere Set.univ ≠ ⊤ := by
  haveI : Nontrivial K := Module.nontrivial_of_finrank_pos (lt_of_lt_of_le (by norm_num) hK)
  rw [Measure.toSphere_apply_univ']
  refine ⟨?_, ?_⟩
  · refine mul_ne_zero (Nat.cast_ne_zero.2 (ne_of_gt (lt_of_lt_of_le (by norm_num) hK))) ?_
    rw [measure_sdiff_null (measure_singleton _)]
    exact (measure_ball_pos _ _ one_pos).ne'
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.sdiff_subset))

/-- **`hcapD` from the surface density and v2 Lemma 13.0.** -/
theorem SurfaceDensity.toContDensityHyp {Ks : ι → Submodule ℝ E}
    [∀ i, (Ks i).HasOrthogonalProjection] {deff : ℕ} {D : ℝ} {ν : ι → Measure (Sph E)}
    [∀ i, IsProbabilityMeasure (ν i)] (H : SurfaceDensity Ks deff D ν) :
    Oracle.ContDensityHyp Ks deff D ν where
  hD := H.hD
  hdeff := H.hdeff
  hsupp := H.hsupp
  hcapD := by
    intro i y hy hyn ρ hρ
    set A : Set (Sph E) := {g | ‖y - g.1‖ ≤ ρ}
    have hA : MeasurableSet A :=
      (isClosed_le (continuous_const.sub continuous_subtype_val).norm continuous_const).measurableSet
    have hdim := H.hdim i
    have hd2 := H.hdeff
    obtain ⟨h0, htop⟩ := toSphere_univ_pos_ne_top (Ks i) (by omega)
    -- the preimage in `S(Kᵢ)` is the closed chordal ball about `y`
    have hpre : sphIncl (Ks i) ⁻¹' A =
        {x : sphere (0 : Ks i) 1 | ‖((x : Ks i)) - ⟨y, hy⟩‖ ≤ ρ} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, A, sphIncl]
      rw [norm_sub_rev]
      exact Iff.rfl
    have hcap := cap_measure_le (F := Ks i) (by omega) ⟨y, hy⟩ (by simpa using hyn) ρ hρ
    rw [← hpre, hdim] at hcap
    have hσ : sigmaK (Ks i) A ≤ ENNReal.ofReal (ρ ^ (deff - 1)) := by
      unfold sigmaK
      rw [Measure.smul_apply, Measure.map_apply (sphIncl_measurable _) hA, smul_eq_mul]
      calc ((volume : Measure (Ks i)).toSphere Set.univ)⁻¹ *
            (volume : Measure (Ks i)).toSphere (sphIncl (Ks i) ⁻¹' A)
          ≤ ((volume : Measure (Ks i)).toSphere Set.univ)⁻¹ *
            (ENNReal.ofReal (ρ ^ (deff - 1)) * (volume : Measure (Ks i)).toSphere Set.univ) :=
            mul_le_mul_left' hcap _
        _ = ENNReal.ofReal (ρ ^ (deff - 1)) := by
            rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel h0 htop, mul_one]
    have hν := (H.hdens i A hA).trans (mul_le_mul_left' hσ _)
    rw [← ENNReal.ofReal_mul (by linarith [H.hD])] at hν
    calc (ν i A).toReal ≤ (ENNReal.ofReal (D * ρ ^ (deff - 1))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hν
      _ = D * ρ ^ (deff - 1) := ENNReal.toReal_ofReal (mul_nonneg (by linarith [H.hD]) (by positivity))

end OracleBounds.GeneralPrior
