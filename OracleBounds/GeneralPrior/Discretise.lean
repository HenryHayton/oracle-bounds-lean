import Mathlib

/-!
# Representative discretisation of product priors

The bridge from finite-support priors (everything in `OracleBounds.GeneralPrior`) to arbitrary
Borel priors on a compact metric space (e.g. the unit sphere with a density prior).

Given Borel probability measures `ν i` on a compact metric space `S` and a bounded measurable
`F : (ι → S) → ℝ`, for every `η > 0` there are finite priors (weights `w i`, atoms `r i`) such
that

* every atom-set mass is bounded by the `η`-thickened `ν`-mass: moving each face's mass to
  representatives at distance `≤ η` can only enlarge ball/cap masses by an `η`-margin;
* the expectation of `F` under the discrete product prior is at least its expectation under
  `⊗ ν i`.

Construction: partition `S` into finitely many measurable cells of diameter `≤ η` (compactness),
put weight `ν i (cell)` on one point of each cell, and choose the points one coordinate at a time
(Fubini) so that the partial average of `F` does not decrease (`exists_le_setAverage`).

Applying it to `F` and to `-F` transfers every finite-prior bound of the form `E[F] ≤ c` or
`E[F] ≥ c` to Borel priors, with the prior parameters evaluated at `η`-enlarged radii.

**Statement locked by the administrator. Do not edit the statement.**
-/

namespace OracleBounds.GeneralPrior

open MeasureTheory

section Helpers

variable {S : Type*} [MeasurableSpace S]

/-- Integral over a finite measurable partition given by the fibres of `q`. -/
lemma integral_eq_sum_fiber {K : ℕ} (μ : Measure S) [IsFiniteMeasure μ] (q : S → Fin K)
    (hq : Measurable q) (h : S → ℝ) (hh : Integrable h μ) :
    ∫ x, h x ∂μ = ∑ c, ∫ x in q ⁻¹' {c}, h x ∂μ := by
  have hU : (⋃ c, q ⁻¹' {c}) = Set.univ := by
    ext x; simp
  rw [← integral_iUnion_fintype (fun c => hq (measurableSet_singleton c))
    (fun a b hab => (Set.disjoint_singleton.2 hab).preimage q) (fun c => hh.integrableOn), hU,
    Measure.restrict_univ]

/-- One-measure step: representatives not decreasing the integral. -/
lemma exists_reps_one {K : ℕ} [Nonempty S] (μ : Measure S) [IsProbabilityMeasure μ]
    (q : S → Fin K) (hq : Measurable q) (f : S → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) :
    ∃ r : Fin K → S, (∀ c, μ (q ⁻¹' {c}) ≠ 0 → q (r c) = c) ∧
      ∫ x, f x ∂μ ≤ ∫ x, f (r (q x)) ∂μ := by
  have hfi : Integrable f μ :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hC x)
  have key : ∀ c, ∃ y : S, (μ (q ⁻¹' {c}) ≠ 0 → q y = c) ∧
      ∫ x in q ⁻¹' {c}, f x ∂μ ≤ ∫ x in q ⁻¹' {c}, f y ∂μ := by
    intro c
    by_cases h0 : μ (q ⁻¹' {c}) = 0
    · refine ⟨Classical.arbitrary S, fun h => absurd h0 h, ?_⟩
      rw [Measure.restrict_eq_zero.2 h0]
      simp
    · obtain ⟨y, hy, hle⟩ := exists_setAverage_le h0 (measure_ne_top _ _) hfi.integrableOn
      refine ⟨y, fun _ => hy, ?_⟩
      rw [setIntegral_const, setAverage_eq, smul_eq_mul] at *
      have hpos : 0 < μ.real (q ⁻¹' {c}) := by
        rw [measureReal_def]
        exact ENNReal.toReal_pos h0 (measure_ne_top _ _)
      have := mul_le_mul_of_nonneg_left hle hpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
  choose r hr1 hr2 using key
  refine ⟨r, hr1, ?_⟩
  have hgi : Integrable (fun x => f (r (q x))) μ :=
    Integrable.of_bound (hf.comp ((measurable_of_countable r).comp hq)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC _)
  rw [integral_eq_sum_fiber μ q hq f hfi, integral_eq_sum_fiber μ q hq _ hgi]
  refine Finset.sum_le_sum fun c _ => ?_
  refine (hr2 c).trans (le_of_eq ?_)
  refine setIntegral_congr_fun (hq (measurableSet_singleton c)) fun x hx => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  simp [hx]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma measurable_update_pair (i : ι) :
    Measurable (fun p : S × (ι → S) => Function.update p.2 i p.1) :=
  measurable_update'.comp measurable_swap

/-- Resampling one coordinate is measure preserving. -/
lemma measurePreserving_update_pair (ν : ι → Measure S) [∀ i, IsProbabilityMeasure (ν i)]
    (i : ι) :
    MeasurePreserving (fun p : S × (ι → S) => Function.update p.2 i p.1)
      ((ν i).prod (Measure.pi ν)) (Measure.pi ν) := by
  refine ⟨measurable_update_pair i, (Measure.pi_eq fun s hs => ?_).symm⟩
  have hpre : (fun p : S × (ι → S) => Function.update p.2 i p.1) ⁻¹' Set.pi Set.univ s =
      s i ×ˢ Set.pi Set.univ (Function.update s i Set.univ) := by
    ext ⟨x, v⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h i, fun j => ?_⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨hx, h⟩ j
      by_cases hj : j = i
      · subst hj; simpa using hx
      · simpa [Function.update_of_ne hj] using h j
  rw [Measure.map_apply (measurable_update_pair i) (MeasurableSet.univ_pi hs), hpre,
    Measure.prod_prod, Measure.pi_pi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => ν j (s j)) (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma integral_update_fubini (ν : ι → Measure S) [∀ i, IsProbabilityMeasure (ν i)] (i : ι)
    (H : (ι → S) → ℝ) (hH : Measurable H) (C : ℝ) (hC : ∀ v, |H v| ≤ C) :
    ∫ v, H v ∂(Measure.pi ν) = ∫ x, ∫ v, H (Function.update v i x) ∂(Measure.pi ν) ∂(ν i) := by
  have hmp := measurePreserving_update_pair ν i
  have hint : Integrable (fun p : S × (ι → S) => H (Function.update p.2 i p.1))
      ((ν i).prod (Measure.pi ν)) :=
    Integrable.of_bound (hH.comp hmp.measurable).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC _)
  calc ∫ v, H v ∂(Measure.pi ν)
      = ∫ v, H v ∂(Measure.map (fun p : S × (ι → S) => Function.update p.2 i p.1)
          ((ν i).prod (Measure.pi ν))) := by rw [hmp.map_eq]
    _ = ∫ p, H (Function.update p.2 i p.1) ∂((ν i).prod (Measure.pi ν)) :=
        integral_map hmp.measurable.aemeasurable hH.aestronglyMeasurable
    _ = _ := integral_prod _ hint

/-- One-coordinate step. -/
lemma exists_reps_coord {K : ℕ} [Nonempty S] (ν : ι → Measure S) [∀ i, IsProbabilityMeasure (ν i)]
    (q : S → Fin K) (hq : Measurable q) (G : (ι → S) → ℝ) (hG : Measurable G) (C : ℝ)
    (hC : ∀ v, |G v| ≤ C) (i : ι) :
    ∃ r' : Fin K → S, (∀ c, ν i (q ⁻¹' {c}) ≠ 0 → q (r' c) = c) ∧
      ∫ v, G v ∂(Measure.pi ν) ≤
        ∫ v, G (Function.update v i (r' (q (v i)))) ∂(Measure.pi ν) := by
  set g : S → ℝ := fun x => ∫ v, G (Function.update v i x) ∂(Measure.pi ν) with hg_def
  have hgm : Measurable g :=
    ((hG.comp (measurable_update_pair i)).stronglyMeasurable.integral_prod_right'
      (ν := Measure.pi ν)).measurable
  have hgC : ∀ x, |g x| ≤ C := by
    intro x
    have := norm_integral_le_of_norm_le_const (μ := Measure.pi ν)
      (f := fun v => G (Function.update v i x)) (C := C)
      (Filter.Eventually.of_forall fun v => by simpa [Real.norm_eq_abs] using hC _)
    simpa [Real.norm_eq_abs] using this
  obtain ⟨r', hr'1, hr'2⟩ := exists_reps_one (ν i) q hq g hgm C hgC
  refine ⟨r', hr'1, ?_⟩
  have hm2 : Measurable (fun v : ι → S => G (Function.update v i (r' (q (v i))))) := by
    refine hG.comp ?_
    exact measurable_update'.comp (Measurable.prodMk measurable_id
      ((measurable_of_countable r').comp (hq.comp (measurable_pi_apply i))))
  rw [integral_update_fubini ν i G hG C hC,
    integral_update_fubini ν i _ hm2 C (fun v => hC _)]
  convert hr'2 using 3 with x
  simp [g]

/-- Discretise the coordinates in `s`, one at a time. -/
lemma exists_reps_finset {K : ℕ} [Nonempty S] (ν : ι → Measure S)
    [∀ i, IsProbabilityMeasure (ν i)] (q : S → Fin K) (hq : Measurable q)
    (F : (ι → S) → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ v, |F v| ≤ C) (s : Finset ι) :
    ∃ r : ι → Fin K → S, (∀ i ∈ s, ∀ c, ν i (q ⁻¹' {c}) ≠ 0 → q (r i c) = c) ∧
      ∫ v, F v ∂(Measure.pi ν) ≤
        ∫ v, F (fun j => if j ∈ s then r j (q (v j)) else v j) ∂(Measure.pi ν) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ _ => Classical.arbitrary S, by simp, by simp⟩
  | insert i s hi ih =>
    obtain ⟨r, hr1, hr2⟩ := ih
    have hmeas : Measurable (fun v : ι → S => fun j => if j ∈ s then r j (q (v j)) else v j) := by
      refine measurable_pi_lambda _ fun j => ?_
      by_cases hj : j ∈ s
      · simp only [hj, if_true]
        exact (measurable_of_countable _).comp (hq.comp (measurable_pi_apply j))
      · simp only [hj, if_false]
        exact measurable_pi_apply j
    obtain ⟨r', hr'1, hr'2⟩ := exists_reps_coord ν q hq
      (fun v => F (fun j => if j ∈ s then r j (q (v j)) else v j)) (hF.comp hmeas) C
      (fun v => hC _) i
    refine ⟨Function.update r i r', ?_, hr2.trans (hr'2.trans (le_of_eq ?_))⟩
    · intro j hj c hc
      rcases Finset.mem_insert.1 hj with rfl | hj
      · simpa using hr'1 c hc
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        rw [Function.update_of_ne hji]
        exact hr1 j hj c hc
    · congr 1
      funext v
      congr 1
      funext j
      by_cases hji : j = i
      · subst hji
        simp [hi]
      · simp [Finset.mem_insert, hji]

end Helpers

open Classical in
/-- **Representative discretisation.** -/
theorem discretise_pi {ι S : Type*} [Fintype ι] [DecidableEq ι]
    [MetricSpace S] [CompactSpace S] [Nonempty S] [MeasurableSpace S] [BorelSpace S]
    (ν : ι → Measure S) [∀ i, IsProbabilityMeasure (ν i)]
    (F : (ι → S) → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ v, |F v| ≤ C)
    (η : ℝ) (hη : 0 < η) :
    ∃ (K : ℕ) (w : ι → Fin K → ℝ) (r : ι → Fin K → S),
      (∀ i c, 0 ≤ w i c) ∧ (∀ i, ∑ c, w i c = 1) ∧
      (∀ i (A : Set S), ∑ c ∈ Finset.univ.filter (fun c => r i c ∈ A), w i c ≤
          (ν i (Metric.cthickening η A)).toReal) ∧
      ∫ v, F v ∂(Measure.pi ν) ≤
        ∑ c : ι → Fin K, (∏ i, w i (c i)) * F (fun i => r i (c i)) := by
  classical
  -- a finite cover by balls of radius `η/2`
  obtain ⟨t, -, htf, hcov⟩ :=
    finite_cover_balls_of_compact (isCompact_univ (X := S)) (half_pos hη)
  obtain ⟨K, e, he⟩ := htf.fin_embedding
  have hcov' : ∀ x : S, ∃ n, ∃ h : n < K, dist x (e ⟨n, h⟩) < η / 2 := by
    intro x
    have := hcov (Set.mem_univ x)
    simp only [Set.mem_iUnion, Metric.mem_ball] at this
    obtain ⟨y, hy, hxy⟩ := this
    rw [← he] at hy
    obtain ⟨k, rfl⟩ := hy
    exact ⟨k.1, k.2, hxy⟩
  let q : S → Fin K := fun x => ⟨Nat.find (hcov' x), (Nat.find_spec (hcov' x)).1⟩
  have hqball : ∀ x, dist x (e (q x)) < η / 2 := fun x => (Nat.find_spec (hcov' x)).2
  have hq : Measurable q := by
    have hN : Measurable fun x => Nat.find (hcov' x) := by
      refine measurable_find hcov' fun k => ?_
      by_cases hk : k < K
      · have : {x : S | ∃ h : k < K, dist x (e ⟨k, h⟩) < η / 2} =
            Metric.ball (e ⟨k, hk⟩) (η / 2) := by
          ext x
          simp [hk, Metric.mem_ball]
        rw [this]
        exact Metric.isOpen_ball.measurableSet
      · simp [hk]
    refine measurable_to_countable' fun c => ?_
    have : q ⁻¹' {c} = (fun x => Nat.find (hcov' x)) ⁻¹' {c.1} := by
      ext y
      simp [q, Fin.ext_iff]
    rw [this]
    exact hN (measurableSet_singleton _)
  have hclose : ∀ x y, q x = q y → dist x y ≤ η := by
    intro x y hxy
    have h1 := hqball x
    have h2 := hqball y
    rw [← hxy] at h2
    linarith [dist_triangle_right x y (e (q x))]
  obtain ⟨r, hr1, hr2⟩ := exists_reps_finset ν q hq F hF C hC Finset.univ
  refine ⟨K, fun i c => (ν i (q ⁻¹' {c})).toReal, r, fun i c => ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · intro i
    rw [← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _),
      sum_measure_preimage_singleton _ (fun y _ => hq (measurableSet_singleton y))]
    simp
  · intro i A
    have h1 : ∑ c ∈ Finset.univ.filter (fun c => r i c ∈ A), (ν i (q ⁻¹' {c})).toReal =
        ∑ c ∈ (Finset.univ.filter (fun c => r i c ∈ A)).filter (fun c => ν i (q ⁻¹' {c}) ≠ 0),
          (ν i (q ⁻¹' {c})).toReal := by
      refine (Finset.sum_filter_of_ne fun c _ h => ?_).symm
      intro h0
      exact h (by simp [h0])
    rw [h1, ← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _),
      sum_measure_preimage_singleton _ (fun y _ => hq (measurableSet_singleton y))]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
    intro x hx
    simp at hx
    obtain ⟨hA, hne⟩ := hx
    have hqr : q (r i (q x)) = q x := hr1 i (Finset.mem_univ i) (q x) hne
    exact Metric.mem_cthickening_of_dist_le x _ η A hA (hclose _ _ hqr.symm)
  · refine hr2.trans (le_of_eq ?_)
    simp only [Finset.mem_univ, if_true]
    let φ : (ι → S) → (ι → Fin K) := fun v j => q (v j)
    have hφ : Measurable φ := measurable_pi_lambda _ fun j => hq.comp (measurable_pi_apply j)
    have hmap : ∫ v, F (fun j => r j (q (v j))) ∂(Measure.pi ν) =
        ∫ c, F (fun i => r i (c i)) ∂(Measure.map φ (Measure.pi ν)) := by
      rw [integral_map (f := fun c : ι → Fin K => F (fun i => r i (c i))) hφ.aemeasurable
        (measurable_of_countable _).aestronglyMeasurable]
    rw [hmap, integral_fintype Integrable.of_finite]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_eq_mul, measureReal_def, Measure.map_apply hφ (measurableSet_singleton c)]
    have hpre : φ ⁻¹' {c} = Set.pi Set.univ (fun j => q ⁻¹' {c j}) := by
      ext v
      simp [φ, funext_iff]
    rw [hpre, Measure.pi_pi, ENNReal.toReal_prod]

end OracleBounds.GeneralPrior
