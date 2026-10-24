import Mathlib

/-!
# Spherical cap measure (`n-face-general-prior-v2` Lemma 13.0)

On the unit sphere of an `m`-dimensional real inner product space (`m ≥ 2`), with the surface
measure `volume.toSphere` (Mathlib's cone construction), the closed chordal ball of radius `r`
about a unit vector `a` has at most an `r^{m−1}` fraction of the total surface measure:

  `σ(B̄(a, r) ∩ S^{m−1}) ≤ r^{m−1} · σ(S^{m−1})`.

This is the geometric input behind v2 Prop 13.1 / P1 P.1–P.2 (the dimension law). Downstream it
enters `Continuous.ContDensityHyp.hcapD` as "density `≤ D` × this lemma".

**Statement locked by the administrator. Do not edit the statement.**
-/

namespace OracleBounds.GeneralPrior

open MeasureTheory Metric
open scoped Pointwise RealInnerProductSpace

section CapHelpers
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The stretch map `x ↦ r x + (α − r)⟪a,x⟫ a` (eigenvalue `α` along `a`, `r` across). -/
noncomputable def capStretch (a : F) (α r : ℝ) : F →ₗ[ℝ] F :=
  r • LinearMap.id + (α - r) • (innerₗ F a).smulRight a

lemma capStretch_apply (a : F) (α r : ℝ) (x : F) :
    capStretch a α r x = r • x + ((α - r) * ⟪a, x⟫) • a := by
  simp [capStretch, mul_smul, innerₗ_apply_apply]

/-- Scalar core: `Q(p) ≤ 0` on `[1 − r²/2, 1]`. -/
lemma cap_quad_le {r p : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hpc : 1 - r ^ 2 / 2 ≤ p)
    (hp1 : p ≤ 1) :
    (r ^ 2 * (1 + r / 2) ^ 2 - 1) * p ^ 2 - 2 * (r ^ 2 * (1 + r / 2)) * p + 1 ≤ 0 := by
  set A := r ^ 2 * (1 + r / 2) ^ 2 - 1
  set B := r ^ 2 * (1 + r / 2)
  set c := 1 - r ^ 2 / 2
  have hQ1 : A * 1 ^ 2 - 2 * B * 1 + 1 = r ^ 2 * (1 + r / 2) * (r / 2 - 1) := by
    simp only [A, B]; ring
  have hQc : A * c ^ 2 - 2 * B * c + 1 = -(r ^ 5 / 4) * (2 + r) * (1 - r / 2 - r ^ 2 / 4) := by
    simp only [A, B, c]; ring
  have hQ1n : A * 1 ^ 2 - 2 * B * 1 + 1 ≤ 0 := by
    rw [hQ1]
    have h : 0 ≤ r ^ 2 * (1 + r / 2) := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos h (by linarith)
  have hQcn : A * c ^ 2 - 2 * B * c + 1 ≤ 0 := by
    rw [hQc]
    have : 0 ≤ 1 - r / 2 - r ^ 2 / 4 := by nlinarith
    have : 0 ≤ r ^ 5 / 4 * (2 + r) * (1 - r / 2 - r ^ 2 / 4) := by positivity
    linarith
  have hc0 : 0 < c := by simp only [c]; nlinarith
  rcases le_or_gt 0 A with hA | hA
  · have h1 : 0 ≤ (1 - p) * -(A * c ^ 2 - 2 * B * c + 1) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ (p - c) * -(A * 1 ^ 2 - 2 * B * 1 + 1) := mul_nonneg (by linarith) (by linarith)
    have h3 : 0 ≤ A * (p - c) * (1 - p) := mul_nonneg (mul_nonneg hA (by linarith)) (by linarith)
    have hid : (1 - c) * (A * p ^ 2 - 2 * B * p + 1) =
        (1 - p) * (A * c ^ 2 - 2 * B * c + 1) + (p - c) * (A * 1 ^ 2 - 2 * B * 1 + 1)
          - (1 - c) * (A * (p - c) * (1 - p)) := by ring
    have h1c : 0 < 1 - c := by have := pow_pos hr0 2; simp only [c]; linarith
    have : (1 - c) * (A * p ^ 2 - 2 * B * p + 1) ≤ 0 := by
      rw [hid]; nlinarith
    exact nonpos_of_mul_nonpos_right (by linarith) h1c
  · have hB : 0 < B := by simp only [B]; positivity
    have h4 : A * (p + c) - 2 * B ≤ 0 := by
      have : A * (p + c) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hA.le (by linarith)
      linarith
    have h5 : (p - c) * (A * (p + c) - 2 * B) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) h4
    have hid : A * p ^ 2 - 2 * B * p + 1 =
        (A * c ^ 2 - 2 * B * c + 1) + (p - c) * (A * (p + c) - 2 * B) := by ring
    rw [hid]; linarith

/-- Every point of the cap `‖u − a‖ ≤ r` lies in the ellipsoid `L(B̄(a,1))`. -/
lemma mem_capStretch_image {a u : F} (ha : ‖a‖ = 1) (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r < 1) (hua : ‖u - a‖ ≤ r) :
    u ∈ capStretch a (2 / (2 + r)) r '' closedBall a 1 := by
  have haa : ⟪a, a⟫ = 1 := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
  rcases hr.eq_or_lt with rfl | hr0
  · have : u = a := by
      have := norm_nonneg (u - a)
      exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm hua this))
    subst this
    refine ⟨u, mem_closedBall_self zero_le_one, ?_⟩
    rw [capStretch_apply, haa]; norm_num
  · set p := ⟪a, u⟫ with hp
    have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
    have hua' : ⟪u, a⟫ = p := real_inner_comm _ _
    have hp1 : p ≤ 1 := by
      have := real_inner_le_norm a u
      rw [ha, hu] at this; linarith
    have hpc : 1 - r ^ 2 / 2 ≤ p := by
      have h := norm_sub_sq_real u a
      have : ‖u - a‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hua 2
      rw [hu, ha] at h
      linarith
    set k := 1 + r / 2 - r⁻¹ with hk
    refine ⟨r⁻¹ • u + (k * p) • a, ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm]
      have hsq : ‖r⁻¹ • u + (k * p) • a - a‖ ^ 2
          = r⁻¹ ^ 2 + 2 * r⁻¹ * (k * p - 1) * p + (k * p - 1) ^ 2 := by
        rw [← real_inner_self_eq_norm_sq]
        have : r⁻¹ • u + (k * p) • a - a = r⁻¹ • u + (k * p - 1) • a := by
          rw [sub_smul, one_smul]; abel
        rw [this]
        simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
          haa, huu, hua', ← hp]
        ring
      have hQ := cap_quad_le hr0 hr1 hpc hp1
      have e : r⁻¹ ^ 2 + 2 * r⁻¹ * (k * p - 1) * p + (k * p - 1) ^ 2 - 1 =
          r⁻¹ ^ 2 * ((r ^ 2 * (1 + r / 2) ^ 2 - 1) * p ^ 2 - 2 * (r ^ 2 * (1 + r / 2)) * p + 1) := by
        simp only [hk]; field_simp; ring
      have hle : ‖r⁻¹ • u + (k * p) • a - a‖ ^ 2 ≤ 1 := by
        rw [hsq]
        have : r⁻¹ ^ 2 * ((r ^ 2 * (1 + r / 2) ^ 2 - 1) * p ^ 2
            - 2 * (r ^ 2 * (1 + r / 2)) * p + 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hQ
        linarith
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hle
    · rw [capStretch_apply]
      simp only [inner_add_right, real_inner_smul_right, haa, ← hp]
      rw [smul_add, smul_smul, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, add_assoc,
        ← add_smul]
      have : r * (k * p) + (2 / (2 + r) - r) * (r⁻¹ * p + k * p * 1) = 0 := by
        simp only [hk]; field_simp; ring
      rw [this, zero_smul, add_zero]

lemma det_capStretch [FiniteDimensional ℝ F] {a : F} (ha : ‖a‖ = 1) (α r : ℝ) :
    LinearMap.det (capStretch a α r) = α * r ^ (Module.finrank ℝ F - 1) := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  haveI : Nontrivial F := nontrivial_of_ne a 0 ha0
  obtain ⟨k, hk⟩ : ∃ k, Module.finrank ℝ F = k + 1 :=
    ⟨Module.finrank ℝ F - 1, (Nat.sub_add_cancel Module.finrank_pos).symm⟩
  have hon : Orthonormal ℝ (Set.restrict ({0} : Set (Fin (k + 1))) (fun _ => a)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have : i = j := Subtype.ext (i.2.trans j.2.symm)
    subst this
    simp [ha]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (ι := Fin (k + 1)) (by simp [hk]) hon
  have hb0 : b 0 = a := hb 0 rfl
  rw [← LinearMap.det_toMatrix b.toBasis]
  have hM : LinearMap.toMatrix b.toBasis b.toBasis (capStretch a α r) =
      Matrix.diagonal (fun i => if i = 0 then α else r) := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, capStretch_apply, ← hb0]
    simp only [inner_add_right, real_inner_smul_right, b.inner_eq_ite, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [hM, Matrix.det_diagonal, Fin.prod_univ_succ]
  simp [Fin.succ_ne_zero, hk]

end CapHelpers

/-- **v2 Lemma 13.0.** `σ(B̄(a,r) ∩ S^{m−1}) ≤ r^{m−1}·σ(S^{m−1})`. -/
theorem cap_measure_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (hm : 2 ≤ Module.finrank ℝ F) (a : F) (ha : ‖a‖ = 1) (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure F).toSphere {x : sphere (0 : F) 1 | ‖(x : F) - a‖ ≤ r} ≤
      ENNReal.ofReal (r ^ (Module.finrank ℝ F - 1)) * (volume : Measure F).toSphere Set.univ := by
  set s : Set (sphere (0 : F) 1) := {x | ‖(x : F) - a‖ ≤ r} with hsdef
  have hs : MeasurableSet s :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  rcases le_or_gt 1 r with h1 | h1
  · calc (volume : Measure F).toSphere s ≤ (volume : Measure F).toSphere Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 * (volume : Measure F).toSphere Set.univ := (one_mul _).symm
      _ ≤ _ := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (one_le_pow₀ h1)
  · set α : ℝ := 2 / (2 + r) with hα
    set L := capStretch a α r
    have hsub : Set.Ioo (0 : ℝ) 1 • ((↑) '' s : Set F) ⊆ L '' closedBall a 1 := by
      rintro y ⟨t, ht, _, ⟨u, hu, rfl⟩, rfl⟩
      have hconv : Convex ℝ (L '' closedBall a 1) := (convex_closedBall a 1).linear_image L
      have h0 : (0 : F) ∈ L '' closedBall a 1 :=
        ⟨0, by simp [mem_closedBall, dist_eq_norm, ha], map_zero L⟩
      exact hconv.smul_mem_of_zero_mem h0
        (mem_capStretch_image ha (norm_eq_of_mem_sphere u) hr h1 hu) ⟨ht.1.le, ht.2.le⟩
    have hαle : α ≤ 1 := by
      rw [hα, div_le_one (by linarith)]; linarith
    have hvol : volume (L '' closedBall a 1) =
        ENNReal.ofReal (α * r ^ (Module.finrank ℝ F - 1)) * volume (ball (0 : F) 1) := by
      rw [Measure.addHaar_image_linearMap, Measure.addHaar_closedBall _ _ zero_le_one,
        det_capStretch ha, one_pow, ENNReal.ofReal_one, one_mul,
        abs_of_nonneg (by positivity)]
    rw [Measure.toSphere_apply' _ hs, Measure.toSphere_apply_univ]
    calc (Module.finrank ℝ F : ENNReal) * volume (Set.Ioo (0 : ℝ) 1 • ((↑) '' s : Set F))
        ≤ (Module.finrank ℝ F : ENNReal) * volume (L '' closedBall a 1) := by
          gcongr
      _ = (Module.finrank ℝ F : ENNReal) *
          (ENNReal.ofReal (α * r ^ (Module.finrank ℝ F - 1)) * volume (ball (0 : F) 1)) := by
          rw [hvol]
      _ ≤ (Module.finrank ℝ F : ENNReal) *
          (ENNReal.ofReal (r ^ (Module.finrank ℝ F - 1)) * volume (ball (0 : F) 1)) := by
          gcongr
          exact mul_le_of_le_one_left (by positivity) hαle
      _ = _ := by ring


end OracleBounds.GeneralPrior
