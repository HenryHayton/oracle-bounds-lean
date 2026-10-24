import OracleBounds.GeneralPrior.Density
import OracleBounds.GeneralPrior.Discretise

/-!
# Continuous (Borel) priors

Every result in `OracleBounds.GeneralPrior` is proved for finite-support priors. This file
transfers the Q2 headline results to arbitrary Borel product priors `⊗ νᵢ` on the unit sphere,
via `discretise_pi`: for each `η > 0`, a finite product prior whose ball/cap masses are bounded by
the `η`-enlarged masses of `ν` and under which the attacker does at least as well. The finite
theorem then applies to the discretised prior.

* `cont_m_of_n` — Cor 6.2(ii) + Cor 6.3 Q₁ (any `m` of `n` faces, information branch) for Borel
  priors, with the ball mass taken at radius `ε + η`;
* `cont_nominated` — Prop 7.3 (a nominated face) for Borel priors, reach at `thr − η`, balls at
  `ε + η`;
* `cont_blind_m_of_n`, `cont_blind_nominated` — the density-prior dimension laws (v2 §13 /
  P1 P.1–P.2) for genuinely continuous priors, `η → 0` taken: `Q ≥ m/(2β*)·((d−1)log(1/ε) −
  log(kD) − L)` and `P[face i recovered at ε] ≤ Q(D·r_thr^{d−1} + 2ζ) + k·D·ε^{d−1}`.

Attackers are deterministic (Remark 1.4). The oracle kernel must be Borel measurable.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6 MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Thickenings on the sphere -/

lemma cthickening_halfspace (x : E) (hx : ‖x‖ = 1) (t η : ℝ) (hη : 0 ≤ η) :
    Metric.cthickening η {g : Sph E | t < inner ℝ x g.1} ⊆
      {g : Sph E | t - η ≤ inner ℝ x g.1} := by
  intro g hg
  rw [Metric.cthickening_eq_iInter_thickening hη] at hg
  simp only [Set.mem_iInter] at hg
  simp only [Set.mem_setOf_eq]
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  obtain ⟨a, ha, hga⟩ := Metric.mem_thickening_iff.1 (hg (η + δ) (by linarith))
  simp only [Set.mem_setOf_eq] at ha
  have h1 : |inner ℝ x g.1 - inner ℝ x a.1| ≤ dist g a := by
    rw [← inner_sub_right, Subtype.dist_eq, dist_eq_norm]
    calc |inner ℝ x (g.1 - a.1)| ≤ ‖x‖ * ‖g.1 - a.1‖ := abs_real_inner_le_norm _ _
      _ = ‖g.1 - a.1‖ := by rw [hx, one_mul]
  linarith [(abs_le.1 h1).1]

lemma cthickening_ball (y : Sph E) (ε η : ℝ) (hη : 0 ≤ η) :
    Metric.cthickening η (Metric.closedBall y ε) ⊆ Metric.closedBall y (ε + η) := by
  intro g hg
  rw [Metric.cthickening_eq_iInter_thickening hη] at hg
  simp only [Set.mem_iInter] at hg
  rw [Metric.mem_closedBall]
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  obtain ⟨a, ha, hga⟩ := Metric.mem_thickening_iff.1 (hg (η + δ) (by linarith))
  rw [Metric.mem_closedBall] at ha
  linarith [dist_triangle g a y]

/-! ### Oracle without a prior, and its discretised galleries -/

/-- The oracle's parameters (v2 Def 1.2), with a measurable kernel. -/
structure Oracle (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  thr : ℝ
  τacc : ℝ
  hτ : thr < τacc
  hthr : -1 < thr
  κ : ℝ → ℝ
  ν₀ : ℝ
  ζ : ℝ
  hκ : ∀ s, 0 ≤ κ s ∧ κ s ≤ 1
  hband : ∀ s ≤ thr, |κ s - ν₀| ≤ ζ
  hκm : Measurable κ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Oracle

variable (O : Oracle E)

/-- Response against a gallery of templates `v`. -/
noncomputable def respC [Nonempty ι] (v : ι → Sph E) (x : Sph E) : ℝ :=
  O.κ (Finset.univ.sup' Finset.univ_nonempty (fun j => inner ℝ x.1 (v j).1))

/-- The finite gallery with face `i` distributed as `Σ_c w i c · δ_{r i c}`. -/
noncomputable def disc {K : ℕ} (w : ι → Fin K → ℝ) (r : ι → Fin K → Sph E)
    (hw0 : ∀ i c, 0 ≤ w i c) (hw1 : ∀ i, ∑ c, w i c = 1) : Gallery E ι (ι × Fin K) where
  thr := O.thr
  τacc := O.τacc
  hτ := O.hτ
  hthr := O.hthr
  κ := O.κ
  ν₀ := O.ν₀
  ζ := O.ζ
  hκ := O.hκ
  hband := O.hband
  g := fun jc => (r jc.1 jc.2).1
  hg := fun jc => (r jc.1 jc.2).2
  π := fun i jc => if jc.1 = i then w i jc.2 else 0
  hπ0 := fun i jc => by by_cases h : jc.1 = i <;> simp [h, hw0]
  hπ1 := fun i => by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simpa using hw1 i
    · intro j _ hj; simp [hj]
    · simp

section Disc

variable {K : ℕ} (w : ι → Fin K → ℝ) (r : ι → Fin K → Sph E)
  (hw0 : ∀ i c, 0 ≤ w i c) (hw1 : ∀ i, ∑ c, w i c = 1)

open Classical in
lemma disc_mass (i : ι) (A : Set (Sph E)) :
    (∑ l ∈ Finset.univ.filter (fun l : ι × Fin K => r l.1 l.2 ∈ A), (O.disc w r hw0 hw1).π i l) =
      ∑ c ∈ Finset.univ.filter (fun c => r i c ∈ A), w i c := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single i]
  · rw [Finset.sum_filter]; simp [disc]
  · intro j _ hj
    refine Finset.sum_eq_zero fun c _ => ?_
    simp [disc, hj]
  · simp

omit [DecidableEq ι] in
lemma disc_nonempty [Nonempty ι] (w : ι → Fin K → ℝ) (hw1 : ∀ i, ∑ c, w i c = 1) :
    Nonempty (ι × Fin K) := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; have := hw1 i; simp at this
  · exact ⟨(i, ⟨0, hK⟩)⟩

/-- The discretised prior's expectation is the finite sum of `discretise_pi`. -/
lemma disc_sum (F : (ι → Sph E) → ℝ) :
    ∑ v : ι → ι × Fin K, (O.disc w r hw0 hw1).prior v * F (fun j => r (v j).1 (v j).2) =
      ∑ c : ι → Fin K, (∏ i, w i (c i)) * F (fun i => r i (c i)) := by
  set φ : (ι → Fin K) → (ι → ι × Fin K) := fun c j => (j, c j) with hφ
  have hinj : Function.Injective φ := fun c c' h => funext fun j => by
    have := congrFun h j; simp [φ] at this; exact this
  have hprior : ∀ c, (O.disc w r hw0 hw1).prior (φ c) = ∏ i, w i (c i) := fun c => by
    simp [Gallery.prior, disc, φ]
  calc ∑ v : ι → ι × Fin K, (O.disc w r hw0 hw1).prior v * F (fun j => r (v j).1 (v j).2)
      = ∑ v ∈ Finset.univ.image φ,
          (O.disc w r hw0 hw1).prior v * F (fun j => r (v j).1 (v j).2) := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun v _ hv => ?_).symm
        have : ∃ j, (v j).1 ≠ j := by
          by_contra hcon
          push Not at hcon
          exact hv (Finset.mem_image.2 ⟨fun j => (v j).2, Finset.mem_univ _,
            funext fun j => Prod.ext (hcon j).symm rfl⟩)
        obtain ⟨j, hj⟩ := this
        rw [Gallery.prior, Finset.prod_eq_zero (Finset.mem_univ j) (by simp [disc, hj]), zero_mul]
    _ = ∑ c : ι → Fin K, (O.disc w r hw0 hw1).prior (φ c) *
          F (fun j => r (φ c j).1 (φ c j).2) := Finset.sum_image fun c _ c' _ h => hinj h
    _ = _ := Finset.sum_congr rfl fun c _ => by rw [hprior]

end Disc

/-! ### The process under a continuous prior -/

section Process

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

lemma measurable_respC [Nonempty ι] (x : Sph E) : Measurable fun v : ι → Sph E => O.respC v x := by
  refine O.hκm.comp ?_
  have : (fun v : ι → Sph E => Finset.univ.sup' Finset.univ_nonempty
      (fun j => inner ℝ x.1 (v j).1)) =
      Finset.univ.sup' Finset.univ_nonempty (fun j (v : ι → Sph E) => inner ℝ x.1 (v j).1) := by
    funext v; rw [Finset.sup'_apply]
  rw [this]
  exact Finset.measurable_sup' _ fun j _ =>
    (continuous_const.inner (continuous_subtype_val.comp (continuous_apply j))).measurable

lemma measurable_pathProb [Nonempty ι] (probe : List Bool → Sph E) :
    ∀ r h (e : Fin r → Bool), Measurable fun v : ι → Sph E => pathProb (O.respC v) probe r h e := by
  intro r
  induction r with
  | zero => intro h e; simp [pathProb]
  | succ r ih =>
    intro h e
    simp only [pathProb, bern]
    refine Measurable.mul ?_ (ih _ _)
    split_ifs
    · exact O.measurable_respC (probe h)
    · exact measurable_const.sub (O.measurable_respC (probe h))

open Classical in
/-- `N_ε` for a gallery of templates. -/
noncomputable def Nc {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E) (ε : ℝ)
    (v : ι → Sph E) (e : Fin Q → Bool) : ℝ :=
  ((Finset.univ.filter fun i => ∃ j, ‖(out e j).1 - (v i).1‖ ≤ ε).card : ℝ)

lemma measurableSet_rec {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E) (ε : ℝ)
    (e : Fin Q → Bool) (i : ι) :
    MeasurableSet {v : ι → Sph E | ∃ j, ‖(out e j).1 - (v i).1‖ ≤ ε} := by
  have : {v : ι → Sph E | ∃ j, ‖(out e j).1 - (v i).1‖ ≤ ε} =
      ⋃ j, {v : ι → Sph E | ‖(out e j).1 - (v i).1‖ ≤ ε} := by ext; simp
  rw [this]
  exact MeasurableSet.iUnion fun j => (isClosed_le (continuous_const.sub
    (continuous_subtype_val.comp (continuous_apply i))).norm continuous_const).measurableSet

open Classical in
lemma measurable_Nc {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E) (ε : ℝ)
    (e : Fin Q → Bool) : Measurable fun v : ι → Sph E => Nc out ε v e := by
  unfold Nc
  simp only [Finset.natCast_card_filter]
  exact Finset.measurable_sum _ fun i _ =>
    Measurable.ite (measurableSet_rec out ε e i) measurable_const measurable_const

open Classical in
/-- `P[N_ε ≥ m | gallery v]`. -/
noncomputable def FPN [Nonempty ι] (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε m : ℝ) (v : ι → Sph E) : ℝ :=
  ∑ e, pathProb (O.respC v) probe Q [] e * (if m ≤ Nc out ε v e then 1 else 0)

open Classical in
/-- `P[face i recovered at ε | gallery v]`. -/
noncomputable def Frec [Nonempty ι] (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε : ℝ) (i : ι) (v : ι → Sph E) : ℝ :=
  ∑ e, pathProb (O.respC v) probe Q [] e *
    (if ∃ j, ‖(out e j).1 - (v i).1‖ ≤ ε then 1 else 0)

lemma pathProb_resp_mem [Nonempty ι] (v : ι → Sph E) :
    ∀ x, 0 ≤ O.respC v x ∧ O.respC v x ≤ 1 := fun _ => O.hκ _

/-- A `[0,1]`-weighted transcript average lies in `[0,1]`. -/
lemma abs_avg_le [Nonempty ι] (probe : List Bool → Sph E) (Q : ℕ) (v : ι → Sph E)
    (a : (Fin Q → Bool) → ℝ) (ha : ∀ e, 0 ≤ a e ∧ a e ≤ 1) :
    |∑ e, pathProb (O.respC v) probe Q [] e * a e| ≤ 1 := by
  have h0 : ∀ e, 0 ≤ pathProb (O.respC v) probe Q [] e :=
    pathProb_nonneg probe (O.pathProb_resp_mem v) Q []
  have hs := pathProb_sum probe (O.pathProb_resp_mem v) Q []
  rw [abs_le]; constructor
  · linarith [Finset.sum_nonneg fun e (_ : e ∈ Finset.univ) => mul_nonneg (h0 e) (ha e).1]
  · calc ∑ e, pathProb (O.respC v) probe Q [] e * a e ≤ ∑ e, pathProb (O.respC v) probe Q [] e :=
          Finset.sum_le_sum fun e _ => mul_le_of_le_one_right (h0 e) (ha e).2
      _ = 1 := hs

open Classical in
lemma measurable_FPN [Nonempty ι] (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε m : ℝ) :
    Measurable (O.FPN probe out ε m (ι := ι)) := by
  unfold FPN
  exact Finset.measurable_sum _ fun e _ => (O.measurable_pathProb probe Q [] e).mul
    (Measurable.ite (measurableSet_le measurable_const (measurable_Nc out ε e))
      measurable_const measurable_const)

open Classical in
lemma measurable_Frec [Nonempty ι] (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε : ℝ) (i : ι) :
    Measurable (O.Frec probe out ε i) := by
  unfold Frec
  exact Finset.measurable_sum _ fun e _ => (O.measurable_pathProb probe Q [] e).mul
    (Measurable.ite (measurableSet_rec out ε e i) measurable_const measurable_const)

variable [Nontrivial E]

instance sph_compact : CompactSpace (Sph E) := by
  rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ, Subtype.range_coe_subtype]
  have : {x : E | ‖x‖ = 1} = Metric.sphere 0 1 := by ext; simp
  rw [this]; exact isCompact_sphere 0 1

instance sph_nonempty : Nonempty (Sph E) :=
  ⟨⟨_, (exists_norm_eq E (zero_le_one : (0 : ℝ) ≤ 1)).choose_spec⟩⟩

section Transfer

variable {K : ℕ} (w : ι → Fin K → ℝ) (r : ι → Fin K → Sph E)
  (hw0 : ∀ i c, 0 ≤ w i c) (hw1 : ∀ i, ∑ c, w i c = 1)

open Classical in
lemma disc_PN [Nonempty ι] (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε m : ℝ) :
    haveI := disc_nonempty w hw1
    (O.disc w r hw0 hw1).PN probe out ε m =
      ∑ v, (O.disc w r hw0 hw1).prior v * O.FPN probe out ε m (fun j => r (v j).1 (v j).2) := by
  simp only [Gallery.PN, Gallery.wt, FPN, Finset.mul_sum, mul_assoc]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun e _ => ?_
  congr 2
  · simp only [Gallery.Ncount, Nc, Gallery.recovered]
    congr

open Classical in
lemma disc_rec [Nonempty ι] (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε : ℝ) (i : ι) (v : ι → ι × Fin K) :
    O.Frec probe out ε i (fun j => r (v j).1 (v j).2) =
      val ((O.disc w r hw0 hw1).resp v) probe (fun h => if ∃ j,
        ‖(Gallery.outL out h j).1 - (O.disc w r hw0 hw1).g (v i)‖ ≤ ε then (1 : ℝ) else 0) Q [] := by
  rw [val_eq_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Gallery.outL_ofFn]
  rfl

open Classical in
/-- Ball masses of the discretised prior are bounded by `(ε+η)`-ball masses of `ν`. -/
lemma disc_ball (ν : ι → Measure (Sph E)) [∀ i, IsProbabilityMeasure (ν i)] (η : ℝ) (hη : 0 ≤ η)
    (hmass : ∀ i (A : Set (Sph E)), ∑ c ∈ Finset.univ.filter (fun c => r i c ∈ A), w i c ≤
      (ν i (Metric.cthickening η A)).toReal)
    (ε : ℝ) (i : ι) (y : Sph E) :
    (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - (O.disc w r hw0 hw1).g l‖ ≤ ε),
      (O.disc w r hw0 hw1).π i l) ≤ (ν i (Metric.closedBall y (ε + η))).toReal := by
  have hset : Finset.univ.filter (fun l => ‖y.1 - (O.disc w r hw0 hw1).g l‖ ≤ ε) =
      Finset.univ.filter (fun l : ι × Fin K => r l.1 l.2 ∈ Metric.closedBall y ε) := by
    ext l
    simp [disc, Metric.mem_closedBall, Subtype.dist_eq, dist_eq_norm, norm_sub_rev]
  rw [hset]
  calc _ = _ := O.disc_mass w r hw0 hw1 i _
    _ ≤ (ν i (Metric.cthickening η (Metric.closedBall y ε))).toReal := hmass i _
    _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (cthickening_ball y ε η hη))

open Classical in
/-- Reach masses of the discretised prior are bounded by `ν`-masses at threshold `thr − η`. -/
lemma disc_reach (ν : ι → Measure (Sph E)) [∀ i, IsProbabilityMeasure (ν i)] (η : ℝ) (hη : 0 ≤ η)
    (hmass : ∀ i (A : Set (Sph E)), ∑ c ∈ Finset.univ.filter (fun c => r i c ∈ A), w i c ≤
      (ν i (Metric.cthickening η A)).toReal)
    (i : ι) (x : Sph E) :
    (∑ l ∈ Finset.univ.filter ((O.disc w r hw0 hw1).reachG · x), (O.disc w r hw0 hw1).π i l) ≤
      (ν i {g : Sph E | O.thr - η ≤ inner ℝ x.1 g.1}).toReal := by
  have hset : Finset.univ.filter ((O.disc w r hw0 hw1).reachG · x) =
      Finset.univ.filter (fun l : ι × Fin K => r l.1 l.2 ∈ {g : Sph E | O.thr < inner ℝ x.1 g.1}) := by
    ext l
    simp [disc, Gallery.reachG]
  rw [hset]
  calc _ = _ := O.disc_mass w r hw0 hw1 i _
    _ ≤ (ν i (Metric.cthickening η {g : Sph E | O.thr < inner ℝ x.1 g.1})).toReal := hmass i _
    _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (cthickening_halfspace x.1 x.2 O.thr η hη))

end Transfer

open Classical in
/-- **Cor 6.2(ii) + Cor 6.3 Q₁ for Borel product priors.** If the attacker recovers at least
`m` of the `n` faces at `ε` with probability `≥ ½` under `⊗νᵢ`, and every `(ε+η)`-ball has
`νᵢ`-mass `≤ p` (any `η > 0`), then `Q ≥ m/(2β*)·(log(1/(k·p)) − log(2en/m))`. -/
theorem cont_m_of_n [Nonempty ι] (hν : 0 ≤ O.ν₀ ∧ O.ν₀ ≤ 1) (βstar : ℝ) (hβpos : 0 < βstar)
    (hβ : ∀ s, bkl (O.κ s) (1 / 2) ≤ βstar)
    (ν : ι → Measure (Sph E)) [∀ i, IsProbabilityMeasure (ν i)]
    (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)
    (ε η p : ℝ) (hη : 0 < η) (hp : 0 ≤ p)
    (hball : ∀ i (y : Sph E), (ν i (Metric.closedBall y (ε + η))).toReal ≤ p)
    (m : ℝ) (hm : 1 ≤ m) (hmn : m ≤ Fintype.card ι)
    (hPN : 1 / 2 ≤ ∫ v, O.FPN probe out ε m v ∂(Measure.pi ν)) :
    m / (2 * βstar) * (Real.log (1 / ((kout : ℝ) * p)) -
      Real.log (2 * Real.exp 1 * Fintype.card ι / m)) ≤ Q := by
  set L := Real.log (2 * Real.exp 1 * Fintype.card ι / m) with hL
  set Λ := Real.log (1 / ((kout : ℝ) * p)) with hΛ
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hL0 : 0 ≤ L := Real.log_nonneg (by
    rw [le_div_iff₀ (by linarith)]; nlinarith [Real.add_one_le_exp (1 : ℝ)])
  -- trivial cases: `Λ < L`, or `k·p ≥ 1` (then `Λ ≤ 0 ≤ L`)
  by_cases htriv : Λ < L
  · have : m / (2 * βstar) * (Λ - L) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  push Not at htriv
  by_cases hkp : (kout : ℝ) * p < 1
  swap
  · push Not at hkp
    have hΛ0 : Λ ≤ 0 := Real.log_nonpos (by positivity)
      (by rw [div_le_one (by linarith)]; exact hkp)
    have : m / (2 * βstar) * (Λ - L) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  -- discretise and apply the finite theorem
  obtain ⟨K, w, r, hw0, hw1, hmass, hint⟩ := discretise_pi ν (O.FPN probe out ε m)
    (O.measurable_FPN probe out ε m) 1
    (fun v => O.abs_avg_le probe Q v _ fun e => by split_ifs <;> norm_num) η hη
  haveI := disc_nonempty w hw1
  set G := O.disc w r hw0 hw1
  have hPNG : 1 / 2 ≤ G.PN probe out ε m := by
    rw [O.disc_PN w r hw0 hw1, O.disc_sum w r hw0 hw1]; linarith
  have hcovG : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ 1 := fun i x =>
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun l _ _ => G.hπ0 i l).trans (G.hπ1 i).le
  have hballG : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ p := fun i y =>
    (O.disc_ball w r hw0 hw1 ν η hη.le hmass ε i y).trans (hball i y)
  have h := (G.cor62_ii probe out hν βstar (fun v x => hβ _) 1 zero_le_one hcovG ε p hp hkp
    hballG m hm hmn hPNG).2 htriv
  have hB : Bbest (Fintype.card ι) 1 G.ζ G.ν₀ βstar Q ≤ Q * βstar := min_le_left _ _
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

open Classical in
/-- **Prop 7.3 (a nominated face) for Borel product priors.** If every probe's `(thr−η)`-cap has
`νᵢ`-mass `≤ μ₁` and every `(ε+η)`-ball `≤ p`, then
`P[face i recovered at ε] ≤ Q(μ₁ + 2ζ) + k·p`. -/
theorem cont_nominated [Nonempty ι] (ν : ι → Measure (Sph E)) [∀ i, IsProbabilityMeasure (ν i)]
    (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)
    (ε η μ₁ p : ℝ) (hη : 0 < η) (hμ : 0 ≤ μ₁) (hp : 0 ≤ p)
    (hcov : ∀ i (x : Sph E), (ν i {g : Sph E | O.thr - η ≤ inner ℝ x.1 g.1}).toReal ≤ μ₁)
    (hball : ∀ i (y : Sph E), (ν i (Metric.closedBall y (ε + η))).toReal ≤ p) (i : ι) :
    ∫ v, O.Frec probe out ε i v ∂(Measure.pi ν) ≤ Q * (μ₁ + 2 * O.ζ) + kout * p := by
  obtain ⟨K, w, r, hw0, hw1, hmass, hint⟩ := discretise_pi ν (O.Frec probe out ε i)
    (O.measurable_Frec probe out ε i) 1
    (fun v => O.abs_avg_le probe Q v _ fun e => by split_ifs <;> norm_num) η hη
  haveI := disc_nonempty w hw1
  set G := O.disc w r hw0 hw1
  have hrec := G.gallery_recovery i probe kout (Gallery.outL out) Q μ₁ ε p hμ hp
    (fun x => (O.disc_reach w r hw0 hw1 ν η hη.le hmass i x).trans (hcov i x))
    (fun y => (O.disc_ball w r hw0 hw1 ν η hη.le hmass ε i y).trans (hball i y))
  refine hint.trans ?_
  rw [← O.disc_sum w r hw0 hw1]
  calc _ = ∑ v : ι → ι × Fin K, (∏ j, G.π j (v j)) * val (G.resp v) probe (fun h =>
        if ∃ j, ‖(Gallery.outL out h j).1 - G.g (v i)‖ ≤ ε then (1 : ℝ) else 0) Q [] :=
        Finset.sum_congr rfl fun v _ => by rw [O.disc_rec w r hw0 hw1]; rfl
    _ ≤ _ := hrec

/-! ### Density priors, continuous: the dimension laws with `η → 0` -/

section Density

variable (Ks : ι → Submodule ℝ E) [∀ i, (Ks i).HasOrthogonalProjection] (deff : ℕ) (D : ℝ)

/-- v2 §13's standing assumptions for a Borel prior: face `i` lives on `S(Kᵢ)` (a.s.), and
`νᵢ(B̄(y′, ρ)) ≤ D·ρ^{d_eff−1}` for centres `y′ ∈ S(Kᵢ)` (density `≤ D` + v2 Lemma 13.0;
labelled hypothesis). -/
structure ContDensityHyp (ν : ι → Measure (Sph E)) : Prop where
  hD : 1 ≤ D
  hdeff : 2 ≤ deff
  hsupp : ∀ i, ν i {g : Sph E | g.1 ∉ Ks i} = 0
  hcapD : ∀ i (y : E), y ∈ Ks i → ‖y‖ = 1 → ∀ ρ, 0 ≤ ρ →
    (ν i {g : Sph E | ‖y - g.1‖ ≤ ρ}).toReal ≤ D * ρ ^ (deff - 1)

variable {Ks deff D}

lemma projUnit_unit (K : Submodule ℝ E) [K.HasOrthogonalProjection] (y : E)
    (h : K.starProjection y ≠ 0) : projUnit K y ∈ K ∧ ‖projUnit K y‖ = 1 := by
  refine ⟨K.smul_mem _ (K.starProjection_apply_mem y), ?_⟩
  unfold projUnit
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_pos_iff.2 h).ne']

/-- The mass of a set that meets `S(Kᵢ)` only inside `{g : ‖y′ − g‖ ≤ ρ}` is `≤ D·ρ^{d−1}`. -/
lemma mass_via_proj {ν : ι → Measure (Sph E)} [∀ i, IsProbabilityMeasure (ν i)]
    (H : ContDensityHyp Ks deff D ν) (i : ι) (S : Set (Sph E)) (y : E) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hproj : ∀ g ∈ S, g.1 ∈ Ks i → (Ks i).starProjection y ≠ 0 ∧
      ‖projUnit (Ks i) y - g.1‖ ≤ ρ) :
    (ν i S).toReal ≤ D * ρ ^ (deff - 1) := by
  by_cases hP : (Ks i).starProjection y = 0
  · have hsub : S ⊆ {g : Sph E | g.1 ∉ Ks i} := fun g hg hK => (hproj g hg hK).1 hP
    rw [measure_mono_null hsub (H.hsupp i), ENNReal.toReal_zero]
    exact mul_nonneg (by linarith [H.hD]) (pow_nonneg hρ _)
  · obtain ⟨hK, hn⟩ := projUnit_unit (Ks i) y hP
    have hsub : S ⊆ {g : Sph E | g.1 ∉ Ks i} ∪
        {g : Sph E | ‖projUnit (Ks i) y - g.1‖ ≤ ρ} := fun g hg => by
      by_cases hgK : g.1 ∈ Ks i
      · exact Or.inr (hproj g hg hgK).2
      · exact Or.inl hgK
    calc (ν i S).toReal ≤ (ν i ({g : Sph E | g.1 ∉ Ks i} ∪
          {g : Sph E | ‖projUnit (Ks i) y - g.1‖ ≤ ρ})).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      _ ≤ (ν i {g : Sph E | g.1 ∉ Ks i}).toReal +
          (ν i {g : Sph E | ‖projUnit (Ks i) y - g.1‖ ≤ ρ}).toReal := measureReal_union_le _ _
      _ ≤ 0 + D * ρ ^ (deff - 1) := by
          rw [H.hsupp i, ENNReal.toReal_zero]
          exact add_le_add le_rfl (H.hcapD i _ hK hn ρ hρ)
      _ = _ := zero_add _

lemma cont_ball_density {ν : ι → Measure (Sph E)} [∀ i, IsProbabilityMeasure (ν i)]
    (H : ContDensityHyp Ks deff D ν) (i : ι) (y : Sph E) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (ν i (Metric.closedBall y ρ)).toReal ≤ D * ρ ^ (deff - 1) := by
  by_cases hbig : 2 ≤ ρ ^ 2
  · have hρ1 : 1 ≤ ρ := by nlinarith
    calc (ν i (Metric.closedBall y ρ)).toReal ≤ 1 := by
          rw [← measureReal_def]; exact measureReal_le_one
      _ ≤ D * ρ ^ (deff - 1) := by nlinarith [one_le_pow₀ (n := deff - 1) hρ1, H.hD]
  push Not at hbig
  refine mass_via_proj H i _ y.1 ρ hρ fun g hg hgK => ?_
  rw [Metric.mem_closedBall, Subtype.dist_eq, dist_eq_norm] at hg
  have hd : ‖y.1 - g.1‖ ≤ ρ := by rwa [norm_sub_rev]
  have hpos : 0 < inner ℝ y.1 g.1 := by
    have hsq : ‖y.1 - g.1‖ ^ 2 = 2 * (1 - inner ℝ y.1 g.1) := by
      rw [norm_sub_sq_real, y.2, g.2]; ring
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hd 2]
  exact ⟨(proj_inner_ge (Ks i) y.1 g.1 y.2.le hgK hpos).1,
    proj_ball (Ks i) y.1 g.1 y.2 hgK g.2 ρ hbig hd⟩

lemma cont_reach_density {ν : ι → Measure (Sph E)} [∀ i, IsProbabilityMeasure (ν i)]
    (H : ContDensityHyp Ks deff D ν) (i : ι) (x : Sph E) (t : ℝ) (ht : 0 < t) :
    (ν i {g : Sph E | t ≤ inner ℝ x.1 g.1}).toReal ≤ D * Face.chordRad t ^ (deff - 1) := by
  refine mass_via_proj H i _ x.1 _ (Real.sqrt_nonneg _) fun g hg hgK => ?_
  simp only [Set.mem_setOf_eq] at hg
  obtain ⟨hne, -, hn, hge⟩ := proj_inner_ge (Ks i) x.1 g.1 x.2.le hgK (by linarith)
  refine ⟨hne, ?_⟩
  have hsq : ‖projUnit (Ks i) x.1 - g.1‖ ^ 2 = 2 * (1 - inner ℝ (projUnit (Ks i) x.1) g.1) := by
    rw [norm_sub_sq_real, hn, g.2]; ring
  unfold Face.chordRad
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt (by rw [hsq]; linarith)

lemma le_of_small_eta {f : ℝ → ℝ} {Q δ : ℝ} (hδ : 0 < δ)
    (hf : ContinuousWithinAt f (Set.Ioi 0) 0) (h : ∀ η, 0 < η → η < δ → f η ≤ Q) : f 0 ≤ Q :=
  le_of_tendsto hf (Filter.eventually_of_mem (Ioo_mem_nhdsGT hδ) fun η hη => h η hη.1 hη.2)

lemma ge_of_small_eta {f : ℝ → ℝ} {Q δ : ℝ} (hδ : 0 < δ)
    (hf : ContinuousWithinAt f (Set.Ioi 0) 0) (h : ∀ η, 0 < η → η < δ → Q ≤ f η) : Q ≤ f 0 :=
  ge_of_tendsto hf (Filter.eventually_of_mem (Ioo_mem_nhdsGT hδ) fun η hη => h η hη.1 hη.2)

open Classical in
/-- **The dimension law for continuous density priors (v2 Cor 6.2/6.3 Q₁ via §13; P1 P.2(ii)),
radius `ε` not `2ε`.** For a Borel product prior with density `≤ D` on `d_eff`-dimensional
subspheres: if the attacker recovers `m` of `n` faces at `ε` with probability `≥ ½`, then

  `Q ≥ m/(2β*)·((d_eff−1)·log(1/ε) − log(k·D) − log(2en/m))`. -/
theorem cont_blind_m_of_n [Nonempty ι] (hν : 0 ≤ O.ν₀ ∧ O.ν₀ ≤ 1) (βstar : ℝ)
    (hβpos : 0 < βstar) (hβ : ∀ s, bkl (O.κ s) (1 / 2) ≤ βstar)
    (ν : ι → Measure (Sph E)) [∀ i, IsProbabilityMeasure (ν i)] (H : ContDensityHyp Ks deff D ν)
    (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)
    (hk : 1 ≤ kout) (ε : ℝ) (hε : 0 < ε)
    (m : ℝ) (hm : 1 ≤ m) (hmn : m ≤ Fintype.card ι)
    (hPN : 1 / 2 ≤ ∫ v, O.FPN probe out ε m v ∂(Measure.pi ν)) :
    m / (2 * βstar) * (((deff - 1 : ℕ) : ℝ) * Real.log (1 / ε) - Real.log (kout * D) -
      Real.log (2 * Real.exp 1 * Fintype.card ι / m)) ≤ Q := by
  set f : ℝ → ℝ := fun η => m / (2 * βstar) * (((deff - 1 : ℕ) : ℝ) * Real.log (1 / (ε + η)) -
      Real.log (kout * D) - Real.log (2 * Real.exp 1 * Fintype.card ι / m)) with hf
  have h0 : f 0 = m / (2 * βstar) * (((deff - 1 : ℕ) : ℝ) * Real.log (1 / ε) -
      Real.log (kout * D) - Real.log (2 * Real.exp 1 * Fintype.card ι / m)) := by
    simp [hf]
  rw [← h0]
  refine le_of_small_eta one_pos ?_ fun η hη _ => ?_
  · refine ContinuousAt.continuousWithinAt ?_
    have hlog : ContinuousAt (fun η : ℝ => Real.log (1 / (ε + η))) 0 :=
      ContinuousAt.log (continuousAt_const.div (continuousAt_const.add continuousAt_id)
        (by simp; linarith)) (by simp; linarith)
    exact continuousAt_const.mul (((continuousAt_const.mul hlog).sub continuousAt_const).sub
      continuousAt_const)
  · have hρ : 0 < ε + η := by linarith
    have hmain := O.cont_m_of_n hν βstar hβpos hβ ν probe out ε η (D * (ε + η) ^ (deff - 1)) hη
      (mul_nonneg (by linarith [H.hD]) (by positivity))
      (fun i y => cont_ball_density H i y _ hρ.le) m hm hmn hPN
    rwa [Gallery.Lambda_density (k := (kout : ℝ)) (D := D) (by exact_mod_cast hk) (by linarith [H.hD]) hρ]
      at hmain

open Classical in
/-- **The nominated-entry law for continuous density priors (Prop 7.3 via §13; P1 P.1).**
For a Borel product prior with density `≤ D` on `d_eff`-dimensional subspheres and `thr > 0`:

  `P[face i recovered at ε] ≤ Q·(D·r_thr^{d_eff−1} + 2ζ) + k·D·ε^{d_eff−1}`,

`r_thr = √(2(1−thr))`: finding a *specified* face costs `≳ 1/(2D·r_thr^{d_eff−1})` queries,
exponential in `d_eff`. -/
theorem cont_blind_nominated [Nonempty ι]
    (ν : ι → Measure (Sph E)) [∀ i, IsProbabilityMeasure (ν i)] (H : ContDensityHyp Ks deff D ν)
    (hthr : 0 < O.thr) (probe : List Bool → Sph E) {Q kout : ℕ}
    (out : (Fin Q → Bool) → Fin kout → Sph E) (ε : ℝ) (hε : 0 < ε) (i : ι) :
    ∫ v, O.Frec probe out ε i v ∂(Measure.pi ν) ≤
      Q * (D * Face.chordRad O.thr ^ (deff - 1) + 2 * O.ζ) + kout * (D * ε ^ (deff - 1)) := by
  set f : ℝ → ℝ := fun η => Q * (D * Face.chordRad (O.thr - η) ^ (deff - 1) + 2 * O.ζ) +
      kout * (D * (ε + η) ^ (deff - 1)) with hf
  have h0 : f 0 = Q * (D * Face.chordRad O.thr ^ (deff - 1) + 2 * O.ζ) +
      kout * (D * ε ^ (deff - 1)) := by simp [hf]
  rw [← h0]
  refine ge_of_small_eta hthr ?_ fun η hη hηt => ?_
  · refine Continuous.continuousWithinAt ?_
    simp only [hf, Face.chordRad]
    fun_prop
  · exact O.cont_nominated ν probe out ε η _ _ hη
      (mul_nonneg (by linarith [H.hD]) (pow_nonneg (Real.sqrt_nonneg _) _))
      (mul_nonneg (by linarith [H.hD]) (by positivity))
      (fun j x => cont_reach_density H j x _ (by linarith))
      (fun j y => cont_ball_density H j y _ (by linarith)) i

end Density

end Process

end Oracle

end OracleBounds.GeneralPrior
