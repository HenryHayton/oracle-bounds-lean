import OracleBounds.GeneralPrior.Coupling
import OracleBounds.V6.Operational

/-!
# One face under a general prior (`n-face-general-prior-v1` §§1–2, 4, 7)

Fix one face and summarise everything about the *other* faces by a single function `m : E → ℝ`
(the maximum score they contribute, at a fixed realisation — see `GeneralPrior.Gallery` for how
`m` is built and averaged over). This mirrors `OracleBounds.V6.FaceSetting`, but drops the
cap/centre/`r₀` layer entirely: the hidden value `l` of this face is drawn from an arbitrary
finite prior `π` on `Fine`, and both the *reach* test and the *response* use the same embedding
`g l` directly (no coarse/fine split), exactly Definitions 1.2/1.5/2.1 of the note.

No `sorry`s.
-/

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One face with its environment (the other faces) summarised by `m`. -/
structure Face (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Fine : Type*)
    [Fintype Fine] where
  thr : ℝ
  τacc : ℝ
  hτ : thr < τacc
  κ : ℝ → ℝ
  ν₀ : ℝ
  ζ : ℝ
  hκ : ∀ s, 0 ≤ κ s ∧ κ s ≤ 1
  hband : ∀ s ≤ thr, |κ s - ν₀| ≤ ζ
  g : Fine → E
  m : E → ℝ
  π : Fine → ℝ
  hπ0 : ∀ l, 0 ≤ π l
  hπ1 : ∑ l, π l = 1

namespace Face

variable {Fine : Type*} [Fintype Fine] (F : Face E Fine)

/-- True response probability when this face takes value `l`. -/
noncomputable def pT (l : Fine) (x : Sph E) : ℝ := F.κ (max (inner ℝ x.1 (F.g l)) (F.m x.1))

/-- Ghost response probability (this face's contribution removed). -/
noncomputable def pG (x : Sph E) : ℝ := F.κ (F.m x.1)

/-- `x` *reaches* value `l` (Def 1.5). -/
def reach (l : Fine) (x : Sph E) : Prop := F.thr < inner ℝ x.1 (F.g l)

/-- `y` is *accepted* by value `l` (Def 1.5). -/
def accepts (l : Fine) (y : Sph E) : Prop := F.τacc ≤ inner ℝ y.1 (F.g l)

lemma ζ_nonneg : 0 ≤ F.ζ := (abs_nonneg _).trans (F.hband F.thr le_rfl)

lemma pT_mem (l : Fine) (x : Sph E) : 0 ≤ F.pT l x ∧ F.pT l x ≤ 1 := F.hκ _
lemma pG_mem (x : Sph E) : 0 ≤ F.pG x ∧ F.pG x ≤ 1 := F.hκ _

/-- Acceptance implies reach (`τacc > thr`). -/
lemma reach_of_accepts (l : Fine) (y : Sph E) (hy : F.accepts l y) : F.reach l y :=
  lt_of_lt_of_le F.hτ hy

/-- **Locality** (proof of Lemma 4.1, cases 2–3): off the reach of `l`, true and ghost responses
are within `2ζ`. Simpler than `OracleBounds.V6.kernel_locality`/`reach_of_match`, since there is
no cap/centre gap here: reach and response use the same `g l`. -/
lemma loc (l : Fine) (x : Sph E) (hx : ¬ F.reach l x) : |F.pT l x - F.pG x| ≤ 2 * F.ζ := by
  unfold reach at hx
  push Not at hx
  unfold pT pG
  rcases le_total (F.m x.1) F.thr with hb | hb
  · have h1 := F.hband _ (max_le hx hb)
    have h2 := F.hband _ hb
    have h2' : |F.ν₀ - F.κ (F.m x.1)| ≤ F.ζ := by rwa [abs_sub_comm] at h2
    calc |F.κ (max (inner ℝ x.1 (F.g l)) (F.m x.1)) - F.κ (F.m x.1)|
        ≤ |F.κ (max (inner ℝ x.1 (F.g l)) (F.m x.1)) - F.ν₀| + |F.ν₀ - F.κ (F.m x.1)| :=
          abs_sub_le _ _ _
      _ ≤ F.ζ + F.ζ := by linarith
      _ = 2 * F.ζ := by ring
  · have hle : inner ℝ x.1 (F.g l) ≤ F.m x.1 := hx.trans hb
    rw [max_eq_right hle]
    simp [F.ζ_nonneg]

open Classical in
/-- **Cor 4.2 (hitting), general prior — G1.** `P[T ≤ K] ≤ K(μ₁ + 2ζ)`. -/
theorem hitting_bound (probe : List Bool → Sph E) (K : ℕ) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ x, (∑ l ∈ Finset.univ.filter (F.reach · x), F.π l) ≤ μ₁) :
    ∑ l, F.π l * val (F.pT l) probe (hitInd F.reach probe l) K [] ≤ K * (μ₁ + 2 * F.ζ) := by
  have hb := ghost_bound_weighted F.π F.reach probe F.pT F.pG F.ζ μ₁ 0 K
    (hitInd F.reach probe) (fun _ _ => 0) F.hπ0 F.hπ1 F.pT_mem F.pG_mem F.ζ_nonneg F.loc hcov
    (fun _ _ => by norm_num) (fun _ _ => by simp) (fun l h _ => by simp)
  calc ∑ l, F.π l * val (F.pT l) probe (hitInd F.reach probe l) K []
      ≤ K * μ₁ + 0 + 2 * K * F.ζ := hb
    _ = K * (μ₁ + 2 * F.ζ) := by ring

open Classical in
/-- **Prop 7.3 (coarse recovery at scale `ε`), general prior — G4.**
`P[face recovered at ε] ≤ Q(μ₁ + 2ζ) + k_out·p(ε)`, where `p(ε)` bounds the prior mass of every
closed `ε`-ball centred on the sphere (at this one `ε`; no sign condition on `ε` is needed). -/
theorem coarse_recovery_bound (probe : List Bool → Sph E) (kout : ℕ)
    (out : List Bool → Fin kout → Sph E) (Q : ℕ) (μ₁ ε pε : ℝ) (hμ : 0 ≤ μ₁) (hp : 0 ≤ pε)
    (hcov : ∀ x, (∑ l ∈ Finset.univ.filter (F.reach · x), F.π l) ≤ μ₁)
    (hballcov : ∀ y : Sph E, (∑ l ∈ Finset.univ.filter
        (fun l => ‖y.1 - F.g l‖ ≤ ε), F.π l) ≤ pε) :
    ∑ l, F.π l * val (F.pT l) probe
      (fun h => if ∃ j, ‖(out h j).1 - F.g l‖ ≤ ε then (1 : ℝ) else 0) Q []
      ≤ Q * (μ₁ + 2 * F.ζ) + kout * pε := by
  set Aball : Fine → List Bool → ℝ :=
    fun l h => if ∃ j, ‖(out h j).1 - F.g l‖ ≤ ε then (1 : ℝ) else 0 with hAdef
  have hA01 : ∀ l h, 0 ≤ Aball l h ∧ Aball l h ≤ 1 := by
    intro l h; simp only [hAdef]; split_ifs <;> norm_num
  set reachB : Fine → Sph E → Prop := fun l y => ‖y.1 - F.g l‖ ≤ ε with hreachBdef
  have hK : ∀ h : List Bool, h.length = Q → ∑ l, F.π l * Aball l h ≤ kout * pε := by
    intro h _
    have hpts := mass_reached_le F.π reachB pε F.hπ0 hballcov
      (Finset.univ : Finset (Fin kout)) (out h)
    rw [Finset.card_univ, Fintype.card_fin] at hpts
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_)) hpts
    simp only [hAdef, hreachBdef, Finset.mem_univ, true_and]
  have hAle : ∀ l h, Aball l h ≤ 1 - (1 - hitInd F.reach probe l h) * (1 - Aball l h) := by
    intro l h
    have h1 := hA01 l h
    have h2 : 0 ≤ hitInd F.reach probe l h ∧ hitInd F.reach probe l h ≤ 1 := by
      unfold hitInd; split_ifs <;> norm_num
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hb := ghost_bound_weighted F.π F.reach probe F.pT F.pG F.ζ μ₁ (kout * pε) Q
    Aball Aball F.hπ0 F.hπ1 F.pT_mem F.pG_mem F.ζ_nonneg F.loc hcov hA01 hK
    (fun l h _ => hAle l h)
  linarith [hb]

open Classical in
/-- **Thm 7.1 (impersonation), general prior — G5.** A probe or output *matches* this face if it
is accepted. `P[some probe or output matches] ≤ Q(μ₁ + 2ζ) + k_out·μacc`. -/
theorem impersonation_bound (probe : List Bool → Sph E) (kout : ℕ)
    (out : List Bool → Fin kout → Sph E) (Q : ℕ) (μ₁ μacc : ℝ) (hμ : 0 ≤ μ₁) (hacc : 0 ≤ μacc)
    (hcov : ∀ x, (∑ l ∈ Finset.univ.filter (F.reach · x), F.π l) ≤ μ₁)
    (haccov : ∀ y, (∑ l ∈ Finset.univ.filter (F.accepts · y), F.π l) ≤ μacc) :
    ∑ l, F.π l * val (F.pT l) probe (fun h =>
        if (∃ k < h.length, F.accepts l (probe (h.take k))) ∨ (∃ j, F.accepts l (out h j))
          then (1 : ℝ) else 0) Q []
      ≤ Q * (μ₁ + 2 * F.ζ) + kout * μacc := by
  set A : Fine → List Bool → ℝ := fun l h =>
    if (∃ k < h.length, F.accepts l (probe (h.take k))) ∨ (∃ j, F.accepts l (out h j))
      then (1 : ℝ) else 0 with hAdef
  set Eout : Fine → List Bool → ℝ := fun l h => if ∃ j, F.accepts l (out h j) then 1 else 0
    with hEoutdef
  have hE01 : ∀ l h, 0 ≤ Eout l h ∧ Eout l h ≤ 1 := by
    intro l h; simp only [hEoutdef]; split_ifs <;> norm_num
  have hK : ∀ h : List Bool, h.length = Q → ∑ l, F.π l * Eout l h ≤ kout * μacc := by
    intro h _
    have hpts := mass_reached_le F.π F.accepts μacc F.hπ0 haccov
      (Finset.univ : Finset (Fin kout)) (out h)
    rw [Finset.card_univ, Fintype.card_fin] at hpts
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_)) hpts
    simp only [hEoutdef, Finset.mem_univ, true_and]
  have hAle : ∀ l, ∀ h : List Bool, h.length = Q →
      A l h ≤ 1 - (1 - hitInd F.reach probe l h) * (1 - Eout l h) := by
    intro l h _
    have hit01 := by
      show 0 ≤ hitInd F.reach probe l h ∧ hitInd F.reach probe l h ≤ 1
      unfold hitInd; split_ifs <;> norm_num
    have hE := hE01 l h
    simp only [hAdef]
    split_ifs with hcase
    · rcases hcase with ⟨k, hk, hm⟩ | ⟨j, hm⟩
      · have h1 : hitInd F.reach probe l h = 1 := by
          unfold hitInd
          rw [if_pos ⟨k, hk, F.reach_of_accepts l _ hm⟩]
        rw [h1]; simp
      · have h1 : Eout l h = 1 := by
          simp only [hEoutdef]; rw [if_pos ⟨j, hm⟩]
        rw [h1]; simp
    · nlinarith
  have hb := ghost_bound_weighted F.π F.reach probe F.pT F.pG F.ζ μ₁ (kout * μacc) Q
    A Eout F.hπ0 F.hπ1 F.pT_mem F.pG_mem F.ζ_nonneg F.loc hcov hE01 hK hAle
  linarith [hb]

/-! ### The ball-mass reduction (note P1, Lemma P.0(a))

`‖x − g‖² = 2(1 − ⟨x, g⟩)` for unit vectors, so the reach set of a probe is exactly a closed ball
of chordal radius `r_thr = √(2(1 − thr))` centred at the probe. Hence the single function
`p(·)` (largest ball mass) controls `μ₁` as well: no separate reach-coverage hypothesis is needed,
and this is how the *decision threshold* enters every bound as a variable. -/

/-- Chordal radius of the score-`t` cap. -/
noncomputable def chordRad (t : ℝ) : ℝ := Real.sqrt (2 * (1 - t))

/-- Reach is containment in a ball of chordal radius `r_thr` about the probe. -/
lemma reach_imp_ball (l : Fine) (x : Sph E) (hg : ‖F.g l‖ = 1) (hx : F.reach l x) :
    ‖x.1 - F.g l‖ ≤ chordRad F.thr := by
  have hsq : ‖x.1 - F.g l‖ ^ 2 = 2 * (1 - inner ℝ x.1 (F.g l)) := by
    rw [norm_sub_sq_real, x.2, hg]; ring
  have hlt : ‖x.1 - F.g l‖ ^ 2 ≤ 2 * (1 - F.thr) := by
    rw [hsq]; unfold reach at hx; linarith
  calc ‖x.1 - F.g l‖ = Real.sqrt (‖x.1 - F.g l‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ chordRad F.thr := Real.sqrt_le_sqrt hlt

open Classical in
/-- **Lemma P.0(a).** A bound on ball masses at radius `r_thr` is a bound on reach coverage:
`μ₁ ≤ p(r_thr)`. So `hcov` never has to be assumed separately. -/
lemma cov_of_ballcov (hg : ∀ l, ‖F.g l‖ = 1) (p₀ : ℝ)
    (hball : ∀ y : E, (∑ l ∈ Finset.univ.filter (fun l => ‖y - F.g l‖ ≤ chordRad F.thr), F.π l)
      ≤ p₀) (x : Sph E) :
    (∑ l ∈ Finset.univ.filter (F.reach · x), F.π l) ≤ p₀ := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun l _ _ => F.hπ0 l)) (hball x.1)
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
  exact F.reach_imp_ball l x (hg l) hl

end Face

end OracleBounds.GeneralPrior
