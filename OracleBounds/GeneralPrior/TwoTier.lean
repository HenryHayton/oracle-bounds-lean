import OracleBounds.GeneralPrior.SingleFace
import OracleBounds.GeneralPrior.Profile

/-!
# Two-tier prior (person clusters): identity tier and template tier lower bounds

Draft §3 / P.5: each enrolled face `i` is a *person* `p` with centre `ctr p`, and a *template*
`g (p, l)` within chordal radius `r_in` of the centre (re-randomised at each enrolment). So
`Fine = P × L`, and the prior on face `i` is any `π i : P × L → ℝ` (person weight `w p =
∑ₗ π i (p, l)`, within-person law `π i (p, ·)/w p`); nothing here needs the factorisation.

Two recovery events for face `i`:
* **identity** at scale `ε_id`: some output within `ε_id` of the person's centre (`idRecovered`);
* **template** at scale `ε`: some output within `ε` of the template (`recovered`, as before).

Results (statements locked by the administrator; proofs by subagent):

* `Face.recovery_near`, `Gallery.gallery_recovery_near` — Prop 7.3 for an arbitrary target
  relation `near` (the coupling never used that the relation is a ball around `g l`);
* `Gallery.identity_recovery` — staircase branch for the identity tier:
  `P[identity i at ε_id] ≤ Q(μ₁+2ζ) + k_out·p_id(ε_id)`, with `p_id` the largest person-prior
  mass of a centre ball;
* `Gallery.identity_info`, `Gallery.identity_queries` — information branch for the identity tier
  (small-ball Fano on the centre relation);
* `Gallery.twoTier_ball_mass` — the two tiers split multiplicatively:
  `π(B(y, ε)) ≤ p_id(r_in + ε) · p_loc(ε)`, `p_loc` the largest *within-person* ball mass;
* `Gallery.two_tier_m_of_n` — hence Cor 6.2(ii) reads
  `Q·β* ≥ (m/2)(Λ_id(r_in+ε) + Λ_loc(ε) − log k_out − log(2en/m))`: identity bits plus
  template bits, additively;
* `Gallery.rerandomised_template`, `Gallery.rerandomised_spread` — an attacker who already knows
  the person (prior concentrated on `{p₀} × L`, e.g. from a previous template) still needs
  `Q·β* ≥ Λ_loc(ε)/2 − log 2`, i.e. `Q ≥ ((d−1)log(r_in/ε) − log k − 2 log 2)/(2β*)` for an
  `(r_in, d)`-spread within-person law. This is the re-randomisation guarantee.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6 OracleBounds.V6.Info

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section face

variable {Fine : Type*} [Fintype Fine] (F : Face E Fine)

open Classical in
/-- **Prop 7.3 for an arbitrary target relation.** `near l y` says output `y` counts as recovering
value `l`; `pn` bounds the prior mass of `{l : near l y}` for every `y`. -/
theorem Face.recovery_near (probe : List Bool → Sph E) (kout : ℕ)
    (out : List Bool → Fin kout → Sph E) (Q : ℕ) (μ₁ pn : ℝ)
    (near : Fine → Sph E → Prop)
    (hcov : ∀ x, (∑ l ∈ Finset.univ.filter (F.reach · x), F.π l) ≤ μ₁)
    (hnear : ∀ y : Sph E, (∑ l ∈ Finset.univ.filter (near · y), F.π l) ≤ pn) :
    ∑ l, F.π l * val (F.pT l) probe
      (fun h => if ∃ j, near l (out h j) then (1 : ℝ) else 0) Q []
      ≤ Q * (μ₁ + 2 * F.ζ) + kout * pn := by
  set Aball : Fine → List Bool → ℝ :=
    fun l h => if ∃ j, near l (out h j) then (1 : ℝ) else 0 with hAdef
  have hA01 : ∀ l h, 0 ≤ Aball l h ∧ Aball l h ≤ 1 := by
    intro l h; simp only [hAdef]; split_ifs <;> norm_num
  have hK : ∀ h : List Bool, h.length = Q → ∑ l, F.π l * Aball l h ≤ kout * pn := by
    intro h _
    have hpts := mass_reached_le F.π near pn F.hπ0 hnear
      (Finset.univ : Finset (Fin kout)) (out h)
    rw [Finset.card_univ, Fintype.card_fin] at hpts
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_)) hpts
    simp only [hAdef, Finset.mem_univ, true_and]
  have hAle : ∀ l h, Aball l h ≤ 1 - (1 - hitInd F.reach probe l h) * (1 - Aball l h) := by
    intro l h
    have h1 := hA01 l h
    have h2 : 0 ≤ hitInd F.reach probe l h ∧ hitInd F.reach probe l h ≤ 1 := by
      unfold hitInd; split_ifs <;> norm_num
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hb := ghost_bound_weighted F.π F.reach probe F.pT F.pG F.ζ μ₁ (kout * pn) Q
    Aball Aball F.hπ0 F.hπ1 F.pT_mem F.pG_mem F.ζ_nonneg F.loc hcov hA01 hK
    (fun l h _ => hAle l h)
  linarith [hb]

end face

variable {ι P L : Type*} [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P]
  [Fintype L] [DecidableEq L]

namespace Gallery

variable (G : Gallery E ι (P × L)) [Nonempty ι] [Nonempty P] [Nonempty L]

open Classical in
/-- **Prop 7.3 for an arbitrary target relation, full gallery.** -/
theorem gallery_recovery_near (i : ι) (probe : List Bool → Sph E) (kout : ℕ)
    (out : List Bool → Fin kout → Sph E) (Q : ℕ) (μ₁ pn : ℝ)
    (near : P × L → Sph E → Prop)
    (hcov : ∀ x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (hnear : ∀ y : Sph E, (∑ l ∈ Finset.univ.filter (near · y), G.π i l) ≤ pn) :
    ∑ v : ι → P × L, (∏ j, G.π j (v j)) * val (G.resp v) probe
      (fun h => if ∃ j, near (v i) (out h j) then (1 : ℝ) else 0) Q []
      ≤ Q * (μ₁ + 2 * G.ζ) + kout * pn := by
  exact G.gallery_avg i probe Q (fun l h => if ∃ j, near l (out h j) then (1 : ℝ) else 0) _
    (fun γ => (G.face i γ).recovery_near probe kout out Q μ₁ pn near hcov hnear)

variable (ctr : P → E)
variable (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)

/-- Identity of face `i` recovered at scale `εid`: some output within `εid` of the centre of
the person of face `i`. -/
def idRecovered (εid : ℝ) (i : ι) (v : ι → P × L) (e : Fin Q → Bool) : Prop :=
  ∃ j, ‖(out e j).1 - ctr (v i).1‖ ≤ εid

open Classical in
/-- `P[identity of face i recovered at εid]`. -/
noncomputable def Pid (εid : ℝ) (i : ι) : ℝ :=
  ∑ v, ∑ e, G.wt probe v e * (if idRecovered ctr out εid i v e then (1 : ℝ) else 0)

open Classical in
/-- **Identity tier, staircase branch.** `P[identity i at εid] ≤ Q(μ₁+2ζ) + k_out·p_id`, where
`p_id` bounds, for every `y`, the prior mass of the persons whose centre is within `εid` of `y`. -/
theorem identity_recovery (i : ι) (μ₁ εid pid : ℝ)
    (hcov : ∀ x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (hid : ∀ y : Sph E,
      (∑ pl ∈ Finset.univ.filter (fun pl : P × L => ‖y.1 - ctr pl.1‖ ≤ εid), G.π i pl) ≤ pid) :
    G.Pid ctr probe out εid i ≤ Q * (μ₁ + 2 * G.ζ) + kout * pid := by
  have h := G.gallery_recovery_near i probe kout (outL out) Q μ₁ pid
    (fun pl y => ‖y.1 - ctr pl.1‖ ≤ εid) hcov hid
  refine le_of_eq_of_le ?_ h
  unfold Pid
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [val_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [outL_ofFn]
  unfold wt idRecovered prior
  ring_nf

open Classical in
/-- `P[identity of face i recovered]` in the per-face joint form used by small-ball Fano
(analogue of `Prec_eq_P`). -/
private lemma Pid_eq_P (εid : ℝ) (i : ι) :
    G.Pid ctr probe out εid i = ∑ le : (P × L) × (Fin Q → Bool),
      (if le.1 ∈ Finset.univ.filter (fun a : P × L => ∃ j, ‖(out le.2 j).1 - ctr a.1‖ ≤ εid) then
        ∑ v ∈ Finset.univ.filter (fun v : ι → P × L => v i = le.1),
          (∏ j, G.π j (v j)) * pathProb (G.resp v) probe Q [] le.2 else 0) := by
  unfold Pid
  set H : (ι → P × L) → (Fin Q → Bool) → ℝ :=
    fun v e => G.wt probe v e * (if idRecovered ctr out εid i v e then (1 : ℝ) else 0) with hH
  have hpt : ∀ (l : P × L) e,
      (if l ∈ Finset.univ.filter (fun a : P × L => ∃ j, ‖(out e j).1 - ctr a.1‖ ≤ εid) then
        ∑ v ∈ Finset.univ.filter (fun v : ι → P × L => v i = l),
          (∏ j, G.π j (v j)) * pathProb (G.resp v) probe Q [] e else 0) =
      ∑ v ∈ Finset.univ.filter (fun v : ι → P × L => v i = l), H v e := by
    intro l e
    split_ifs with hl
    · refine Finset.sum_congr rfl fun v hv => ?_
      have hvi := (Finset.mem_filter.1 hv).2
      rw [Finset.mem_filter] at hl
      simp only [hH, wt, prior, idRecovered, hvi, if_pos hl.2, mul_one]
    · refine (Finset.sum_eq_zero fun v hv => ?_).symm
      have hvi := (Finset.mem_filter.1 hv).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp only [hH, idRecovered, hvi, if_neg hl, mul_zero]
  have hfib : ∀ e, ∑ l, ∑ v ∈ Finset.univ.filter (fun v : ι → P × L => v i = l), H v e =
      ∑ v, H v e := fun e => by
    convert Finset.sum_fiberwise Finset.univ (fun v : ι → P × L => v i) (fun v => H v e)
  rw [Fintype.sum_prod_type]
  simp only [hpt]
  symm
  calc ∑ l, ∑ e, ∑ v ∈ Finset.univ.filter (fun v : ι → P × L => v i = l), H v e
      = ∑ e, ∑ l, ∑ v ∈ Finset.univ.filter (fun v : ι → P × L => v i = l), H v e :=
        Finset.sum_comm
    _ = ∑ e, ∑ v, H v e := Finset.sum_congr rfl fun e _ => hfib e
    _ = ∑ v, ∑ e, H v e := Finset.sum_comm

open Classical in
/-- **Identity tier, information branch (small-ball Fano on centres).**
`P_id·log(1/(k·p_id)) − h(P_id) ≤ I(G; transcript)`. -/
theorem identity_info (εid pid : ℝ) (hp : 0 ≤ pid) (hkp : (kout : ℝ) * pid < 1) (i : ι)
    (hid : ∀ y : Sph E,
      (∑ pl ∈ Finset.univ.filter (fun pl : P × L => ‖y.1 - ctr pl.1‖ ≤ εid), G.π i pl) ≤ pid) :
    G.Pid ctr probe out εid i * Real.log (1 / ((kout : ℝ) * pid)) -
      Real.binEntropy (G.Pid ctr probe out εid i) ≤ G.jointInfo probe Q := by
  set qf : ι → (P × L) × (Fin Q → Bool) → ℝ := fun j le =>
    ∑ v ∈ Finset.univ.filter (fun v : ι → P × L => v j = le.1),
      (∏ k, G.π k (v k)) * pathProb (G.resp v) probe Q [] le.2 with hqf
  have hPv0 : ∀ v e, 0 ≤ pathProb (G.resp v) probe Q [] e :=
    fun v => pathProb_nonneg probe (G.resp_mem v) Q []
  have hPv1 : ∀ v, ∑ e, pathProb (G.resp v) probe Q [] e = 1 :=
    fun v => pathProb_sum probe (G.resp_mem v) Q []
  have hq0 : ∀ j le, 0 ≤ qf j le := fun j le => Finset.sum_nonneg fun v _ =>
    mul_nonneg (Finset.prod_nonneg fun k _ => G.hπ0 k (v k)) (hPv0 v _)
  have hm1 : ∀ j l, marg₁ (qf j) l = G.π j l :=
    fun j l => faceJoint_marg₁ G.π G.hπ1 (fun v e => pathProb (G.resp v) probe Q [] e) hPv1 j l
  have hqsum : ∀ j, ∑ le, qf j le = 1 := by
    intro j
    rw [Fintype.sum_prod_type]
    show ∑ l, marg₁ (qf j) l = 1
    rw [Finset.sum_congr rfl fun l _ => hm1 j l]
    exact G.hπ1 j
  have hb : ∀ c : Sph E, (∑ a ∈ Finset.univ.filter (fun a : P × L => ‖c.1 - ctr a.1‖ ≤ εid),
      marg₁ (qf i) a) ≤ pid := by
    intro c
    rw [Finset.sum_congr rfl fun a _ => hm1 i a]
    exact hid c
  have hF := small_ball_fano (qf i) (hq0 i) (hqsum i)
    (fun (a : P × L) (c : Sph E) => ‖c.1 - ctr a.1‖ ≤ εid) kout out pid hp hkp hb
  simp only at hF
  rw [← G.Pid_eq_P ctr probe out εid i] at hF
  have hsup := mutualInfo_superadditive_prior G.π G.hπ0 G.hπ1
    (fun v e => pathProb (G.resp v) probe Q [] e) hPv0 hPv1
  have hle : mutualInfo (qf i) ≤ ∑ j, mutualInfo (qf j) :=
    Finset.single_le_sum (f := fun j => mutualInfo (qf j))
      (fun j _ => mutualInfo_nonneg _ (hq0 j) (hqsum j)) (Finset.mem_univ i)
  have : mutualInfo (qf i) ≤ G.jointInfo probe Q := by
    unfold jointInfo prior; exact hle.trans hsup
  linarith

open Classical in
/-- **Identifying a specified person with probability `≥ ½`** needs
`Q·β* ≥ log(1/(k·p_id))/2 − log 2`. -/
theorem identity_queries (βstar : ℝ) (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar)
    (εid pid : ℝ) (hp : 0 ≤ pid) (hkp : (kout : ℝ) * pid < 1) (i : ι)
    (hid : ∀ y : Sph E,
      (∑ pl ∈ Finset.univ.filter (fun pl : P × L => ‖y.1 - ctr pl.1‖ ≤ εid), G.π i pl) ≤ pid)
    (hPi : 1 / 2 ≤ G.Pid ctr probe out εid i) :
    Real.log (1 / ((kout : ℝ) * pid)) / 2 - Real.log 2 ≤ Q * βstar := by
  have hF := G.identity_info ctr probe out εid pid hp hkp i hid
  have hB := info_le_global G.prior G.prior_nonneg G.prior_sum G.resp (fun v x => G.resp_mem v x)
    probe βstar hβ Q
  have hJ : G.jointInfo probe Q ≤ βstar * Q := by unfold jointInfo; exact hB
  have hΛ := Lambda_nonneg (kout := kout) hp hkp
  have hh : Real.binEntropy (G.Pid ctr probe out εid i) ≤ Real.log 2 :=
    Real.binEntropy_le_log_two
  have : Real.log (1 / ((kout : ℝ) * pid)) / 2 ≤
      G.Pid ctr probe out εid i * Real.log (1 / ((kout : ℝ) * pid)) := by nlinarith
  linarith

open Classical in
/-- A filtered sum over `P × L` split as a sum over persons of filtered sums over templates. -/
private lemma sum_filter_prod (i : ι) (y : Sph E) (ε : ℝ) :
    (∑ pl ∈ Finset.univ.filter (fun pl : P × L => ‖y.1 - G.g pl‖ ≤ ε), G.π i pl) =
      ∑ p, ∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g (p, l)‖ ≤ ε), G.π i (p, l) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Finset.sum_filter]

open Classical in
/-- **The two tiers split.** If every template lies within `r_in` of its person's centre, the
prior mass of a template ball of radius `ε` is at most (person mass of the centre ball of radius
`r_in + ε`) × (largest within-person ball mass). Here `hloc` is the within-person bound in
unnormalised form: `∑_{l : ‖y − g(p,l)‖ ≤ ε} π(p,l) ≤ p_loc · ∑_l π(p,l)`. -/
theorem twoTier_ball_mass (i : ι) (y : Sph E) (ε rin pid ploc : ℝ) (hploc : 0 ≤ ploc)
    (hin : ∀ p l, ‖G.g (p, l) - ctr p‖ ≤ rin)
    (hid : (∑ p ∈ Finset.univ.filter (fun p => ‖y.1 - ctr p‖ ≤ rin + ε),
      ∑ l, G.π i (p, l)) ≤ pid)
    (hloc : ∀ p, (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g (p, l)‖ ≤ ε), G.π i (p, l))
      ≤ ploc * ∑ l, G.π i (p, l)) :
    (∑ pl ∈ Finset.univ.filter (fun pl : P × L => ‖y.1 - G.g pl‖ ≤ ε), G.π i pl)
      ≤ pid * ploc := by
  set S : P → ℝ := fun p => ∑ l, G.π i (p, l) with hS
  set A : Finset P := Finset.univ.filter (fun p => ‖y.1 - ctr p‖ ≤ rin + ε) with hA
  have hinner : ∀ p, (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g (p, l)‖ ≤ ε), G.π i (p, l))
      ≤ if p ∈ A then ploc * S p else 0 := by
    intro p
    split_ifs with hp
    · exact hloc p
    · apply le_of_eq
      apply Finset.sum_eq_zero
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      exfalso
      apply hp
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
      calc ‖y.1 - ctr p‖ = ‖(y.1 - G.g (p, l)) + (G.g (p, l) - ctr p)‖ := by congr 1; abel
        _ ≤ ‖y.1 - G.g (p, l)‖ + ‖G.g (p, l) - ctr p‖ := norm_add_le _ _
        _ ≤ ε + rin := add_le_add hl (hin p l)
        _ = rin + ε := by ring
  rw [G.sum_filter_prod i y ε]
  refine le_trans (Finset.sum_le_sum fun p _ => hinner p) ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
  calc ploc * ∑ p ∈ A, S p ≤ ploc * pid := mul_le_mul_of_nonneg_left hid hploc
    _ = pid * ploc := mul_comm _ _

open Classical in
/-- **Cor 6.2(ii) for the two-tier prior: identity bits plus template bits.** With
`Λ_id = log(1/p_id(r_in+ε))` and `Λ_loc = log(1/p_loc(ε))`, if `P[N_ε ≥ m] ≥ ½` then
`(m/2)(Λ_id + Λ_loc − log k_out − log(2en/m)) ≤ B_best ≤ Q·β*`. -/
theorem two_tier_m_of_n (hν : 0 ≤ G.ν₀ ∧ G.ν₀ ≤ 1) (βstar : ℝ)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ i x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (ε rin pid ploc : ℝ) (hpid : 0 < pid) (hploc : 0 < ploc) (hk : 1 ≤ kout)
    (hkp : (kout : ℝ) * (pid * ploc) < 1)
    (hin : ∀ p l, ‖G.g (p, l) - ctr p‖ ≤ rin)
    (hid : ∀ i (y : Sph E), (∑ p ∈ Finset.univ.filter (fun p => ‖y.1 - ctr p‖ ≤ rin + ε),
      ∑ l, G.π i (p, l)) ≤ pid)
    (hloc : ∀ i (y : Sph E) p,
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g (p, l)‖ ≤ ε), G.π i (p, l))
        ≤ ploc * ∑ l, G.π i (p, l))
    (m : ℝ) (hm : 1 ≤ m) (hmn : m ≤ Fintype.card ι) (hPN : 1 / 2 ≤ G.PN probe out ε m)
    (hL : Real.log (2 * Real.exp 1 * Fintype.card ι / m) ≤
      Real.log (1 / pid) + Real.log (1 / ploc) - Real.log kout) :
    m / 2 * (Real.log (1 / pid) + Real.log (1 / ploc) - Real.log kout -
        Real.log (2 * Real.exp 1 * Fintype.card ι / m)) ≤
      Bbest (Fintype.card ι) μ₁ G.ζ G.ν₀ βstar Q := by
  have hball : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ pid * ploc :=
    fun i y => G.twoTier_ball_mass ctr i y ε rin pid ploc hploc.le hin (hid i y) (hloc i y)
  have h := G.cor62_ii probe out hν βstar hβ μ₁ hμ hcov ε (pid * ploc)
    (by positivity) hkp hball m hm hmn hPN
  have hΛ : Real.log (1 / ((kout : ℝ) * (pid * ploc))) =
      Real.log (1 / pid) + Real.log (1 / ploc) - Real.log kout := by
    have hk0 : (0 : ℝ) < kout := by exact_mod_cast hk
    simp only [one_div, Real.log_inv]
    rw [Real.log_mul hk0.ne' (by positivity), Real.log_mul hpid.ne' hploc.ne']
    ring
  rw [hΛ] at h
  exact h.2 hL

open Classical in
/-- **Re-randomisation: knowing the person does not give the template.** If face `i`'s prior is
concentrated on person `p₀` (the attacker already knows who it is), recovering the fresh template
at `ε` with probability `≥ ½` still needs `Q·β* ≥ log(1/(k·p_loc))/2 − log 2`. -/
theorem rerandomised_template (βstar : ℝ) (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar)
    (i : ι) (p₀ : P) (hconc : ∀ p l, p ≠ p₀ → G.π i (p, l) = 0)
    (ε ploc : ℝ) (hploc : 0 ≤ ploc) (hkp : (kout : ℝ) * ploc < 1)
    (hloc : ∀ y : Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g (p₀, l)‖ ≤ ε), G.π i (p₀, l)) ≤ ploc)
    (hPi : 1 / 2 ≤ G.Prec probe out ε i) :
    Real.log (1 / ((kout : ℝ) * ploc)) / 2 - Real.log 2 ≤ Q * βstar := by
  have hball : ∀ y : Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ ploc := by
    intro y
    rw [G.sum_filter_prod i y ε, Finset.sum_eq_single p₀]
    · exact hloc y
    · intro p _ hp
      exact Finset.sum_eq_zero fun l _ => hconc p l hp
    · intro h; exact absurd (Finset.mem_univ p₀) h
  exact G.single_face_queries probe out βstar hβ ε ploc hploc hkp i hball hPi

open Classical in
/-- **Re-randomisation, spread form.** If the within-person law of `p₀` is `(r_in, d)`-spread
(`ball mass ≤ (ε/r_in)^{d−1}`), then `Q ≥ ((d−1)·log(r_in/ε) − log k − 2 log 2)/(2β*)`. -/
theorem rerandomised_spread (βstar : ℝ) (hβpos : 0 < βstar)
    (hβ : ∀ v x, bkl (G.resp v x) (1 / 2) ≤ βstar) (hk : 1 ≤ kout)
    (i : ι) (p₀ : P) (hconc : ∀ p l, p ≠ p₀ → G.π i (p, l) = 0)
    (rin ε : ℝ) (hrin : 0 < rin) (hε : 0 < ε) (d : ℕ)
    (hspread : ∀ y : Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g (p₀, l)‖ ≤ ε), G.π i (p₀, l))
        ≤ (ε / rin) ^ (d - 1))
    (hkp : (kout : ℝ) * (ε / rin) ^ (d - 1) < 1)
    (hPi : 1 / 2 ≤ G.Prec probe out ε i) :
    (((d - 1 : ℕ) : ℝ) * Real.log (rin / ε) - Real.log kout - 2 * Real.log 2) / (2 * βstar)
      ≤ Q := by
  have h := G.rerandomised_template probe out βstar hβ i p₀ hconc ε _ (by positivity) hkp
    hspread hPi
  have hΛ : Real.log (1 / ((kout : ℝ) * (ε / rin) ^ (d - 1))) =
      ((d - 1 : ℕ) : ℝ) * Real.log (rin / ε) - Real.log kout := by
    have hk0 : (0 : ℝ) < kout := by exact_mod_cast hk
    rw [one_div, Real.log_inv, Real.log_mul hk0.ne' (by positivity), Real.log_pow,
      Real.log_div hε.ne' hrin.ne', Real.log_div hrin.ne' hε.ne']
    ring
  rw [hΛ] at h
  rw [div_le_iff₀ (by positivity)]
  linarith

end Gallery

end OracleBounds.GeneralPrior
