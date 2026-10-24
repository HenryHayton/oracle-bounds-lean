import OracleBounds.GeneralPrior.Mixture

/-!
# The covering profile (upper-bounds note v1.2, §5B)

`Cor 4.2` / `Prop 7.3` bound the ghost trajectory's reach mass by `Q·μ₁`, a union bound over the
`Q` ghost probes. The U1 note (v1.2, Lemma 5B.2) observes that the same coupling gives the mass
of the **union** of the ghost caps, i.e. the prior's *covering profile*

  `M_π(Q) := sup_{x₁,…,x_Q} π(⋃_k cap(x_k, thr))`,

and that `Cor 6.2(i)` is the linearisation `M_π(Q) ≤ Q·μ₁` of the profile bound — exact for the
uniform prior, arbitrarily loose for two-scale priors (its Example 5B.5).

Here `M` enters as a labelled hypothesis (`hprof`): the mass of the union of *any* `Q` reach
sets is `≤ M`. The results are the `ζ`-general forms (the note states them at `ζ = 0`):

* `ghost_bound_profile` — the engine, `≤ M + K + 2Qζ`;
* `Face.hitting_profile`, `Face.recovery_profile`, `Gallery.gallery_hitting_profile`,
  `Gallery.gallery_recovery_profile` — Lemma 5B.2 (`P[T(i) ≤ Q] ≤ M_i + 2Qζ`,
  `P[face i recovered] ≤ M_i + 2Qζ + k_out·p(ε)`);
* `Gallery.EN_le_profile`, `Gallery.prop5B3` — Prop 5B.3
  (`P[N_ε ≥ m] ≥ ½ ∧ n·k_out·p(ε) ≤ m/8 ⇒ 3m/8 ≤ ∑ᵢ M_i + 2nQζ`);
* `Gallery.first_contact_profile` — `P[T ≤ Q] ≤ ∑ᵢ (M_i + 2Qζ)` (Prop 3.3's input).

`profile_le_linear` recovers the old hypothesis: `hcov` at `μ₁` gives `hprof` at `Q·μ₁`.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {X : Type*}

/-- The union of `Q` reach sets has mass at most `Q·c` when each has mass at most `c`. -/
lemma profile_le_linear {Fine : Type*} [Fintype Fine] (π : Fine → ℝ) (reach : Fine → X → Prop)
    [∀ l x, Decidable (reach l x)] (c : ℝ) (hπ0 : ∀ l, 0 ≤ π l)
    (hcov : ∀ x, (∑ l ∈ Finset.univ.filter (reach · x), π l) ≤ c) (Q : ℕ) (y : ℕ → X)
    [∀ l, Decidable (∃ k < Q, reach l (y k))] :
    (∑ l ∈ Finset.univ.filter (fun l => ∃ k < Q, reach l (y k)), π l) ≤ Q * c := by
  have h := mass_reached_le π reach c hπ0 hcov (Finset.range Q) y
  rw [Finset.card_range] at h
  refine le_trans (le_of_eq ?_) h
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Finset.mem_range]
  split_ifs <;> simp

open Classical in
/-- **Weighted ghost bound, covering-profile form.** As `ghost_bound_weighted`, but the per-point
hypothesis `hcov` is replaced by a bound `M` on the prior mass of the union of any `Q` reach sets;
the conclusion is `M + K + 2Qζ` in place of `Q·c + K + 2Qζ`. -/
theorem ghost_bound_profile {Fine : Type*} [Fintype Fine] (π : Fine → ℝ)
    (reach : Fine → X → Prop) [∀ l x, Decidable (reach l x)]
    (probe : List Bool → X) (pT : Fine → X → ℝ) (pG : X → ℝ) (ζ M K : ℝ) (Q : ℕ)
    (A E : Fine → List Bool → ℝ)
    (hπ0 : ∀ l, 0 ≤ π l) (hπ1 : ∑ l, π l = 1)
    (hpT : ∀ l x, 0 ≤ pT l x ∧ pT l x ≤ 1) (hpG : ∀ x, 0 ≤ pG x ∧ pG x ≤ 1) (hζ : 0 ≤ ζ)
    (hloc : ∀ l, ∀ x, ¬ reach l x → |pT l x - pG x| ≤ 2 * ζ)
    (hprof : ∀ y : ℕ → X,
      (∑ l ∈ Finset.univ.filter (fun l => ∃ k < Q, reach l (y k)), π l) ≤ M)
    (hE : ∀ l h, 0 ≤ E l h ∧ E l h ≤ 1)
    (hK : ∀ h : List Bool, h.length = Q → ∑ l, π l * E l h ≤ K)
    (hA : ∀ l, ∀ h : List Bool, h.length = Q →
      A l h ≤ 1 - (1 - hitInd reach probe l h) * (1 - E l h)) :
    ∑ l, π l * val (pT l) probe (A l) Q [] ≤ M + K + 2 * Q * ζ := by
  set N : Fine → List Bool → ℝ := fun l h => (1 - hitInd reach probe l h) * (1 - E l h) with hN
  have hit01 : ∀ l h, 0 ≤ hitInd reach probe l h ∧ hitInd reach probe l h ≤ 1 := by
    intro l h; unfold hitInd; split_ifs <;> norm_num
  have hN01 : ∀ l h, 0 ≤ N l h ∧ N l h ≤ 1 := by
    intro l h
    have := hit01 l h; have := hE l h
    exact ⟨mul_nonneg (by linarith) (by linarith), by nlinarith⟩
  have hNhit : ∀ l h, hitBy (reach l) probe h → N l h = 0 := by
    intro l h hh; simp [hN, hitInd, hh]
  have per : ∀ l, val (pT l) probe (A l) Q [] ≤
      val pG probe (fun h => hitInd reach probe l h + E l h) Q [] + 2 * Q * ζ := by
    intro l
    have c1 : val (pT l) probe (A l) Q [] ≤ val (pT l) probe (fun h => 1 + (-1) * N l h) Q [] :=
      val_mono probe (hpT l) Q [] (fun h' hl => by
        have := hA l h' (by simpa using hl); simp only [hN] at *; linarith)
    have c2 := val_coupling probe (pT l) pG (reach l) ζ (hpT l) hpG hζ (hloc l) (N l)
      (hN01 l) (hNhit l) Q []
    have c3 : val pG probe (fun h => 1 + (-1) * N l h) Q [] ≤
        val pG probe (fun h => hitInd reach probe l h + E l h) Q [] :=
      val_mono probe hpG Q [] (fun h' _ => by
        have := hit01 l h'; have := hE l h'; simp only [hN]; nlinarith)
    rw [val_affine] at c1 c3
    have := (abs_le.mp c2).1
    linarith
  have step1 : ∑ l, π l * val (pT l) probe (A l) Q [] ≤
      ∑ l, π l * val pG probe (fun h => hitInd reach probe l h + E l h) Q [] + 2 * Q * ζ := by
    calc ∑ l, π l * val (pT l) probe (A l) Q []
        ≤ ∑ l, π l * (val pG probe (fun h => hitInd reach probe l h + E l h) Q [] + 2 * Q * ζ) :=
          Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (per l) (hπ0 l))
      _ = ∑ l, π l * val pG probe (fun h => hitInd reach probe l h + E l h) Q [] +
            2 * Q * ζ * ∑ l, π l := by
          rw [Finset.mul_sum]; ring_nf; rw [Finset.sum_add_distrib]; ring_nf
      _ = _ := by rw [hπ1]; ring
  have step2 : ∑ l, π l * val pG probe (fun h => hitInd reach probe l h + E l h) Q [] =
      val pG probe (fun h => ∑ l, π l * (hitInd reach probe l h + E l h)) Q [] := by
    rw [val_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := val_affine pG probe 0 (π l) (fun h => hitInd reach probe l h + E l h) Q []
    simpa using this.symm
  have step3 : val pG probe (fun h => ∑ l, π l * (hitInd reach probe l h + E l h)) Q [] ≤
      M + K := by
    have hb : val pG probe (fun h => ∑ l, π l * (hitInd reach probe l h + E l h)) Q [] ≤
        val pG probe (fun _ => M + K) Q [] := by
      apply val_mono probe hpG Q []
      intro h' hl
      simp only [List.length_nil, zero_add] at hl
      -- the profile step: the hit mass is the mass of the union of the ghost caps
      have hc : ∑ l, π l * hitInd reach probe l h' ≤ M := by
        have hpts := hprof (fun k => probe (h'.take k))
        refine le_trans (le_of_eq ?_) hpts
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun l _ => ?_
        unfold hitInd hitBy
        rw [hl]
        split_ifs <;> simp
      have hKb := hK h' hl
      calc ∑ l, π l * (hitInd reach probe l h' + E l h')
          = ∑ l, π l * hitInd reach probe l h' + ∑ l, π l * E l h' := by
            rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun l _ => by ring
        _ ≤ M + K := by linarith
    rwa [val_const] at hb
  linarith [step1, step2 ▸ step3]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Fine : Type*} [Fintype Fine]

namespace Face

variable (F : Face E Fine)

open Classical in
/-- **Lemma 5B.2 (hitting), one face.** `P[T ≤ Q] ≤ M + 2Qζ` where `M` bounds the prior mass
of the union of any `Q` reach sets. -/
theorem hitting_profile (probe : List Bool → Sph E) (Q : ℕ) (M : ℝ)
    (hprof : ∀ y : ℕ → Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ∃ k < Q, F.reach l (y k)), F.π l) ≤ M) :
    ∑ l, F.π l * val (F.pT l) probe (hitInd F.reach probe l) Q [] ≤ M + 2 * Q * F.ζ := by
  have hb := ghost_bound_profile F.π F.reach probe F.pT F.pG F.ζ M 0 Q
    (hitInd F.reach probe) (fun _ _ => 0) F.hπ0 F.hπ1 F.pT_mem F.pG_mem F.ζ_nonneg F.loc hprof
    (fun _ _ => by norm_num) (fun _ _ => by simp) (fun l h _ => by simp)
  linarith

open Classical in
/-- **Lemma 5B.2 (recovery), one face.** `P[face recovered at ε] ≤ M + 2Qζ + k_out·p(ε)`. -/
theorem recovery_profile (probe : List Bool → Sph E) (kout : ℕ)
    (out : List Bool → Fin kout → Sph E) (Q : ℕ) (M ε pε : ℝ)
    (hprof : ∀ y : ℕ → Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ∃ k < Q, F.reach l (y k)), F.π l) ≤ M)
    (hballcov : ∀ y : Sph E, (∑ l ∈ Finset.univ.filter
        (fun l => ‖y.1 - F.g l‖ ≤ ε), F.π l) ≤ pε) :
    ∑ l, F.π l * val (F.pT l) probe
      (fun h => if ∃ j, ‖(out h j).1 - F.g l‖ ≤ ε then (1 : ℝ) else 0) Q []
      ≤ M + 2 * Q * F.ζ + kout * pε := by
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
  have hb := ghost_bound_profile F.π F.reach probe F.pT F.pG F.ζ M (kout * pε) Q
    Aball Aball F.hπ0 F.hπ1 F.pT_mem F.pG_mem F.ζ_nonneg F.loc hprof hA01 hK
    (fun l h _ => hAle l h)
  linarith [hb]

end Face

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Fine]

namespace Gallery

variable (G : Gallery E ι Fine) [Nonempty ι] [Nonempty Fine]

open Classical in
/-- **Lemma 5B.2 (hitting), full gallery.** `P[T(i) ≤ Q] ≤ M_i + 2Qζ`. -/
theorem gallery_hitting_profile (i : ι) (probe : List Bool → Sph E) (Q : ℕ) (M : ℝ)
    (hprof : ∀ y : ℕ → Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ∃ k < Q, G.reachG l (y k)), G.π i l) ≤ M) :
    ∑ v : ι → Fine, (∏ j, G.π j (v j)) * val (G.resp v) probe (hitInd G.reachG probe (v i)) Q []
      ≤ M + 2 * Q * G.ζ :=
  G.gallery_avg i probe Q (fun l => hitInd G.reachG probe l) _
    (fun γ => (G.face i γ).hitting_profile probe Q M hprof)

open Classical in
/-- **Lemma 5B.2 (recovery), full gallery.** `P[face i recovered at ε] ≤ M_i + 2Qζ + k_out·p(ε)`
— Prop 7.3 with the profile in place of `Q·μ₁`. -/
theorem gallery_recovery_profile (i : ι) (probe : List Bool → Sph E)
    (kout : ℕ) (out : List Bool → Fin kout → Sph E) (Q : ℕ) (M ε pε : ℝ)
    (hprof : ∀ y : ℕ → Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ∃ k < Q, G.reachG l (y k)), G.π i l) ≤ M)
    (hballcov : ∀ y : Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ pε) :
    ∑ v : ι → Fine, (∏ j, G.π j (v j)) * val (G.resp v) probe
      (fun h => if ∃ j, ‖(out h j).1 - G.g (v i)‖ ≤ ε then (1 : ℝ) else 0) Q []
      ≤ M + 2 * Q * G.ζ + kout * pε :=
  G.gallery_avg i probe Q (fun l h => if ∃ j, ‖(out h j).1 - G.g l‖ ≤ ε then (1 : ℝ) else 0) _
    (fun γ => (G.face i γ).recovery_profile probe kout out Q M ε pε hprof hballcov)

variable (probe : List Bool → Sph E) {Q kout : ℕ} (out : (Fin Q → Bool) → Fin kout → Sph E)

open Classical in
/-- Per-face recovery probability in profile form. -/
lemma Prec_le_profile (i : ι) (M ε p : ℝ)
    (hprof : ∀ y : ℕ → Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ∃ k < Q, G.reachG l (y k)), G.π i l) ≤ M)
    (hballcov : ∀ y : Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ p) :
    G.Prec probe out ε i ≤ M + 2 * Q * G.ζ + kout * p := by
  have h := G.gallery_recovery_profile i probe kout (outL out) Q M ε p hprof hballcov
  refine le_of_eq_of_le ?_ h
  unfold Prec
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [val_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [outL_ofFn]
  unfold wt recovered prior
  ring_nf

open Classical in
/-- **Thm 6.1(3), profile form.** `E[N_ε] ≤ ∑ᵢ M_i + 2nQζ + n·k_out·p(ε)`. -/
theorem EN_le_profile (M : ι → ℝ) (ε pε : ℝ)
    (hprof : ∀ i (y : ℕ → Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ∃ k < Q, G.reachG l (y k)), G.π i l) ≤ M i)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ pε) :
    G.EN probe out ε ≤ ∑ i, M i + Fintype.card ι * (2 * Q * G.ζ + kout * pε) := by
  rw [G.EN_eq_val]
  calc _ ≤ ∑ i : ι, (M i + 2 * Q * G.ζ + kout * pε) := Finset.sum_le_sum fun i _ =>
        G.gallery_recovery_profile i probe kout (outL out) Q (M i) ε pε (hprof i) (hballcov i)
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]; ring

open Classical in
/-- **Prop 5B.3 (profile form of Cor 6.2(i)).** If `P[N_ε ≥ m] ≥ ½` then
`∑ᵢ M_i + 2nQζ ≥ m/2 − n·k_out·p(ε)`, and `≥ 3m/8` when `n·k_out·p(ε) ≤ m/8`. For i.i.d. faces
(`M_i = M`) this reads `M ≥ 3m/(8n) − 2Qζ`, i.e. `Q ≥ K_π(3m/(8n))` at `ζ = 0`. -/
theorem prop5B3 (M : ι → ℝ) (ε pε : ℝ)
    (hprof : ∀ i (y : ℕ → Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ∃ k < Q, G.reachG l (y k)), G.π i l) ≤ M i)
    (hballcov : ∀ i (y : Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ pε)
    (m : ℝ) (hm : 0 ≤ m) (hPN : 1 / 2 ≤ G.PN probe out ε m) :
    m / 2 - Fintype.card ι * kout * pε ≤ ∑ i, M i + Fintype.card ι * (2 * Q * G.ζ) ∧
    (Fintype.card ι * kout * pε ≤ m / 8 →
      3 * m / 8 ≤ ∑ i, M i + Fintype.card ι * (2 * Q * G.ζ)) := by
  have hx := G.markov probe out ε m hm hPN
  have h3 := G.EN_le_profile probe out M ε pε hprof hballcov
  constructor
  · nlinarith
  · intro hs; nlinarith

open Classical in
/-- **First contact, profile form** (input to the note's Prop 3.3):
`P[some face hit within Q] ≤ ∑ᵢ (M_i + 2Qζ)`. -/
theorem first_contact_profile (Q : ℕ) (M : ι → ℝ)
    (hprof : ∀ i (y : ℕ → Sph E),
      (∑ l ∈ Finset.univ.filter (fun l => ∃ k < Q, G.reachG l (y k)), G.π i l) ≤ M i) :
    ∑ v, G.prior v * val (G.resp v) probe
      (fun h => if ∃ i, hitBy (G.reachG (v i)) probe h then (1 : ℝ) else 0) Q [] ≤
      ∑ i, M i + Fintype.card ι * (2 * Q * G.ζ) := by
  have hle : ∀ v, val (G.resp v) probe
      (fun h => if ∃ i, hitBy (G.reachG (v i)) probe h then (1 : ℝ) else 0) Q [] ≤
      ∑ i, val (G.resp v) probe (hitInd G.reachG probe (v i)) Q [] := by
    intro v
    rw [← val_sum]
    refine val_mono probe (G.resp_mem v) Q [] fun h _ => ?_
    split_ifs with hh
    · obtain ⟨i, hi⟩ := hh
      exact le_trans (by simp [hitInd, hi])
        (Finset.single_le_sum (f := fun i => hitInd G.reachG probe (v i) h)
          (fun j _ => by unfold hitInd; split_ifs <;> norm_num) (Finset.mem_univ i))
    · exact Finset.sum_nonneg fun j _ => by unfold hitInd; split_ifs <;> norm_num
  calc _ ≤ ∑ v, G.prior v * ∑ i, val (G.resp v) probe (hitInd G.reachG probe (v i)) Q [] :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hle v) (G.prior_nonneg v)
    _ = ∑ i, ∑ v, (∏ j, G.π j (v j)) * val (G.resp v) probe (hitInd G.reachG probe (v i)) Q [] := by
        simp only [Finset.mul_sum, prior]; exact Finset.sum_comm
    _ ≤ ∑ i : ι, (M i + 2 * Q * G.ζ) :=
        Finset.sum_le_sum fun i _ => G.gallery_hitting_profile i probe Q (M i) (hprof i)
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Gallery

end OracleBounds.GeneralPrior
