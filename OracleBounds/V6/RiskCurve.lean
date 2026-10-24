import OracleBounds.V6.Plant
import OracleBounds.V6.InfoProcess

/-!
# Inequality (4) and Corollary 8.1 at plant level

End-to-end assembly in the planted model of `OracleBounds.V6.Plant`:

* the fine-scale list decoder (v6/v7 Thm 6.1 (4) proof): from the transcript, list the fine indices
  of cap `Wᵢ` within `α/2` of some output; it has at most `k_out` entries (α-separation) and contains
  `Vᵢ` whenever face `i` is recovered at precision `ε < α/2`;
* per cap assignment `W`: list-Fano for each face and `Σᵢ I(Vᵢ; Y) ≤ I(V; Y) ≤ log 2 · E[C_Q]`
  (Thm 5.1 in the process model);
* averaging over the plant with the staircase bound gives (4) (`eq4_plant`), and then Cor 8.1's second
  branch (`cor81_branch2_plant`).

Information inputs `Info.list_fano` and `Info.mutualInfo_superadditive` are proved (no `sorry`).
Assumed as hypotheses: the spread-family coverage/separation, α-separation of the fine templates in
each cap, and the local packing size `log N₁ ≥ 6B/n + 4` (what N1 Lemma 2.6(b) supplies at the scale
`ε*` of `Info.cor81_epsStar`). Band-null kernel (`ζ = 0`), `β* = log 2`.
-/

namespace OracleBounds.V6

open Finset Function Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Cap Fine : Type*} [Fintype ι] [Nonempty ι] [Fintype Cap] [Fintype Fine] [Nonempty Fine]

namespace PlantData

variable (P : PlantData E Cap Fine)

/-! ### The list decoder -/

/-- Fine indices of cap `c` within `α/2` of some output point. -/
noncomputable def decList {k : ℕ} (α : ℝ) (c : Cap) (y : Fin k → Sph E) : Finset Fine :=
  Finset.univ.filter (fun l => ∃ j, ‖(y j).1 - P.g c l‖ < α / 2)

lemma decList_card {k : ℕ} (α : ℝ) (hsepF : ∀ c l l', l ≠ l' → α ≤ ‖P.g c l - P.g c l'‖)
    (c : Cap) (y : Fin k → Sph E) : (P.decList α c y).card ≤ k := by
  have hsub : P.decList α c y = Finset.univ.biUnion (fun j => Finset.univ.filter
      (fun l => ‖(y j).1 - P.g c l‖ < α / 2)) := by
    ext l; simp [decList]
  rw [hsub]
  calc _ ≤ ∑ j, (Finset.univ.filter (fun l => ‖(y j).1 - P.g c l‖ < α / 2)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin k, 1 := by
        refine Finset.sum_le_sum fun j _ => Finset.card_le_one.2 fun l hl l' hl' => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl hl'
        by_contra hne
        have := hsepF c l l' hne
        have htri : ‖P.g c l - P.g c l'‖ ≤ ‖(y j).1 - P.g c l‖ + ‖(y j).1 - P.g c l'‖ := by
          calc ‖P.g c l - P.g c l'‖ = ‖((y j).1 - P.g c l') - ((y j).1 - P.g c l)‖ := by abel_nf
            _ ≤ _ := by rw [add_comm]; exact norm_sub_le _ _
        linarith
    _ = k := by simp

lemma mem_decList {k : ℕ} {α ε : ℝ} (hε : ε < α / 2) (c : Cap) (y : Fin k → Sph E) (l : Fine)
    (j : Fin k) (hj : ‖(y j).1 - P.g c l‖ ≤ ε) : l ∈ P.decList α c y := by
  simp only [decList, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨j, lt_of_le_of_lt hj hε⟩

/-! ### Joint pmfs for a fixed cap assignment -/

variable (probe : List Bool → Sph E) (Q : ℕ)

/-- Face `i`'s joint pmf of `(Vᵢ, transcript)` given caps `W` (uniform fine indices). -/
noncomputable def qFace (W : ι → Cap) (i : ι) : Fine × (Fin Q → Bool) → ℝ :=
  fun lb => ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = lb.1),
    (1 / (Fintype.card (ι → Fine) : ℝ)) * pathProb (P.resp W v) probe Q [] lb.2

lemma resp_mem (W : ι → Cap) (v : ι → Fine) (x : Sph E) : 0 ≤ P.resp W v x ∧ P.resp W v x ≤ 1 :=
  P.hκ _

lemma card_fiber (i : ι) (l : Fine) :
    ((Finset.univ.filter (fun v : ι → Fine => v i = l)).card : ℝ) =
      (Fintype.card (ι → Fine) : ℝ) / Fintype.card Fine := by
  have h1 := Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset Fine) i
    (Finset.mem_univ l)
  rw [Fintype.piFinset_univ] at h1
  rw [h1, Fintype.card_fun, Finset.card_univ]
  have hN : 0 < Fintype.card Fine := Fintype.card_pos_iff.2 ⟨l⟩
  have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
  rw [show Fintype.card ι = (Fintype.card ι - 1) + 1 by omega, pow_succ]
  push_cast
  field_simp

/-- **List-Fano for face `i`, caps `W` fixed.** -/
theorem face_fano (W : ι → Cap) (i : ι) {k : ℕ} (out : List Bool → Fin k → Sph E) (α : ℝ)
    (hsepF : ∀ c l l', l ≠ l' → α ≤ ‖P.g c l - P.g c l'‖) (hk : 0 < k) (hkN : k < Fintype.card Fine) :
    let Pi := (1 / (Fintype.card (ι → Fine) : ℝ)) * ∑ v : ι → Fine, val (P.resp W v) probe
      (fun h => if v i ∈ P.decList α (W i) (out h) then 1 else 0) Q []
    Pi * Real.log (Fintype.card Fine / k) - Real.binEntropy Pi ≤ Info.mutualInfo (P.qFace probe Q W i) := by
  intro Pi
  set c : ℝ := ((Fintype.card (ι → Fine) : ℕ) : ℝ)
  have hc : 0 < c := by simp only [c]; exact_mod_cast Fintype.card_pos
  have hq : ∀ lb, 0 ≤ P.qFace probe Q W i lb := fun lb => Finset.sum_nonneg fun v _ =>
    mul_nonneg (by positivity) (pathProb_nonneg probe (P.resp_mem W v) Q [] lb.2)
  -- total mass and marginal
  have hmarg : ∀ l, Info.marg₁ (P.qFace probe Q W i) l = 1 / Fintype.card Fine := by
    intro l
    simp only [Info.marg₁, qFace]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, pathProb_sum probe (P.resp_mem W _), mul_one, Finset.sum_const,
      nsmul_eq_mul, card_fiber]
    have h1 : ((Fintype.card (ι → Fine) : ℕ) : ℝ) ≠ 0 := hc.ne'
    have h2 : ((Fintype.card Fine : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  have hsum : ∑ lb, P.qFace probe Q W i lb = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [show ∀ l, ∑ b, P.qFace probe Q W i (l, b) = Info.marg₁ (P.qFace probe Q W i) l from
      fun l => rfl, hmarg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (0 : ℝ) < Fintype.card Fine := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hkN)
    field_simp
  have hF := Info.list_fano (P.qFace probe Q W i) hq hsum hmarg
    (fun b => P.decList α (W i) (out (List.ofFn b))) k hk hkN
    (fun b => P.decList_card α hsepF (W i) (out (List.ofFn b)))
  simp only at hF
  -- identify the list-Fano probability with `Pi`
  have hP : ∑ lb : Fine × (Fin Q → Bool),
      (if lb.1 ∈ P.decList α (W i) (out (List.ofFn lb.2)) then P.qFace probe Q W i lb else 0) = Pi := by
    simp only [Pi, qFace, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    have inner : ∀ b : Fin Q → Bool, ∑ l : Fine,
        (if l ∈ P.decList α (W i) (out (List.ofFn b)) then
          ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = l),
            1 / ((Fintype.card (ι → Fine) : ℕ) : ℝ) * pathProb (P.resp W v) probe Q [] b else 0) =
        ∑ v : ι → Fine, 1 / ((Fintype.card (ι → Fine) : ℕ) : ℝ) * (pathProb (P.resp W v) probe Q [] b *
          (if v i ∈ P.decList α (W i) (out (List.ofFn b)) then 1 else 0)) := by
      intro b
      rw [← Finset.sum_fiberwise (Finset.univ : Finset (ι → Fine)) (fun v => v i)]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs with hl
      · refine Finset.sum_congr rfl fun v hv => ?_
        simp only [Finset.mem_filter] at hv
        rw [if_pos (hv.2 ▸ hl)]; ring
      · refine (Finset.sum_eq_zero fun v hv => ?_).symm
        simp only [Finset.mem_filter] at hv
        rw [if_neg (hv.2 ▸ hl)]; ring
    simp only [inner]
    rw [Finset.mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [val_eq_sum, Finset.mul_sum]
    simp only [List.nil_append]
    congr
  rw [hP] at hF
  exact hF

/-- **Thm 5.1 + superadditivity for caps `W` fixed** (`ζ = 0`):
`Σᵢ I(Vᵢ; Y) ≤ log 2 · E_V[C_Q]`. -/
theorem info_per_caps (hζ : P.ζ = 0) (W : ι → Cap) :
    ∑ i, Info.mutualInfo (P.qFace probe Q W i) ≤
      Real.log 2 * ((1 / (Fintype.card (ι → Fine) : ℝ)) * ∑ v : ι → Fine, val (P.resp W v) probe
        (fun h => ∑ k ∈ Finset.range Q, if ∃ i, P.reach (W i) (probe (h.take k)) then 1 else 0) Q []) := by
  set c : ℝ := ((Fintype.card (ι → Fine) : ℕ) : ℝ)
  have hc : 0 < c := by simp only [c]; exact_mod_cast Fintype.card_pos
  have hsup := Info.mutualInfo_superadditive (fun v b => pathProb (P.resp W v) probe Q [] b)
    (fun v b => pathProb_nonneg probe (P.resp_mem W v) Q [] b)
    (fun v => pathProb_sum probe (P.resp_mem W v) Q [])
  have hν : 0 ≤ P.ν₀ ∧ P.ν₀ ≤ 1 := by
    have h := P.hband P.thr le_rfl; rw [hζ, abs_nonpos_iff, sub_eq_zero] at h
    rw [← h]; exact P.hκ _
  have hquiet : ∀ (v : ι → Fine) (x : Sph E), (¬ ∃ i, P.reach (W i) x) → P.resp W v x = P.ν₀ := by
    intro v x hx
    push Not at hx
    have hs : P.score W v x.1 ≤ P.thr := by
      refine Finset.sup'_le _ _ fun j _ => ?_
      by_contra hlt
      push Not at hlt
      exact hx j (reach_of_match x.2 (P.hg (W j) (v j)) hlt)
    have h := P.hband _ hs
    rw [hζ, abs_nonpos_iff, sub_eq_zero] at h
    exact h
  have h51 := thm51_log_two (fun _ : ι → Fine => 1 / c) (fun _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; exact mul_one_div_cancel hc.ne')
    (fun v => P.resp W v)
    (fun v x => P.resp_mem W v x) probe (fun x => ¬ ∃ i, P.reach (W i) x) (fun _ => P.ν₀)
    (fun _ => hν) (fun v x hx => hquiet v x hx) Q
  refine hsup.trans (h51.trans (le_of_eq ?_))
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  congr 1
  funext h
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [not_not]

lemma qFace_nonneg (W : ι → Cap) (i : ι) (lb : Fine × (Fin Q → Bool)) : 0 ≤ P.qFace probe Q W i lb :=
  Finset.sum_nonneg fun v _ =>
    mul_nonneg (by positivity) (pathProb_nonneg probe (P.resp_mem W v) Q [] lb.2)

lemma qFace_marg (W : ι → Cap) (i : ι) (l : Fine) :
    Info.marg₁ (P.qFace probe Q W i) l = 1 / Fintype.card Fine := by
  have hc : (0 : ℝ) < ((Fintype.card (ι → Fine) : ℕ) : ℝ) := by exact_mod_cast Fintype.card_pos
  simp only [Info.marg₁, qFace]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, pathProb_sum probe (P.resp_mem W _), mul_one, Finset.sum_const,
    nsmul_eq_mul, card_fiber]
  have h1 : ((Fintype.card (ι → Fine) : ℕ) : ℝ) ≠ 0 := hc.ne'
  have h2 : ((Fintype.card Fine : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma qFace_sum (W : ι → Cap) (i : ι) : ∑ lb, P.qFace probe Q W i lb = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [show ∀ l, ∑ b, P.qFace probe Q W i (l, b) = Info.marg₁ (P.qFace probe Q W i) l from
    fun l => rfl, P.qFace_marg probe Q W i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : ((Fintype.card Fine : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Number of faces recovered at precision `ε` on transcript `h` (gallery `(W, v)`). -/
noncomputable def Ncount {k : ℕ} (out : List Bool → Fin k → Sph E) (ε : ℝ) (W : ι → Cap)
    (v : ι → Fine) (h : List Bool) : ℝ :=
  ∑ i, if ∃ j, ‖(out h j).1 - P.g (W i) (v i)‖ ≤ ε then 1 else 0

omit [Nonempty Fine] in
lemma injs_card_pos (hnM : Fintype.card ι ≤ Fintype.card Cap) :
    (0 : ℝ) < (injs : Finset (ι → Cap)).card := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hnM
  have : (f : ι → Cap) ∈ (injs : Finset (ι → Cap)) := by
    simp only [injs, Finset.mem_filter, Finset.mem_univ, true_and]; exact f.injective
  exact_mod_cast Finset.card_pos.2 ⟨_, this⟩

/-- **Inequality (4), plant level** (band-null, `β* = log 2`, no slack): with
`x = E_plant[N_ε(Q)]`, `Λ′ = log(N₁/k_out)`, and `S_n(Q) = Σ_{j ≤ Q} min{1, n(2μ₁ + 2ζ)j}`:
`x·Λ′ ≤ log 2 · S_n(Q) + n·h(min{x/n, ½})`. Inputs: `Info.list_fano`, `Info.mutualInfo_superadditive`. -/
theorem eq4_plant (hn2 : 2 ≤ Fintype.card ι) (hnM : 2 * Fintype.card ι ≤ Fintype.card Cap)
    {k : ℕ} (out : List Bool → Fin k → Sph E) (hk0 : 0 < k) (hkN : k < Fintype.card Fine)
    (ε : ℝ) (hε0 : 0 < ε) (hsepF : ∀ c l l', l ≠ l' → 3 * ε ≤ ‖P.g c l - P.g c l'‖)
    (hζ : P.ζ = 0) (μ : ℝ) (hμ : 0 ≤ μ)
    (hcov : ∀ x : Sph E, ((Finset.univ.filter fun c => P.thr - P.r₀ < inner ℝ x.1 (P.z c)).card : ℝ)
      ≤ μ * Fintype.card Cap) :
    let x := (1 / (((injs : Finset (ι → Cap)).card : ℝ) * Fintype.card (ι → Fine))) *
      ∑ W ∈ injs, ∑ v : ι → Fine, val (P.resp W v) probe (P.Ncount out ε W v) Q []
    x * Real.log (Fintype.card Fine / k) ≤
      Real.log 2 * ∑ j ∈ Finset.range Q,
        min 1 (Fintype.card ι * (2 * μ * (j + 1) + 2 * (j + 1) * P.ζ))
      + Fintype.card ι * Real.binEntropy (min (x / Fintype.card ι) (1 / 2)) := by
  intro x
  set a : ℝ := ((injs : Finset (ι → Cap)).card : ℝ) with ha_def
  set c : ℝ := ((Fintype.card (ι → Fine) : ℕ) : ℝ) with hc_def
  have ha : 0 < a := injs_card_pos (ι := ι) (Cap := Cap) (by omega)
  have hc : 0 < c := by simp only [c]; exact_mod_cast Fintype.card_pos
  set α : ℝ := 3 * ε
  set Pi : (ι → Cap) → ι → ℝ := fun W i => (1 / c) * ∑ v : ι → Fine, val (P.resp W v) probe
    (fun h => if v i ∈ P.decList α (W i) (out h) then 1 else 0) Q [] with hPi
  set Pbar : ι → ℝ := fun i => ∑ W ∈ (injs : Finset (ι → Cap)), (1 / a) * Pi W i
  set Ibar : ι → ℝ := fun i => ∑ W ∈ (injs : Finset (ι → Cap)), (1 / a) * Info.mutualInfo (P.qFace probe Q W i)
  set S : ℝ := ∑ j ∈ Finset.range Q, min 1 (Fintype.card ι * (2 * μ * (j + 1) + 2 * (j + 1) * P.ζ))
  have hval01 : ∀ (W : ι → Cap) (v : ι → Fine) (F : List Bool → ℝ), (∀ h, 0 ≤ F h ∧ F h ≤ 1) →
      0 ≤ val (P.resp W v) probe F Q [] ∧ val (P.resp W v) probe F Q [] ≤ 1 :=
    fun W v F hF => val_mem_Icc probe (P.resp_mem W v) hF Q []
  have hind : ∀ (p : Prop) [Decidable p], 0 ≤ (if p then (1 : ℝ) else 0) ∧ (if p then (1 : ℝ) else 0) ≤ 1 := by
    intro p _; split_ifs <;> norm_num
  have hPi01 : ∀ W i, 0 ≤ Pi W i ∧ Pi W i ≤ 1 := by
    intro W i
    have hs0 : 0 ≤ ∑ v : ι → Fine, val (P.resp W v) probe
        (fun h => if v i ∈ P.decList α (W i) (out h) then 1 else 0) Q [] :=
      Finset.sum_nonneg fun v _ => (hval01 W v _ fun h => hind _).1
    have hs1 : ∑ v : ι → Fine, val (P.resp W v) probe
        (fun h => if v i ∈ P.decList α (W i) (out h) then 1 else 0) Q [] ≤ c := by
      calc _ ≤ ∑ _v : ι → Fine, (1 : ℝ) := Finset.sum_le_sum fun v _ => (hval01 W v _ fun h => hind _).2
        _ = c := by simp [c]
    constructor
    · simp only [hPi]; positivity
    · simp only [hPi]; rw [one_div_mul_eq_div, div_le_one hc]; exact hs1
  have hw1 : ∑ W ∈ (injs : Finset (ι → Cap)), (1 / a) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]; exact mul_one_div_cancel ha.ne'
  have hP : ∀ i, 0 ≤ Pbar i ∧ Pbar i ≤ 1 := by
    intro i
    constructor
    · exact Finset.sum_nonneg fun W _ => mul_nonneg (by positivity) (hPi01 W i).1
    · calc Pbar i ≤ ∑ W ∈ (injs : Finset (ι → Cap)), (1 / a) :=
            Finset.sum_le_sum fun W _ => by
              have h1 := (hPi01 W i).2
              have h0 : 0 ≤ 1 / a := (by positivity)
              nlinarith
        _ = 1 := hw1
  have hFano : ∀ i, Pbar i * Real.log (Fintype.card Fine / k) - Real.binEntropy (Pbar i) ≤ Ibar i := by
    intro i
    exact Info.fano_average injs (fun _ => 1 / a) (fun W => Pi W i)
      (fun W => Info.mutualInfo (P.qFace probe Q W i)) _ (fun _ _ => by positivity) hw1
      (fun W _ => hPi01 W i) (fun W _ => P.face_fano probe Q W i out α (by simpa [α] using hsepF) hk0 hkN)
  have hI0 : ∀ i, 0 ≤ Ibar i := fun i => Finset.sum_nonneg fun W _ =>
    mul_nonneg (by positivity) (Info.mutualInfo_nonneg _ (P.qFace_nonneg probe Q W i) (P.qFace_sum probe Q W i))
  have hInfo : ∑ i, Ibar i ≤ Real.log 2 * S := by
    simp only [Ibar]
    rw [Finset.sum_comm]
    calc ∑ W ∈ (injs : Finset (ι → Cap)), ∑ i, (1 / a) * Info.mutualInfo (P.qFace probe Q W i)
        ≤ ∑ W ∈ (injs : Finset (ι → Cap)), (1 / a) * (Real.log 2 * ((1 / c) * ∑ v : ι → Fine,
            val (P.resp W v) probe (fun h => ∑ j ∈ Finset.range Q,
              if ∃ i, P.reach (W i) (probe (h.take j)) then 1 else 0) Q [])) := by
          refine Finset.sum_le_sum fun W _ => ?_
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (P.info_per_caps probe Q hζ W) (by positivity)
      _ = Real.log 2 * ((1 / a) * (1 / c) * ∑ v : ι → Fine, ∑ W ∈ (injs : Finset (ι → Cap)),
            val (P.resp W v) probe (fun h => ∑ j ∈ Finset.range Q,
              if ∃ i, P.reach (W i) (probe (h.take j)) then 1 else 0) Q []) := by
          rw [Finset.sum_comm (s := (Finset.univ : Finset (ι → Fine)))]
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun W _ => Finset.sum_congr rfl fun v _ => ?_
          ring
      _ ≤ Real.log 2 * ((1 / a) * (1 / c) * ∑ _v : ι → Fine, a * S) := by
          apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum fun v _ => by
            have := P.staircase_plant hn2 hnM probe μ hμ hcov Q v
            simpa [S, mul_comm] using this
      _ = Real.log 2 * S := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
          rfl
  have hx0 : 0 ≤ x := by
    apply mul_nonneg (by positivity)
    refine Finset.sum_nonneg fun W _ => Finset.sum_nonneg fun v _ => ?_
    have := val_mono probe (P.resp_mem W v) (F := fun _ => (0 : ℝ)) (G := P.Ncount out ε W v) Q []
      (fun h _ => Finset.sum_nonneg fun i _ => (hind _).1)
    rwa [val_const] at this
  have hx : x ≤ ∑ i, Pbar i := by
    have hpath : ∀ (W : ι → Cap) (v : ι → Fine), val (P.resp W v) probe (P.Ncount out ε W v) Q [] ≤
        ∑ i, val (P.resp W v) probe (fun h => if v i ∈ P.decList α (W i) (out h) then 1 else 0) Q [] := by
      intro W v
      rw [← val_sum]
      apply val_mono probe (P.resp_mem W v)
      intro h _
      unfold Ncount
      refine Finset.sum_le_sum fun i _ => ?_
      split_ifs with h1 h2
      · exact le_rfl
      · obtain ⟨j, hj⟩ := h1
        exact absurd (P.mem_decList (by simp only [α]; linarith) (W i) (out h) (v i) j hj) h2
      · norm_num
      · exact le_rfl
    have hsumP : ∑ i, Pbar i = (1 / (a * c)) * ∑ W ∈ (injs : Finset (ι → Cap)), ∑ v : ι → Fine,
        ∑ i, val (P.resp W v) probe (fun h => if v i ∈ P.decList α (W i) (out h) then 1 else 0) Q [] := by
      simp only [Pbar, hPi, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun W _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [hsumP]
    simp only [x]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun W _ => Finset.sum_le_sum fun v _ => hpath W v)
      (by positivity)
  have hΛ : 0 ≤ Real.log (Fintype.card Fine / k) := Real.log_nonneg (by
    rw [le_div_iff₀ (by exact_mod_cast hk0), one_mul]; exact_mod_cast hkN.le)
  have key := Info.thm61_eq4 (Real.log (Fintype.card Fine / k)) (Real.log 2 * S) x 0 Pbar Ibar hΛ
    hP hFano hInfo hI0 hx0 hx le_rfl
  linarith

/-- **Corollary 8.1, second branch (exponential), plant level.** Band-null kernel, `β* = log 2`,
condition (1), fine templates `3ε`-separated in each cap, `k_out = k + 1` outputs. Write
`B = log 2 · S_n(Q)`. If the local packing is large enough, `log N₁ ≥ 6B/n + 4` (N1 Lemma 2.6(b) at the
scale `ε*` of `Info.cor81_epsStar`), and `k_out ≤ exp(2 + 3B/n)` (v7's output-size hypothesis), then for
every attacker the plant-average risk exceeds `ε/2`:
`E_plant[(1/n) Σᵢ minⱼ ‖ĝⱼ − g⁽ⁱ⁾‖] > ε/2`. -/
theorem cor81_branch2_plant (hn2 : 2 ≤ Fintype.card ι) (hnM : 2 * Fintype.card ι ≤ Fintype.card Cap)
    {k : ℕ} (out : List Bool → Fin (k + 1) → Sph E)
    (ε : ℝ) (hε0 : 0 < ε) (hsepF : ∀ c l l', l ≠ l' → 3 * ε ≤ ‖P.g c l - P.g c l'‖)
    (hζ : P.ζ = 0) (μ : ℝ) (hμ : 0 ≤ μ)
    (hcov : ∀ x : Sph E, ((Finset.univ.filter fun c => P.thr - P.r₀ < inner ℝ x.1 (P.z c)).card : ℝ)
      ≤ μ * Fintype.card Cap)
    (hN : 6 * (Real.log 2 * ∑ j ∈ Finset.range Q,
        min 1 (Fintype.card ι * (2 * μ * (j + 1) + 2 * (j + 1) * P.ζ))) / Fintype.card ι + 4
        ≤ Real.log (Fintype.card Fine))
    (hk : ((k + 1 : ℕ) : ℝ) ≤ Real.exp (2 + 3 * (Real.log 2 * ∑ j ∈ Finset.range Q,
        min 1 (Fintype.card ι * (2 * μ * (j + 1) + 2 * (j + 1) * P.ζ))) / Fintype.card ι)) :
    ε / 2 < (1 / (((injs : Finset (ι → Cap)).card : ℝ) * Fintype.card (ι → Fine))) *
      ∑ W ∈ injs, ∑ v : ι → Fine, val (P.resp W v) probe (fun h =>
        (1 / Fintype.card ι : ℝ) * ∑ i, Finset.univ.inf' Finset.univ_nonempty
          (fun j => ‖(out h j).1 - P.g (W i) (v i)‖)) Q [] := by
  set S : ℝ := ∑ j ∈ Finset.range Q, min 1 (Fintype.card ι * (2 * μ * (j + 1) + 2 * (j + 1) * P.ζ))
  set B : ℝ := Real.log 2 * S
  set n : ℝ := ((Fintype.card ι : ℕ) : ℝ)
  have hn : 0 < n := by simp only [n]; exact_mod_cast Fintype.card_pos
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => le_min zero_le_one
    (mul_nonneg (Nat.cast_nonneg _) (by rw [hζ]; simp; positivity))
  have hB : 0 ≤ B := mul_nonneg (Real.log_nonneg (by norm_num)) hS
  -- k_out < N₁ and Λ′ ≥ 3B/n + 2
  have hk0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hlogk : Real.log ((k + 1 : ℕ) : ℝ) ≤ 2 + 3 * B / n := by
    rw [Real.log_le_iff_le_exp hk0]; exact hk
  have hBn : 0 ≤ B / n := div_nonneg hB hn.le
  have hkN : k + 1 < Fintype.card Fine := by
    have h1 : Real.log ((k + 1 : ℕ) : ℝ) < Real.log (Fintype.card Fine) := by
      have : 3 * B / n = 3 * (B / n) := by ring
      have : 6 * B / n = 6 * (B / n) := by ring
      linarith
    have hNpos : (0 : ℝ) < Fintype.card Fine := by exact_mod_cast Fintype.card_pos
    exact_mod_cast (Real.log_lt_log_iff hk0 hNpos).1 h1
  have hΛ : 3 * B / n + 2 ≤ Real.log (Fintype.card Fine / ((k + 1 : ℕ) : ℝ)) := by
    rw [Real.log_div (by exact_mod_cast Fintype.card_ne_zero) hk0.ne']
    have : 3 * B / n = 3 * (B / n) := by ring
    have : 6 * B / n = 6 * (B / n) := by ring
    linarith
  -- (4) and the contradiction step
  have h4 := P.eq4_plant probe Q hn2 hnM out (Nat.succ_pos k) hkN ε hε0 hsepF hζ μ hμ hcov
  simp only at h4
  set x := (1 / (((injs : Finset (ι → Cap)).card : ℝ) * Fintype.card (ι → Fine))) *
      ∑ W ∈ injs, ∑ v : ι → Fine, val (P.resp W v) probe (P.Ncount out ε W v) Q [] with hx
  have hxlt : x < n / 2 := Info.cor81_v7_count n B _ x hn hB hΛ h4
  -- eq. (5) pathwise, then averaged
  have hpath : ∀ (W : ι → Cap) (v : ι → Fine),
      ε - ε / n * val (P.resp W v) probe (P.Ncount out ε W v) Q [] ≤
      val (P.resp W v) probe (fun h => (1 / Fintype.card ι : ℝ) * ∑ i, Finset.univ.inf'
        Finset.univ_nonempty (fun j => ‖(out h j).1 - P.g (W i) (v i)‖)) Q [] := by
    intro W v
    have e := val_affine (P.resp W v) probe ε (-(ε / n)) (P.Ncount out ε W v) Q []
    have hm := val_mono probe (P.resp_mem W v) (F := fun h => ε + -(ε / n) * P.Ncount out ε W v h)
      (G := fun h => (1 / Fintype.card ι : ℝ) * ∑ i, Finset.univ.inf'
        Finset.univ_nonempty (fun j => ‖(out h j).1 - P.g (W i) (v i)‖)) Q [] (fun h _ => by
      have h5 := Info.eq5_pathwise (fun i => Finset.univ.inf' Finset.univ_nonempty
        (fun j => ‖(out h j).1 - P.g (W i) (v i)‖)) (fun i => by
          simp only [Finset.le_inf'_iff]; intros; positivity) ε
      have hcnt : ((Finset.univ.filter fun i => Finset.univ.inf' Finset.univ_nonempty
          (fun j => ‖(out h j).1 - P.g (W i) (v i)‖) ≤ ε).card : ℝ) = P.Ncount out ε W v h := by
        unfold Ncount
        rw [Finset.natCast_card_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.inf'_le_iff, Finset.mem_univ, true_and]
      rw [hcnt] at h5
      have e1 : ε * (1 - P.Ncount out ε W v h / n) = ε + -(ε / n) * P.Ncount out ε W v h := by
        field_simp; ring
      have e2 : (∑ i, Finset.univ.inf' Finset.univ_nonempty
          (fun j => ‖(out h j).1 - P.g (W i) (v i)‖)) / n =
          (1 / Fintype.card ι : ℝ) * ∑ i, Finset.univ.inf' Finset.univ_nonempty
          (fun j => ‖(out h j).1 - P.g (W i) (v i)‖) := by ring
      simp only [n] at e1 e2
      linarith)
    rw [e] at hm
    linarith
  set a : ℝ := ((injs : Finset (ι → Cap)).card : ℝ)
  set c : ℝ := ((Fintype.card (ι → Fine) : ℕ) : ℝ)
  have ha : 0 < a := injs_card_pos (ι := ι) (Cap := Cap) (by omega)
  have hc : 0 < c := by simp only [c]; exact_mod_cast Fintype.card_pos
  have havg : ε - ε / n * x ≤ (1 / (a * c)) * ∑ W ∈ injs, ∑ v : ι → Fine,
      val (P.resp W v) probe (fun h => (1 / Fintype.card ι : ℝ) * ∑ i, Finset.univ.inf'
        Finset.univ_nonempty (fun j => ‖(out h j).1 - P.g (W i) (v i)‖)) Q [] := by
    calc ε - ε / n * x = (1 / (a * c)) * ∑ W ∈ (injs : Finset (ι → Cap)), ∑ v : ι → Fine,
          (ε - ε / n * val (P.resp W v) probe (P.Ncount out ε W v) Q []) := by
          simp only [hx, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
          field_simp
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun W _ => Finset.sum_le_sum fun v _ => hpath W v) (by positivity)
  have : ε / 2 < ε - ε / n * x := by
    have : ε / n * x < ε / n * (n / 2) := mul_lt_mul_of_pos_left hxlt (by positivity)
    have e : ε / n * (n / 2) = ε / 2 := by field_simp
    linarith
  linarith

end PlantData

end OracleBounds.V6
