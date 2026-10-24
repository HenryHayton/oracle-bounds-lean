import OracleBounds.Attacks.RandomSearch

/-!
# Random search: the Chernoff branch of `P_nf`

**Statements reviewed and signed off by the administrator (2026-10-14)**: `lemma9`, `lemma10`, `Pnf_le_chernoff` and `thm63_chernoff` transcribe briefs/attacks/random-search-general-prior.md §6.6–6.7 (Lemmas 9–10, Theorem 6.3(c′) second branch) with the paper's constants.

Source: `briefs/attacks/random-search-general-prior.md` §6.6 (Lemmas 9, 10) and §6.7 (Theorem 6.3(c′),
second term of the `min`). Builds on `RandomSearch.lean` (`EK`, `Fof`, `stepA`, `lemma5`,
`lemma6_Delta`).

* `phi p M r j` — the tail `P[Σ_{i=j}^{M−1} G_i > r]` for independent `G_i ∼ Geom(p_i)` on
  `{1,2,…}`, *defined* by the recursion of the paper's proof (`φ(0,j) = 1{j<M}`, `φ(r,j) = 0` for
  `j ≥ M`, `φ(r+1,j) = p_j φ(r,j+1) + (1−p_j) φ(r,j)`); `phi_antitone`, `phi_succ_le`.
* `lemma9` (generic): for any launch counter `L` on search histories which increases by `0` or `1`
  per round and whose one-round increase probability in stage `j < M` is `≥ p_j`,
  `E[1{L < M after K rounds}] ≤ φ(K, 0)` (finite-sum supermartingale argument).
* `phi_le_mgf` (Chernoff via the recursion): `φ(r,j) ≤ e^{−θr} ∏_{i=j}^{M−1} e^θ p_i/(p_i−θ)` for
  `0 ≤ θ < p_i ≤ 1` (the factor bounds the geometric MGF `p e^θ/(1−(1−p)e^θ)`).
* `lemma10`: `φ(K,0) ≤ exp(−p_* μ (κ − 1 − log κ))` for `0 < p_* ≤ p_j ≤ 1`, `μ = Σ 1/p_j`,
  `κ > 1`, `K ≥ M + κμ` — the paper's constant exactly.
* `lemma9_attack`, `Pnf_le_chernoff` — the attack: `P_nf ≤ D/δ + exp(−p_{M−1} μ (κ−1−log κ))`.
* `thm63_chernoff` — `thm63_markov`'s `E[N_ε]` bound with this branch in place of the Markov one.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.Attacks.RandomSearch

open Finset OracleBounds.V6 OracleBounds.GeneralPrior OracleBounds.Attacks

/-! ### The tail function `φ` -/

/-- `φ(r, j) = P[Σ_{i=j}^{M−1} G_i > r]`, `G_i ∼ Geom(p_i)` independent, via its recursion. -/
noncomputable def phi (p : ℕ → ℝ) (M : ℕ) : ℕ → ℕ → ℝ
  | 0, j => if j < M then 1 else 0
  | r + 1, j => if j < M then p j * phi p M r (j + 1) + (1 - p j) * phi p M r j else 0

section Phi

variable (p : ℕ → ℝ) (M : ℕ)

lemma phi_zero (j : ℕ) : phi p M 0 j = ind (j < M) := by
  unfold ind; simp only [phi]; split_ifs <;> rfl

lemma phi_succ (r j : ℕ) : phi p M (r + 1) j =
    if j < M then p j * phi p M r (j + 1) + (1 - p j) * phi p M r j else 0 := rfl

lemma phi_ge (r j : ℕ) (hj : M ≤ j) : phi p M r j = 0 := by
  cases r with
  | zero => simp [phi, not_lt.2 hj]
  | succ r => simp [phi_succ, not_lt.2 hj]

variable {p M}

lemma phi_nonneg (hp0 : ∀ j < M, 0 ≤ p j) (hp1 : ∀ j < M, p j ≤ 1) :
    ∀ r j, 0 ≤ phi p M r j := by
  intro r
  induction r with
  | zero => intro j; rw [phi_zero]; exact ind_nonneg _
  | succ r ih =>
    intro j; rw [phi_succ]; split_ifs with h
    · exact add_nonneg (mul_nonneg (hp0 j h) (ih _)) (mul_nonneg (by linarith [hp1 j h]) (ih _))
    · exact le_rfl

/-- `φ(r, j+1) ≤ φ(r, j)` and `φ(r+1, j) ≤ φ(r, j)`, jointly by induction on `r`. -/
lemma phi_mono_both (hp0 : ∀ j < M, 0 ≤ p j) (hp1 : ∀ j < M, p j ≤ 1) :
    ∀ r, (∀ j, phi p M r (j + 1) ≤ phi p M r j) ∧ (∀ j, phi p M (r + 1) j ≤ phi p M r j) := by
  have hnn := phi_nonneg hp0 hp1
  intro r
  induction r with
  | zero =>
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [phi_zero, phi_zero]; exact ind_mono fun h => by omega
    · rw [phi_succ, phi_zero, phi_zero]
      split_ifs with h
      · rw [ind_pos h]; have := ind_le_one (j + 1 < M)
        nlinarith [hp0 j h, hp1 j h]
      · exact ind_nonneg _
  | succ r ih =>
    obtain ⟨ha, hb⟩ := ih
    have ha' : ∀ j, phi p M (r + 1) (j + 1) ≤ phi p M (r + 1) j := by
      intro j
      by_cases hj1 : j + 1 < M
      · have h1 := hb (j + 1)
        have hj : j < M := by omega
        rw [phi_succ p M r j, if_pos hj]
        have := ha j
        nlinarith [hp0 j hj, hp1 j hj]
      · rw [phi_ge p M _ _ (by omega)]; exact hnn _ _
    refine ⟨ha', fun j => ?_⟩
    rw [phi_succ p M (r + 1) j]
    split_ifs with hj
    · have := ha' j
      nlinarith [hp0 j hj, hp1 j hj]
    · exact hnn _ _

lemma phi_antitone (hp0 : ∀ j < M, 0 ≤ p j) (hp1 : ∀ j < M, p j ≤ 1) (r j : ℕ) :
    phi p M r (j + 1) ≤ phi p M r j := (phi_mono_both hp0 hp1 r).1 j

lemma phi_succ_le (hp0 : ∀ j < M, 0 ≤ p j) (hp1 : ∀ j < M, p j ≤ 1) (r j : ℕ) :
    phi p M (r + 1) j ≤ phi p M r j := (phi_mono_both hp0 hp1 r).2 j

end Phi

/-! ### Lemma 9 (stochastic domination), generic -/

section Lemma9

variable {X : Type*} [Fintype X] {ν : X → ℝ}

/-- One supermartingale step: `E[φ(r, L_{s+1}) | F_s] ≤ φ(r+1, L_s)`. -/
lemma phi_step (hν1 : ∑ x, ν x = 1) {p : ℕ → ℝ} {M : ℕ}
    (hp0 : ∀ j < M, 0 ≤ p j) (hp1 : ∀ j < M, p j ≤ 1) (L : List X → ℕ)
    (hstep : ∀ l x, L (l ++ [x]) = L l ∨ L (l ++ [x]) = L l + 1)
    (hrate : ∀ l, L l < M → p (L l) ≤ ∑ x, ν x * ind (L (l ++ [x]) = L l + 1))
    (r : ℕ) (l : List X) :
    ∑ x, ν x * phi p M r (L (l ++ [x])) ≤ phi p M (r + 1) (L l) := by
  set j := L l with hj
  by_cases hjM : j < M
  · have e : ∀ x, phi p M r (L (l ++ [x])) =
        phi p M r j + ind (L (l ++ [x]) = j + 1) * (phi p M r (j + 1) - phi p M r j) := by
      intro x
      rcases hstep l x with h | h
      · rw [h, ← hj, ind_neg (by omega)]; ring
      · rw [h, ← hj, ind_pos rfl]; ring
    simp only [e, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hν1, one_mul]
    have hπ := hrate l (hj ▸ hjM)
    rw [← hj] at hπ
    have hd := phi_antitone hp0 hp1 r j
    have : ∑ x, ν x * (ind (L (l ++ [x]) = j + 1) * (phi p M r (j + 1) - phi p M r j)) =
        (∑ x, ν x * ind (L (l ++ [x]) = j + 1)) * (phi p M r (j + 1) - phi p M r j) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun x _ => by ring
    rw [this, phi_succ, if_pos hjM]
    nlinarith
  · have h0 : ∀ x, phi p M r (L (l ++ [x])) = 0 := fun x =>
      phi_ge p M r _ (by rcases hstep l x with h | h <;> omega)
    simp only [h0, mul_zero, Finset.sum_const_zero]
    rw [phi_ge p M _ _ (by omega)]

/-- **Lemma 9 (stochastic domination), generic form.** Let `L` count launches along the search
history: it starts at `0`, increases by `0` or `1` per round, and in stage `j = L < M` the
one-round launch probability is `≥ p_j ∈ [0,1]`. Then `P[L < M after K rounds] ≤ φ(K, 0)
= P[Σ_{j<M} G_j > K]`. -/
theorem lemma9 (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (p : ℕ → ℝ) (M : ℕ)
    (hp0 : ∀ j < M, 0 ≤ p j) (hp1 : ∀ j < M, p j ≤ 1) (L : List X → ℕ) (hL0 : L [] = 0)
    (hstep : ∀ l x, L (l ++ [x]) = L l ∨ L (l ++ [x]) = L l + 1)
    (hrate : ∀ l, L l < M → p (L l) ≤ ∑ x, ν x * ind (L (l ++ [x]) = L l + 1)) (K : ℕ) :
    EK ν K (fun l => ind (L l < M)) ≤ phi p M K 0 := by
  have key : ∀ s r, EK ν s (fun l => phi p M r (L l)) ≤ phi p M (r + s) (L []) := by
    intro s
    induction s with
    | zero => intro r; rw [EK_zero]; simp
    | succ s ih =>
      intro r
      rw [EK_succ]
      refine le_trans (EK_mono (g := fun l => phi p M (r + 1) (L l)) hν0 s
        fun xs => phi_step hν1 hp0 hp1 L hstep hrate r _) ?_
      have := ih (r + 1)
      rwa [show r + 1 + s = r + (s + 1) by omega] at this
  have := key K 0
  rw [zero_add, hL0] at this
  refine le_trans (le_of_eq ?_) this
  congr 1; funext l; rw [phi_zero]

end Lemma9

/-! ### Lemma 10 (geometric tail) -/

/-- `(1−p)(e^θ − 1) ≤ θ` for `0 ≤ θ ≤ p ≤ 1`. -/
lemma geom_key {p θ : ℝ} (hθ : 0 ≤ θ) (hθp : θ ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * (Real.exp θ - 1) ≤ θ := by
  have h1 : Real.exp θ - 1 ≤ θ * Real.exp θ := by
    have := Real.add_one_le_exp (-θ)
    have hm := mul_le_mul_of_nonneg_left this (Real.exp_pos θ).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
    nlinarith
  have h2 : (1 - p) * Real.exp θ ≤ 1 := by
    have h3 : (1 - p) * Real.exp θ ≤ (1 - p) * Real.exp p :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hθp) (by linarith)
    have h4 : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
    have h5 := mul_le_mul_of_nonneg_right h4 (Real.exp_pos p).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h5
    linarith
  have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 - p by linarith)
  nlinarith

/-- **Chernoff through the recursion.** For `0 ≤ θ < p_i ≤ 1` (`i < M`):
`φ(r, j) ≤ e^{−θ r} ∏_{i=j}^{M−1} e^θ p_i/(p_i − θ)`. -/
theorem phi_le_mgf {p : ℕ → ℝ} {M : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (hθp : ∀ j < M, θ < p j)
    (hp1 : ∀ j < M, p j ≤ 1) :
    ∀ r j, phi p M r j ≤
      Real.exp (-θ * r) * ∏ i ∈ Ico j M, (Real.exp θ * p i / (p i - θ)) := by
  have hc : ∀ i < M, 1 ≤ Real.exp θ * p i / (p i - θ) := by
    intro i hi
    have hpθ : 0 < p i - θ := by linarith [hθp i hi]
    rw [le_div_iff₀ hpθ, one_mul]
    nlinarith [Real.add_one_le_exp θ, hθp i hi]
  have hP : ∀ j, 0 ≤ ∏ i ∈ Ico j M, (Real.exp θ * p i / (p i - θ)) := fun j =>
    Finset.prod_nonneg fun i hi => le_trans zero_le_one (hc i (Finset.mem_Ico.1 hi).2)
  intro r
  induction r with
  | zero =>
    intro j
    rw [phi_zero]; simp only [Nat.cast_zero, mul_zero, Real.exp_zero, one_mul]
    by_cases hj : j < M
    · rw [ind_pos hj]
      calc (1:ℝ) = ∏ i ∈ Ico j M, (1:ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
            (fun i hi => hc i (Finset.mem_Ico.1 hi).2)
    · rw [ind_neg hj]; exact hP j
  | succ r ih =>
    intro j
    rw [phi_succ]
    split_ifs with hj
    · rw [Finset.prod_eq_prod_Ico_succ_bot hj]
      set P := ∏ i ∈ Ico (j + 1) M, (Real.exp θ * p i / (p i - θ))
      set c := Real.exp θ * p j / (p j - θ)
      have hpj := hθp j hj
      have hpj1 := hp1 j hj
      have hpθ : 0 < p j - θ := by linarith
      have h1 := ih (j + 1)
      have h2 := ih j
      rw [Finset.prod_eq_prod_Ico_succ_bot hj] at h2
      have hP0 : 0 ≤ P := hP (j + 1)
      have hp0 : 0 ≤ p j := by linarith
      -- `p + (1−p) c ≤ e^{−θ} c`
      have hkey : p j + (1 - p j) * c ≤ Real.exp (-θ) * c := by
        have hg := geom_key hθ hpj.le hpj1
        have hc' : Real.exp (-θ) * c = p j / (p j - θ) := by
          simp only [c]
          rw [show Real.exp (-θ) * (Real.exp θ * p j / (p j - θ)) =
            (Real.exp (-θ) * Real.exp θ) * p j / (p j - θ) by ring, ← Real.exp_add,
            neg_add_cancel, Real.exp_zero, one_mul]
        rw [hc']
        simp only [c]
        rw [show p j + (1 - p j) * (Real.exp θ * p j / (p j - θ)) =
            (p j * (p j - θ) + (1 - p j) * Real.exp θ * p j) / (p j - θ) by
              field_simp]
        refine div_le_div_of_nonneg_right ?_ hpθ.le
        nlinarith [mul_le_mul_of_nonneg_left hg hp0]
      have he : Real.exp (-θ * ((r + 1 : ℕ) : ℝ)) = Real.exp (-θ * r) * Real.exp (-θ) := by
        rw [← Real.exp_add]; push_cast; ring_nf
      rw [he]
      have hE := (Real.exp_pos (-θ * r)).le
      calc p j * phi p M r (j + 1) + (1 - p j) * phi p M r j
          ≤ p j * (Real.exp (-θ * r) * P) + (1 - p j) * (Real.exp (-θ * r) * (c * P)) := by
            have := mul_le_mul_of_nonneg_left h1 hp0
            have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - p j by linarith)
            linarith
        _ = Real.exp (-θ * r) * P * (p j + (1 - p j) * c) := by ring
        _ ≤ Real.exp (-θ * r) * P * (Real.exp (-θ) * c) :=
            mul_le_mul_of_nonneg_left hkey (mul_nonneg hE hP0)
        _ = _ := by ring
    · exact mul_nonneg (Real.exp_pos _).le (hP j)

/-- `p/(p − θ) ≤ κ^{p_*/p}` for `θ = p_*(1 − 1/κ)`, `0 < p_* ≤ p`, `κ > 1` (concavity of `log`). -/
lemma ratio_le {p ps κ : ℝ} (hps : 0 < ps) (hpp : ps ≤ p) (hκ : 1 < κ) :
    p / (p - ps * (1 - 1 / κ)) ≤ Real.exp (ps / p * Real.log κ) := by
  have hp : 0 < p := lt_of_lt_of_le hps hpp
  have hκ0 : 0 < κ := by linarith
  set a := ps / p
  have ha0 : 0 ≤ a := (div_pos hps hp).le
  have ha1 : a ≤ 1 := (div_le_one hp).2 hpp
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2 (x := 1 / κ) (y := 1)
    (by simp [hκ0]) (by simp) ha0 (by linarith : 0 ≤ 1 - a) (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero, one_div, Real.log_inv, mul_one] at hconc
  -- `a/κ + (1−a) = (p − θ)/p`
  have hlin : a * κ⁻¹ + (1 - a) = (p - ps * (1 - 1 / κ)) / p := by
    simp only [a]; field_simp; ring
  rw [hlin] at hconc
  have hpos : 0 < (p - ps * (1 - 1 / κ)) / p := by
    rw [← hlin]; have : 0 < κ⁻¹ := inv_pos.2 hκ0
    have hk1 : κ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hκ
    nlinarith [mul_le_mul_of_nonneg_right ha1 (sub_nonneg.2 hk1.le)]
  have hexp : Real.exp (-(a * Real.log κ)) ≤ (p - ps * (1 - 1 / κ)) / p := by
    rw [← Real.exp_log hpos]; exact Real.exp_le_exp.2 (by linarith)
  have hnum : 0 < p - ps * (1 - 1 / κ) := by
    have := div_pos hpos hp; rw [div_pos_iff] at hpos
    rcases hpos with h | h
    · exact h.1
    · linarith [h.2]
  rw [div_le_iff₀ hnum]
  have := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (a * Real.log κ)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
  rw [mul_div_assoc'] at this
  rw [le_div_iff₀ hp] at this
  linarith

/-- **Lemma 10 (geometric tail).** With `0 < p_* ≤ p_j ≤ 1` (`j < M`), `μ = Σ_{j<M} 1/p_j`,
`κ > 1` and `K ≥ M + κμ`: `φ(K, 0) = P[Σ_j G_j > K] ≤ exp(−p_* μ (κ − 1 − log κ))`. -/
theorem lemma10 (p : ℕ → ℝ) (M K : ℕ) (ps κ : ℝ) (hps : 0 < ps) (hpp : ∀ j < M, ps ≤ p j)
    (hp1 : ∀ j < M, p j ≤ 1) (hκ : 1 < κ)
    (hK : (M : ℝ) + κ * ∑ j ∈ range M, 1 / p j ≤ K) :
    phi p M K 0 ≤ Real.exp (-(ps * (∑ j ∈ range M, 1 / p j) * (κ - 1 - Real.log κ))) := by
  set θ := ps * (1 - 1 / κ)
  set μ := ∑ j ∈ range M, 1 / p j
  have hκ0 : 0 < κ := by linarith
  have hu : 0 < 1 - 1 / κ := by
    rw [sub_pos, div_lt_one hκ0]; exact hκ
  have hu1 : 1 - 1 / κ < 1 := by have : 0 < 1 / κ := by positivity
                                 linarith
  have hθ : 0 ≤ θ := (mul_pos hps hu).le
  have hθp : ∀ j < M, θ < p j := fun j hj => by
    have : θ < ps := by simp only [θ]; nlinarith
    linarith [hpp j hj]
  have h1 := phi_le_mgf hθ hθp hp1 K 0
  rw [Nat.Ico_zero_eq_range] at h1
  refine h1.trans ?_
  have hprod : ∏ i ∈ range M, (Real.exp θ * p i / (p i - θ)) ≤
      Real.exp (M * θ) * Real.exp (ps * Real.log κ * μ) := by
    have e : ∀ i, Real.exp θ * p i / (p i - θ) = Real.exp θ * (p i / (p i - θ)) := fun i => by
      rw [mul_div_assoc]
    simp only [e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [← Real.exp_nat_mul]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have : Real.exp (ps * Real.log κ * μ) = ∏ i ∈ range M, Real.exp (ps / p i * Real.log κ) := by
      rw [← Real.exp_sum]; congr 1
      simp only [μ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ratio_le hps
      (hpp i (Finset.mem_range.1 hi)) hκ)
    have := hθp i (Finset.mem_range.1 hi)
    exact div_nonneg (by linarith) (by linarith)
  have hμ0 : 0 ≤ μ := Finset.sum_nonneg fun j hj => by
    have := hpp j (Finset.mem_range.1 hj); exact (one_div_pos.2 (by linarith)).le
  calc Real.exp (-θ * K) * ∏ i ∈ range M, (Real.exp θ * p i / (p i - θ))
      ≤ Real.exp (-θ * K) * (Real.exp (M * θ) * Real.exp (ps * Real.log κ * μ)) :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (-θ * (K - M) + ps * Real.log κ * μ) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(ps * μ * (κ - 1 - Real.log κ))) := by
        refine Real.exp_le_exp.2 ?_
        have hKM : κ * μ ≤ (K : ℝ) - M := by linarith
        have := mul_le_mul_of_nonneg_left hKM hθ
        have e2 : θ * (κ * μ) = ps * μ * (κ - 1) := by
          simp only [θ]; field_simp
        nlinarith

/-! ### The attack: Lemma 9 for `Fof`, and the second branch of `P_nf` -/

section Attack

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [Nonempty ι]
variable {X : Type*} [Fintype X]
variable {G : Gallery E ι Fine} {A : Atk E X} {ν : X → ℝ}

/-- **Lemma 9 for the attack.** Fix `V` in the support with `Δ(V) ≤ δ`, and put
`p_j = nq − jν₁ − δ`. Then `P[fewer than M launches in K rounds | V] ≤ φ(K, 0)`. -/
theorem lemma9_attack (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (hε : 0 ≤ A.ε) (q ν₁ δ : ℝ)
    (H1 : ∀ i l, G.π i l ≠ 0 → q ≤ ∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0)
    (H5 : ∀ y : Sph E,
      (∑ x, if G.thr - 2 * A.ε < inner ℝ (A.pt x).1 y.1 then ν x else 0) ≤ ν₁)
    (V : ι → Fine) (hV : ∀ i, G.π i (V i) ≠ 0) (hΔ : Delta G A ν V ≤ δ)
    (hp0 : ∀ j < A.M, 0 ≤ (Fintype.card ι : ℝ) * q - j * ν₁ - δ) (K : ℕ) :
    EK ν K (fun l => ind ((Fof G A V l).length < A.M)) ≤
      phi (fun j => (Fintype.card ι : ℝ) * q - j * ν₁ - δ) A.M K 0 := by
  classical
  set p : ℕ → ℝ := fun j => (Fintype.card ι : ℝ) * q - j * ν₁ - δ
  have hrate5 : ∀ F : List (Sph E), p F.length ≤ ∑ x, ν x * ind (launches G A V F x) := by
    intro F
    have := lemma5 hν0 hε q ν₁ H1 H5 V hV F
    simp only [p]; linarith
  have hp1 : ∀ j < A.M, p j ≤ 1 := by
    intro j _
    have hν₁ := nu1_nonneg hν0 ν₁ H5
    have h := hrate5 []
    have hle : ∑ x, ν x * ind (launches G A V [] x) ≤ 1 := by
      rw [← hν1]; exact Finset.sum_le_sum fun x _ => by
        have := ind_le_one (launches G A V [] x); nlinarith [hν0 x]
    simp only [p, List.length_nil, CharP.cast_eq_zero, zero_mul, sub_zero] at h ⊢
    have : (0:ℝ) ≤ j * ν₁ := mul_nonneg (Nat.cast_nonneg _) hν₁
    linarith
  refine lemma9 hν0 hν1 p A.M hp0 hp1 (fun l => (Fof G A V l).length) (by simp [Fof, runSt_nil])
    (fun l x => ?_) (fun l hl => ?_) K
  · simp only [Fof_snoc, stepA_length]; split_ifs <;> simp
  · refine (hrate5 (Fof G A V l)).trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
    congr 1
    simp only [Fof_snoc, stepA_length]
    by_cases h : launches G A V (Fof G A V l) x
    · rw [if_pos ⟨hl, h⟩, ind_pos h, ind_pos rfl]
    · rw [if_neg (fun h' => h h'.2), ind_neg h, ind_neg (by omega)]

/-- **Theorem 6.3(c′), second branch.** For `0 < δ < a_{M−1} = nq − (M−1)ν₁`,
`p_j = nq − jν₁ − δ`, `μ = Σ_{j<M} 1/p_j`, `κ > 1` and `K ≥ M + κμ`:

`P_nf = P[fewer than M launches within K search rounds]
     ≤ D/δ + exp(−p_{M−1} μ (κ − 1 − log κ))`,  `D = n(n−1)μ₁q̄/2`. -/
theorem Pnf_le_chernoff (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (hε : 0 ≤ A.ε)
    (q μ₁ qbar ν₁ : ℝ)
    (H1 : ∀ i l, G.π i l ≠ 0 → q ≤ ∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0)
    (H3 : ∀ i (y : Sph E), (∑ l, if G.thr < inner ℝ y.1 (G.g l) then G.π i l else 0) ≤ μ₁)
    (H4 : ∀ i l, G.π i l ≠ 0 →
      (∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0) ≤ qbar)
    (H5 : ∀ y : Sph E,
      (∑ x, if G.thr - 2 * A.ε < inner ℝ (A.pt x).1 y.1 then ν x else 0) ≤ ν₁)
    (δ κ : ℝ) (hδ : 0 < δ)
    (hδa : δ < (Fintype.card ι : ℝ) * q - ((A.M : ℝ) - 1) * ν₁) (hκ : 1 < κ) (K : ℕ)
    (hK : (A.M : ℝ) + κ * ∑ j ∈ range A.M, 1 / ((Fintype.card ι : ℝ) * q - j * ν₁ - δ) ≤ K) :
    ∑ V, G.prior V * EK ν K (fun l => ind ((Fof G A V l).length < A.M)) ≤
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * μ₁ * qbar / 2 / δ +
        Real.exp (-(((Fintype.card ι : ℝ) * q - ((A.M : ℝ) - 1) * ν₁ - δ) *
          (∑ j ∈ range A.M, 1 / ((Fintype.card ι : ℝ) * q - j * ν₁ - δ)) *
            (κ - 1 - Real.log κ))) := by
  classical
  set n := (Fintype.card ι : ℝ)
  set p : ℕ → ℝ := fun j => n * q - j * ν₁ - δ
  set ps := n * q - ((A.M : ℝ) - 1) * ν₁ - δ
  set D := n * (n - 1) * μ₁ * qbar / 2
  set B := Real.exp (-(ps * (∑ j ∈ range A.M, 1 / p j) * (κ - 1 - Real.log κ)))
  have hν₁ := nu1_nonneg hν0 ν₁ H5
  have hps : 0 < ps := by simp only [ps]; linarith
  have hpp : ∀ j < A.M, ps ≤ p j := by
    intro j hj
    have : (j : ℝ) ≤ (A.M : ℝ) - 1 := by
      have : (j : ℝ) + 1 ≤ A.M := by exact_mod_cast hj
      linarith
    simp only [p, ps]; nlinarith
  have hp0 : ∀ j < A.M, 0 ≤ p j := fun j hj => le_trans hps.le (hpp j hj)
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
  have hper : ∀ V, G.prior V * EK ν K (fun l => ind ((Fof G A V l).length < A.M)) ≤
      G.prior V * (Delta G A ν V / δ + B) := by
    intro V
    by_cases hpr : G.prior V = 0
    · rw [hpr, zero_mul, zero_mul]
    have hV : ∀ i, G.π i (V i) ≠ 0 := fun i =>
      Finset.prod_ne_zero_iff.1 hpr i (Finset.mem_univ i)
    refine mul_le_mul_of_nonneg_left ?_ (G.prior_nonneg V)
    by_cases hΔ : Delta G A ν V ≤ δ
    · have h9 := lemma9_attack hν0 hν1 hε q ν₁ δ H1 H5 V hV hΔ hp0 K
      have hp1 : ∀ j < A.M, p j ≤ 1 := by
        intro j _
        have h := lemma5 hν0 hε q ν₁ H1 H5 V hV []
        have hle : ∑ x, ν x * ind (launches G A V [] x) ≤ 1 := by
          rw [← hν1]; exact Finset.sum_le_sum fun x _ => by
            have := ind_le_one (launches G A V [] x); nlinarith [hν0 x]
        simp only [List.length_nil, CharP.cast_eq_zero, zero_mul, sub_zero] at h
        have : (0:ℝ) ≤ j * ν₁ := mul_nonneg (Nat.cast_nonneg _) hν₁
        simp only [p]; linarith
      have h10 := lemma10 p A.M K ps κ hps hpp hp1 hκ hK
      have : 0 ≤ Delta G A ν V / δ := div_nonneg (Delta_nonneg hν0 V) hδ.le
      linarith
    · have h1 : EK ν K (fun l => ind ((Fof G A V l).length < A.M)) ≤ 1 :=
        EK_le_const hν0 hν1 K fun l _ => ind_le_one _
      have : 1 ≤ Delta G A ν V / δ := by rw [le_div_iff₀ hδ]; linarith
      linarith
  refine (Finset.sum_le_sum fun V _ => hper V).trans ?_
  have hD := lemma6_Delta (G := G) (A := A) hν0 μ₁ qbar H3 H4
  have e : ∑ V, G.prior V * (Delta G A ν V / δ + B) =
      (∑ V, G.prior V * Delta G A ν V) / δ + B := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, G.prior_sum, one_mul,
      Finset.sum_div]
    congr 1; exact Finset.sum_congr rfl fun V _ => by ring
  rw [e]
  have := div_le_div_of_nonneg_right hD hδ.le
  linarith

/-- Pathwise: `N_ε ≥ M·(1 − 1{fewer than M launches}) − B_d`. -/
lemma Neps_ge_ind (hdim : Module.finrank ℝ E = A.m + 2)
    (hΦ : ∀ x, Orthonormal ℝ (Fin.cons (A.pt x).1 (A.Φ x) : Fin (A.m + 2) → E))
    (ht0 : 0 < G.thr) (ht1 : G.thr < 1) (hc : 0 < A.c) (hc1 : G.thr + A.c < 1)
    (hεL : 0 < A.εL) (hεLε : A.εL ≤ A.ε) (hεL1 : A.εL < 1) (V : ι → Fine) (l : List X) :
    (A.M : ℝ) * (1 - ind ((Fof G A V l).length < A.M)) - Bd G A V l ≤ Neps G A V l := by
  have h4 := lemma4' G A hdim hΦ ht0 ht1 hc hc1 hεL hεLε hεL1 V l
  have : (A.M : ℝ) * (1 - ind ((Fof G A V l).length < A.M)) ≤ (Fof G A V l).length := by
    by_cases hf : (Fof G A V l).length < A.M
    · rw [ind_pos hf]; simp
    · rw [ind_neg hf, sub_zero, mul_one]; exact_mod_cast not_lt.1 hf
  linarith

/-- **Theorem 6.3(c′), `E[N_ε]` with the Chernoff branch of `P_nf`.** Hypotheses of
`thm63_markov` (except `0 < K` and `a_{M−1} > 0`, the latter implied by `δ < a_{M−1}`) plus those
of `Pnf_le_chernoff`:
`E[N_ε] ≥ M(1 − [D/δ + exp(−p_{M−1} μ (κ−1−log κ))]) − γ n q̄ (S + K D/a_{M−1}) − K Z̄`. -/
theorem thm63_chernoff (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (hdim : Module.finrank ℝ E = A.m + 2)
    (hΦ : ∀ x, Orthonormal ℝ (Fin.cons (A.pt x).1 (A.Φ x) : Fin (A.m + 2) → E))
    (ht0 : 0 < G.thr) (ht1 : G.thr < 1) (hc : 0 < A.c) (hc1 : G.thr + A.c < 1)
    (hεL : 0 < A.εL) (hεLε : A.εL ≤ A.ε) (hεL1 : A.εL < 1)
    (q γ μ₁ qbar ν₁ : ℝ) (hγ0 : 0 ≤ γ)
    (H1 : ∀ i l, G.π i l ≠ 0 → q ≤ ∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0)
    (H2 : ∀ i l, G.π i l ≠ 0 →
      (1 - γ) * (∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0) ≤
        ∑ x, if G.thr + A.c ≤ inner ℝ (A.pt x).1 (G.g l) then ν x else 0)
    (H3 : ∀ i (y : Sph E), (∑ l, if G.thr < inner ℝ y.1 (G.g l) then G.π i l else 0) ≤ μ₁)
    (H4 : ∀ i l, G.π i l ≠ 0 →
      (∑ x, if G.thr < inner ℝ (A.pt x).1 (G.g l) then ν x else 0) ≤ qbar)
    (H5 : ∀ y : Sph E,
      (∑ x, if G.thr - 2 * A.ε < inner ℝ (A.pt x).1 y.1 then ν x else 0) ≤ ν₁)
    (K : ℕ) (δ κ : ℝ) (hδ : 0 < δ)
    (hδa : δ < (Fintype.card ι : ℝ) * q - ((A.M : ℝ) - 1) * ν₁) (hκ : 1 < κ)
    (hK : (A.M : ℝ) + κ * ∑ j ∈ range A.M, 1 / ((Fintype.card ι : ℝ) * q - j * ν₁ - δ) ≤ K) :
    (A.M : ℝ) * (1 - ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * μ₁ * qbar / 2 / δ +
        Real.exp (-(((Fintype.card ι : ℝ) * q - ((A.M : ℝ) - 1) * ν₁ - δ) *
          (∑ j ∈ range A.M, 1 / ((Fintype.card ι : ℝ) * q - j * ν₁ - δ)) *
            (κ - 1 - Real.log κ)))))
      - γ * Fintype.card ι * qbar * ((∑ j ∈ range A.M, 1 / ((Fintype.card ι : ℝ) * q - j * ν₁)) +
          K * ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * μ₁ * qbar / 2) /
            ((Fintype.card ι : ℝ) * q - ((A.M : ℝ) - 1) * ν₁))
      - K * ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * qbar * μ₁ * (1 / 2 + qL G A))
      ≤ ∑ V, G.prior V * EK ν K (fun l => (Neps G A V l : ℝ)) := by
  set n := (Fintype.card ι : ℝ)
  set aM := n * q - ((A.M : ℝ) - 1) * ν₁
  set S := ∑ j ∈ range A.M, 1 / (n * q - j * ν₁)
  set D := n * (n - 1) * μ₁ * qbar / 2
  set Zb := n * (n - 1) * qbar * μ₁ * (1 / 2 + qL G A)
  set Pc := D / δ + Real.exp (-((n * q - ((A.M : ℝ) - 1) * ν₁ - δ) *
          (∑ j ∈ range A.M, 1 / (n * q - j * ν₁ - δ)) * (κ - 1 - Real.log κ)))
  have hε : 0 ≤ A.ε := by linarith
  have ha : 0 < aM := by simp only [aM]; linarith
  have hD : ∑ V, G.prior V * Delta G A ν V ≤ D := lemma6_Delta hν0 μ₁ qbar H3 H4
  have hZ : ∑ V, G.prior V * Zf G A ν V ≤ Zb := lemma6_Z hν0 hΦ μ₁ qbar H3 H4
  have hP : ∑ V, G.prior V * EK ν K (fun l => ind ((Fof G A V l).length < A.M)) ≤ Pc :=
    Pnf_le_chernoff hν0 hν1 hε q μ₁ qbar ν₁ H1 H3 H4 H5 δ κ hδ hδa hκ K hK
  have hqbar : 0 ≤ qbar := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have := support_mass (G := G) (A := A) (ν := ν) qbar H4 i
    refine le_trans (Finset.sum_nonneg fun l _ => mul_nonneg (G.hπ0 i l)
      (Finset.sum_nonneg fun x _ => mul_nonneg (hν0 x) (ind_nonneg _))) this
  set cg := γ * n * qbar
  have hcg : 0 ≤ cg := mul_nonneg (mul_nonneg hγ0 (Nat.cast_nonneg _)) hqbar
  have hper : ∀ V, G.prior V * ((A.M : ℝ) - A.M * EK ν K (fun l => ind ((Fof G A V l).length < A.M))
      - cg * (S + K * Delta G A ν V / aM) - K * Zf G A ν V) ≤
      G.prior V * EK ν K (fun l => (Neps G A V l : ℝ)) := by
    intro V
    by_cases hp : G.prior V = 0
    · rw [hp, zero_mul, zero_mul]
    have hV : ∀ i, G.π i (V i) ≠ 0 := fun i =>
      Finset.prod_ne_zero_iff.1 hp i (Finset.mem_univ i)
    refine mul_le_mul_of_nonneg_left ?_ (G.prior_nonneg V)
    have h1 : EK ν K (fun l => (A.M : ℝ) + (-(A.M : ℝ)) * ind ((Fof G A V l).length < A.M) +
        (-1) * Bd G A V l) ≤ EK ν K (fun l => (Neps G A V l : ℝ)) := by
      refine EK_mono hν0 K fun xs => ?_
      have := Neps_ge_ind hdim hΦ ht0 ht1 hc hc1 hεL hεLε hεL1 V (List.ofFn xs)
      linarith
    rw [EK_affine hν1] at h1
    have h7 := lemma7 hν0 hν1 hε q ν₁ H1 H5 ha V hV K
    have h8 := lemma8 hν0 hν1 hc γ qbar hγ0 H2 H4 V hV K
    have : cg * EK ν K (tau G A V) ≤ cg * (S + K * Delta G A ν V / aM) :=
      mul_le_mul_of_nonneg_left h7 hcg
    linarith
  have hsum := Finset.sum_le_sum fun V (_ : V ∈ univ) => hper V
  clear_value S Pc
  have e3 : ∑ V, G.prior V * ((A.M : ℝ) - A.M * EK ν K (fun l => ind ((Fof G A V l).length < A.M))
      - cg * (S + K * Delta G A ν V / aM) - K * Zf G A ν V) =
      (A.M - cg * S) * ∑ V, G.prior V
        - A.M * ∑ V, G.prior V * EK ν K (fun l => ind ((Fof G A V l).length < A.M))
        - (cg * K / aM) * ∑ V, G.prior V * Delta G A ν V - K * ∑ V, G.prior V * Zf G A ν V := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun V _ => by ring
  rw [e3, G.prior_sum, mul_one] at hsum
  have hKr : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hcK : 0 ≤ cg * K / aM := div_nonneg (mul_nonneg hcg hKr) ha.le
  have := mul_le_mul_of_nonneg_left hD hcK
  have := mul_le_mul_of_nonneg_left hZ hKr
  have := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg A.M : (0:ℝ) ≤ A.M)
  have e4 : (A.M : ℝ) * (1 - Pc) - cg * (S + K * D / aM) - K * Zb =
      A.M - cg * S - A.M * Pc - (cg * K / aM) * D - K * Zb := by
    field_simp; ring
  rw [e4]
  linarith

end Attack

end OracleBounds.Attacks.RandomSearch

#print axioms OracleBounds.Attacks.RandomSearch.phi_antitone
#print axioms OracleBounds.Attacks.RandomSearch.lemma9
#print axioms OracleBounds.Attacks.RandomSearch.phi_le_mgf
#print axioms OracleBounds.Attacks.RandomSearch.lemma10
#print axioms OracleBounds.Attacks.RandomSearch.lemma9_attack
#print axioms OracleBounds.Attacks.RandomSearch.Pnf_le_chernoff
#print axioms OracleBounds.Attacks.RandomSearch.thm63_chernoff
