import OracleBounds.GeneralPrior.BudgetBest

/-!
# Per-person match cap: the joint (queries, matches) information bound

**Statements reviewed and signed off by the administrator (2026-10-14)**: `info_le_concave`,
`gallery_info_le_concave`, `match_cap_fano` transcribe briefs/attacks/match-cap.md §1–3; the hypothesis
`2·Cp ≤ Q` is the monotonicity caveat recorded there.

Imported from `OracleBounds.lean` (signed off 2026-10-14). No `sorry`s.

Kernel K1(ρ) (`κ s = 1−ρ` if `thr < s`, else `ρ`; `0 < ρ ≤ ½`), `h = Real.binEntropy`,
`φ(s) = h(ρ + (1−2ρ)s) − h(ρ)` (`MatchCap.phi`), `S` = number of rounds whose probe reaches the
target entry.

* `Face.info_le_concave` — **(★), locked §3**: one face, the others summarised by the environment
  `m` (`Face.lean`): `I(g; b₁..b_Q) ≤ Q·[h(ρ + (1−2ρ)·E[S]/Q) − h(ρ)]`.
* `Gallery.gallery_info_le_concave` — the gallery form, `I(Vᵢ; b | V₋ᵢ) ≤ (same)` with
  `E[S]` averaged over `V ∼ ∏πⱼ` (per-environment (★), then Jensen over `V₋ᵢ`).
* `Face.face_fano` — Fano with `E[S] ≤ C ≤ Q/2`.
* `Face.capInfo_le`, `Face.EScap_le`, `Face.match_cap_fano` — the per-person cap as an oracle
  (truthful about the entry for its first `Cp` reaching rounds, then the ghost response):
  `E[S] ≤ Cp` pathwise, and the §1 recovery bound with `Cp` in place of `E[S]`.

**Deviation from §1.** `φ` increases only on `[0, ½]` and is symmetric about `½` (`φ(1) = 0`), so
(★) is monotone in `E[S]` only for `E[S] ≤ Q/2`; the Fano consequence needs `2·Cp ≤ Q` (for larger
caps the bound is `Q·Cap(ρ)`, `MatchCap.phi_le_cap`). The note's "largest `C_p`" certifying the
target must be taken in `[0, Q/2]`.

**Proof route.** `MatchCap.Dw` is `W·I` for a subtree under unnormalised weights `w` (posterior
masses); `Dw_succ` is the chain rule (first bit + posterior-weighted subtrees), `T1_eq` evaluates
the first-bit term exactly as `W·(h(p̄) − h(ρ))` with the *marginal* `p̄` (the `H(b_t|past, g) =
h(ρ)` step), and `Dw_le` closes the induction with superadditivity of the perspective `a·φ(s/a)`
(`persp_add`, from `Real.strictConcave_binEntropy`). The generic form `info_le_concave_gen` takes
any probe space `X`; the capped oracle uses `X = List Bool`, `probe = id` (history-dependent
kernel).
-/

namespace OracleBounds.GeneralPrior.MatchCap

open Finset OracleBounds.V6

/-! ### The concave rate `φ` and its perspective -/

/-- `φ(s) = h(ρ + (1−2ρ)s) − h(ρ)`. -/
noncomputable def phi (ρ s : ℝ) : ℝ := Real.binEntropy (ρ + (1 - 2 * ρ) * s) - Real.binEntropy ρ

/-- The perspective `a·φ(s/a)` (`= 0` at `a = 0`). -/
noncomputable def persp (ρ a s : ℝ) : ℝ := a * phi ρ (s / a)

lemma mem_aff {ρ s : ℝ} (hρ1 : ρ ≤ 1 / 2) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ρ ≤ ρ + (1 - 2 * ρ) * s ∧ ρ + (1 - 2 * ρ) * s ≤ 1 - ρ := by
  obtain ⟨h0, h1⟩ := hs
  constructor <;> nlinarith

lemma phi_concave {ρ x y a b : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * phi ρ x + b * phi ρ y ≤ phi ρ (a * x + b * y) := by
  have mx := mem_aff hρ1 hx
  have my := mem_aff hρ1 hy
  have hc := Real.strictConcave_binEntropy.concaveOn.2
    (⟨by linarith, by linarith⟩ : ρ + (1 - 2 * ρ) * x ∈ Set.Icc (0 : ℝ) 1)
    (⟨by linarith, by linarith⟩ : ρ + (1 - 2 * ρ) * y ∈ Set.Icc (0 : ℝ) 1) ha hb hab
  simp only [smul_eq_mul] at hc
  have e : a * (ρ + (1 - 2 * ρ) * x) + b * (ρ + (1 - 2 * ρ) * y) =
      ρ + (1 - 2 * ρ) * (a * x + b * y) := by
    have : b = 1 - a := by linarith
    subst this; ring
  rw [e] at hc
  unfold phi
  have : b = 1 - a := by linarith
  subst this
  nlinarith

lemma phi_nonneg {ρ s : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ phi ρ s := by
  have m := mem_aff hρ1 hs
  have hc := Real.strictConcave_binEntropy.concaveOn.min_le_of_mem_Icc
    (x := ρ) (y := 1 - ρ) (z := ρ + (1 - 2 * ρ) * s) ⟨hρ0, by linarith⟩
    ⟨by linarith, by linarith⟩ m
  rw [Real.binEntropy_one_sub, min_self] at hc
  unfold phi; linarith

lemma phi_zero (ρ : ℝ) : phi ρ 0 = 0 := by simp [phi]

/-- `φ` is nondecreasing on `[0, ½]`. -/
lemma phi_mono {ρ s t : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 1 / 2) : phi ρ s ≤ phi ρ t := by
  rcases eq_or_lt_of_le hρ1 with hh | hh
  · subst hh; simp [phi]
  have hd : 0 < 1 - 2 * ρ := by linarith
  -- `h` is monotone on `[0, ½]`
  have hmono : MonotoneOn Real.binEntropy (Set.Icc 0 (1 / 2)) := by
    intro u hu v hv huv
    rcases eq_or_lt_of_le huv with h | h
    · rw [h]
    by_contra hlt
    push Not at hlt
    -- concavity: h(v) ≥ min(h u, h (1-u)) = h u since v ∈ [u, 1-u]
    have hc := Real.strictConcave_binEntropy.concaveOn.min_le_of_mem_Icc
      (x := u) (y := 1 - u) (z := v) ⟨hu.1, by linarith [hu.2]⟩
      ⟨by linarith [hu.2], by linarith [hu.1]⟩ ⟨huv, by linarith [hv.2, hu.2]⟩
    rw [Real.binEntropy_one_sub, min_self] at hc
    linarith
  unfold phi
  have := hmono ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩
    (show ρ + (1 - 2 * ρ) * s ≤ ρ + (1 - 2 * ρ) * t by nlinarith)
  linarith

lemma phi_le_cap (ρ s : ℝ) :
    phi ρ s ≤ Real.log 2 - Real.binEntropy ρ := by
  unfold phi; linarith [Real.binEntropy_le_log_two (p := ρ + (1 - 2 * ρ) * s)]

lemma persp_zero (ρ s : ℝ) : persp ρ 0 s = 0 := by simp [persp]

/-- Superadditivity of the perspective (concavity of `φ`). -/
lemma persp_add {ρ a b s t : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2) (hs : 0 ≤ s) (hsa : s ≤ a)
    (ht : 0 ≤ t) (htb : t ≤ b) :
    persp ρ a s + persp ρ b t ≤ persp ρ (a + b) (s + t) := by
  rcases eq_or_lt_of_le (hs.trans hsa) with ha | ha
  · have : s = 0 := le_antisymm (ha ▸ hsa) hs
    subst ha; subst this; simp [persp_zero]
  rcases eq_or_lt_of_le (ht.trans htb) with hb | hb
  · have : t = 0 := le_antisymm (hb ▸ htb) ht
    subst hb; subst this; simp [persp_zero]
  have hc : 0 < a + b := by linarith
  have hx : s / a ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one ha).2 hsa⟩
  have hy : t / b ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hb).2 htb⟩
  have h := phi_concave hρ0 hρ1 hx hy (a := a / (a + b)) (b := b / (a + b)) (by positivity)
    (by positivity) (by field_simp)
  have e : a / (a + b) * (s / a) + b / (a + b) * (t / b) = (s + t) / (a + b) := by
    field_simp
  rw [e] at h
  unfold persp
  have := mul_le_mul_of_nonneg_left h hc.le
  have e2 : (a + b) * (a / (a + b) * phi ρ (s / a) + b / (a + b) * phi ρ (t / b)) =
      a * phi ρ (s / a) + b * phi ρ (t / b) := by field_simp
  linarith

lemma persp_nonneg {ρ a s : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2) (hs : 0 ≤ s) (hsa : s ≤ a) :
    0 ≤ persp ρ a s := by
  rcases eq_or_lt_of_le (hs.trans hsa) with ha | ha
  · subst ha; simp [persp_zero]
  exact mul_nonneg ha.le (phi_nonneg hρ0 hρ1 ⟨by positivity, (div_le_one ha).2 hsa⟩)

/-- Homogeneity: `persp(c·a, c·s) = c·persp(a, s)` for `c ≥ 0`. -/
lemma persp_smul {ρ a s c : ℝ} (hc : 0 ≤ c) : persp ρ (c * a) (c * s) = c * persp ρ a s := by
  rcases eq_or_lt_of_le hc with h | h
  · subst h; simp [persp_zero]
  unfold persp
  rw [mul_div_mul_left _ _ h.ne']; ring


/-- Finite superadditivity of the perspective (Jensen for `φ`). -/
lemma persp_sum {α : Type*} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2) (s : Finset α)
    (a b : α → ℝ) (hab : ∀ k ∈ s, 0 ≤ b k ∧ b k ≤ a k) :
    ∑ k ∈ s, persp ρ (a k) (b k) ≤ persp ρ (∑ k ∈ s, a k) (∑ k ∈ s, b k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [persp_zero]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, Finset.sum_insert hk]
    have hk' := hab k (Finset.mem_insert_self k s)
    have hs : ∀ j ∈ s, 0 ≤ b j ∧ b j ≤ a j := fun j hj => hab j (Finset.mem_insert_of_mem hj)
    have h1 := ih hs
    have h2 := persp_add hρ0 hρ1 hk'.1 hk'.2 (Finset.sum_nonneg fun j hj => (hs j hj).1)
      (Finset.sum_le_sum fun j hj => (hs j hj).2)
    linarith

/-! ### Generic: unnormalised mutual information of a subtree and its recursion -/

section Generic

variable {X Θ : Type*} [Fintype Θ]

/-- `W·I(θ; next r bits)` at history `h`, under (unnormalised) weights `w` on the hidden
parameter: `Σ_θ Σ_e w θ P_θ(e) log(P_θ(e)·W / Σ_θ' w θ' P_θ'(e))`, `W = Σ w`. -/
noncomputable def Dw (p : Θ → X → ℝ) (probe : List Bool → X) (w : Θ → ℝ) (r : ℕ)
    (h : List Bool) : ℝ :=
  ∑ θ, ∑ e : Fin r → Bool, w θ * pathProb (p θ) probe r h e *
    Real.log (pathProb (p θ) probe r h e * (∑ θ', w θ') /
      ∑ θ', w θ' * pathProb (p θ') probe r h e)

/-- Weights after observing bit `b` at probe `x` (posterior, unnormalised). -/
noncomputable def wb (p : Θ → X → ℝ) (x : X) (w : Θ → ℝ) (b : Bool) : Θ → ℝ :=
  fun θ => w θ * bern (p θ x) b

lemma log_div_self' (x : ℝ) : Real.log (x / x) = 0 := by
  rcases eq_or_ne x 0 with h | h
  · simp [h]
  · simp [div_self h]

lemma Dw_zero (p : Θ → X → ℝ) (probe : List Bool → X) (w : Θ → ℝ) (h : List Bool) :
    Dw p probe w 0 h = 0 := by
  simp [Dw, pathProb]

lemma Dw_succ (p : Θ → X → ℝ) (hp : ∀ θ x, 0 ≤ p θ x ∧ p θ x ≤ 1) (probe : List Bool → X)
    (w : Θ → ℝ) (hw : ∀ θ, 0 ≤ w θ) (r : ℕ) (h : List Bool) :
    Dw p probe w (r + 1) h =
      ∑ b : Bool, ∑ θ, wb p (probe h) w b θ *
        Real.log (bern (p θ (probe h)) b * (∑ θ', w θ') / ∑ θ', wb p (probe h) w b θ') +
      ∑ b : Bool, Dw p probe (wb p (probe h) w b) r (h ++ [b]) := by
  set x := probe h
  have key : ∀ θ b (e' : Fin r → Bool),
      w θ * pathProb (p θ) probe (r + 1) h (Fin.cons b e') *
        Real.log (pathProb (p θ) probe (r + 1) h (Fin.cons b e') * (∑ θ', w θ') /
          ∑ θ', w θ' * pathProb (p θ') probe (r + 1) h (Fin.cons b e')) =
      pathProb (p θ) probe r (h ++ [b]) e' * (wb p x w b θ *
        Real.log (bern (p θ x) b * (∑ θ', w θ') / ∑ θ', wb p x w b θ')) +
      wb p x w b θ * pathProb (p θ) probe r (h ++ [b]) e' *
        Real.log (pathProb (p θ) probe r (h ++ [b]) e' * (∑ θ', wb p x w b θ') /
          ∑ θ', wb p x w b θ' * pathProb (p θ') probe r (h ++ [b]) e') := by
    intro θ b e'
    simp only [pathProb, Fin.cons_zero, Fin.tail_cons]
    have hden : ∑ θ', w θ' * (bern (p θ' x) b * pathProb (p θ') probe r (h ++ [b]) e') =
        ∑ θ', wb p x w b θ' * pathProb (p θ') probe r (h ++ [b]) e' :=
      Finset.sum_congr rfl fun θ' _ => by simp only [wb]; ring
    rw [hden]
    simp only [wb]
    set B := bern (p θ x) b
    set P := pathProb (p θ) probe r (h ++ [b]) e'
    set M := ∑ θ', w θ' * bern (p θ' x) b * pathProb (p θ') probe r (h ++ [b]) e'
    set Wb := ∑ θ', w θ' * bern (p θ' x) b
    have hB : 0 ≤ B := (bern_mem (hp θ x) b).1
    have hP : 0 ≤ P := pathProb_nonneg probe (hp θ) _ _ _
    rcases eq_or_lt_of_le (hw θ) with h0 | h0
    · rw [← h0]; simp
    rcases eq_or_lt_of_le hB with h1 | h1
    · rw [← h1]; simp
    rcases eq_or_lt_of_le hP with h2 | h2
    · rw [← h2]; simp
    have hWb : w θ * B ≤ Wb := Finset.single_le_sum (f := fun θ' => w θ' * bern (p θ' x) b)
      (fun θ' _ => mul_nonneg (hw θ') (bern_mem (hp θ' x) b).1) (Finset.mem_univ θ)
    have hM : w θ * B * P ≤ M := Finset.single_le_sum
      (f := fun θ' => w θ' * bern (p θ' x) b * pathProb (p θ') probe r (h ++ [b]) e')
      (fun θ' _ => mul_nonneg (mul_nonneg (hw θ') (bern_mem (hp θ' x) b).1)
        (pathProb_nonneg probe (hp θ') _ _ _)) (Finset.mem_univ θ)
    set W := ∑ θ', w θ'
    have hW : w θ ≤ W := Finset.single_le_sum (f := w) (fun θ' _ => hw θ') (Finset.mem_univ θ)
    have hWp : 0 < W := h0.trans_le hW
    have hWbp : 0 < Wb := (mul_pos h0 h1).trans_le hWb
    have hMp : 0 < M := (mul_pos (mul_pos h0 h1) h2).trans_le hM
    rw [show B * P * W / M = (B * W / Wb) * (P * Wb / M) by field_simp,
      Real.log_mul (by positivity) (by positivity)]
    ring
  have hL : Dw p probe w (r + 1) h = ∑ θ, ∑ b : Bool, ∑ e' : Fin r → Bool,
      (pathProb (p θ) probe r (h ++ [b]) e' * (wb p x w b θ *
        Real.log (bern (p θ x) b * (∑ θ', w θ') / ∑ θ', wb p x w b θ')) +
      wb p x w b θ * pathProb (p θ) probe r (h ++ [b]) e' *
        Real.log (pathProb (p θ) probe r (h ++ [b]) e' * (∑ θ', wb p x w b θ') /
          ∑ θ', wb p x w b θ' * pathProb (p θ') probe r (h ++ [b]) e')) := by
    unfold Dw
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [sum_fin_succ_bool, Fintype.sum_bool]
    simp only [key]
  rw [hL]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, pathProb_sum probe (hp _), one_mul]
  rw [Finset.sum_comm]
  unfold Dw
  rw [Finset.sum_comm (s := (Finset.univ : Finset Θ)) (t := (Finset.univ : Finset Bool))]

lemma sum_bern_log (a : ℝ) :
    ∑ b : Bool, bern a b * Real.log (bern a b) = - Real.binEntropy a := by
  simp only [Fintype.sum_bool, bern, if_true, Bool.false_eq_true, if_false, Real.binEntropy,
    Real.log_inv]
  ring

/-- **The per-round term** (pieces (i) and the marginal-reference step): for a two-valued kernel,
the first-bit contribution to `W·I` is `W·(h(p̄) − h(ρ))`, `p̄ = Σ w p / W`. -/
lemma T1_eq {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (p : Θ → X → ℝ) (x : X)
    (hp2 : ∀ θ, p θ x = ρ ∨ p θ x = 1 - ρ) (w : Θ → ℝ) (hw : ∀ θ, 0 ≤ w θ)
    (hW : 0 < ∑ θ, w θ) :
    ∑ b : Bool, ∑ θ, wb p x w b θ *
        Real.log (bern (p θ x) b * (∑ θ', w θ') / ∑ θ', wb p x w b θ') =
      (∑ θ, w θ) * (Real.binEntropy ((∑ θ, w θ * p θ x) / ∑ θ, w θ) - Real.binEntropy ρ) := by
  set W := ∑ θ, w θ
  have hB : ∀ θ b, ρ ≤ bern (p θ x) b := by
    intro θ b
    rcases hp2 θ with h | h <;> cases b <;> simp [bern, h] <;> linarith
  have hBp : ∀ θ b, 0 < bern (p θ x) b := fun θ b => hρ0.trans_le (hB θ b)
  have hWb : ∀ b, 0 < ∑ θ', wb p x w b θ' := by
    intro b
    have : ρ * W ≤ ∑ θ', wb p x w b θ' := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun θ _ => by
        simp only [wb]; nlinarith [hw θ, hB θ b]
    have := mul_pos hρ0 hW; linarith
  have hpt : ∀ b θ, wb p x w b θ *
      Real.log (bern (p θ x) b * W / ∑ θ', wb p x w b θ') =
      w θ * (bern (p θ x) b * Real.log (bern (p θ x) b)) -
        wb p x w b θ * Real.log ((∑ θ', wb p x w b θ') / W) := by
    intro b θ
    rw [show bern (p θ x) b * W / ∑ θ', wb p x w b θ' =
        bern (p θ x) b / ((∑ θ', wb p x w b θ') / W) by
          field_simp,
      Real.log_div (hBp θ b).ne' (div_pos (hWb b) hW).ne']
    simp only [wb]; ring
  simp only [hpt, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_bern_log]
  have hh : ∀ θ, Real.binEntropy (p θ x) = Real.binEntropy ρ := by
    intro θ; rcases hp2 θ with h | h <;> rw [h]; exact Real.binEntropy_one_sub ρ
  simp only [hh]
  -- the marginal term
  set q := (∑ θ, w θ * p θ x) / W
  have hT : ∑ θ', wb p x w true θ' = W * q := by
    simp only [q, wb, bern, if_true]; field_simp
  have hF : ∑ θ', wb p x w false θ' = W * (1 - q) := by
    simp only [q, wb, bern, Bool.false_eq_true, if_false]
    rw [mul_sub, mul_one, mul_div_cancel₀ _ hW.ne']
    simp only [W, mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [Fintype.sum_bool, hT, hF, mul_div_cancel_left₀ _ hW.ne', mul_div_cancel_left₀ _ hW.ne']
  simp only [Real.binEntropy, Real.log_inv]
  rw [← Finset.sum_mul]
  ring

open Classical in
/-- The kernel shape of §0: at each probe either some *other* entry is reached (answer law
`Bern(1−ρ)` whatever `θ`), or the answer is `Bern(1−ρ)` iff the probe reaches `θ` (`act θ x`),
`Bern(ρ)` otherwise. -/
def TwoValued (ρ : ℝ) (p : Θ → X → ℝ) (act : Θ → X → Prop) : Prop :=
  ∀ x, (∀ θ, p θ x = 1 - ρ) ∨ (∀ θ, p θ x = if act θ x then 1 - ρ else ρ)

omit [Fintype Θ] in
lemma TwoValued.two {ρ : ℝ} {p : Θ → X → ℝ} {act : Θ → X → Prop} (H : TwoValued ρ p act)
    (θ : Θ) (x : X) : p θ x = ρ ∨ p θ x = 1 - ρ := by
  classical
  rcases H x with h | h
  · exact Or.inr (h θ)
  · rw [h θ]; split_ifs <;> simp

omit [Fintype Θ] in
lemma TwoValued.mem {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) {p : Θ → X → ℝ}
    {act : Θ → X → Prop} (H : TwoValued ρ p act) (θ : Θ) (x : X) : 0 ≤ p θ x ∧ p θ x ≤ 1 := by
  rcases H.two θ x with h | h <;> rw [h] <;> constructor <;> linarith

open Classical in
lemma T1_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (p : Θ → X → ℝ) (act : Θ → X → Prop)
    (H : TwoValued ρ p act) (x : X) (w : Θ → ℝ) (hw : ∀ θ, 0 ≤ w θ) :
    ∑ b : Bool, ∑ θ, wb p x w b θ *
        Real.log (bern (p θ x) b * (∑ θ', w θ') / ∑ θ', wb p x w b θ') ≤
      persp ρ (∑ θ, w θ) (∑ θ, w θ * if act θ x then 1 else 0) := by
  set W := ∑ θ, w θ
  set A := ∑ θ, w θ * if act θ x then (1 : ℝ) else 0
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun θ _ => mul_nonneg (hw θ) (by split_ifs <;> norm_num)
  have hAW : A ≤ W := Finset.sum_le_sum fun θ _ => by
    have := hw θ; split_ifs <;> simp [this]
  rcases eq_or_lt_of_le (Finset.sum_nonneg fun θ _ => hw θ : (0 : ℝ) ≤ W) with hW | hW
  · have h0 : ∀ θ, w θ = 0 := fun θ =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun θ _ => hw θ)).1 hW.symm θ (Finset.mem_univ θ)
    have hW0 : W = 0 := hW.symm
    rw [hW0, persp_zero]
    simp [wb, h0]
  rw [T1_eq hρ0 hρ1 p x (fun θ => H.two θ x) w hw hW]
  rcases H x with h | h
  · simp only [h, ← Finset.sum_mul]
    rw [mul_div_cancel_left₀ _ hW.ne', Real.binEntropy_one_sub, sub_self, mul_zero]
    exact persp_nonneg hρ0.le hρ1 hA0 hAW
  · have e : (∑ θ, w θ * p θ x) / W = ρ + (1 - 2 * ρ) * (A / W) := by
      rw [div_eq_iff hW.ne', add_mul, mul_assoc, div_mul_cancel₀ _ hW.ne']
      simp only [h, A, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun θ _ => by split_ifs <;> ring
    rw [e]; rfl

open Classical in
/-- **Induction (chain rule + Jensen).** `W·I(θ; next r bits | h) ≤ persp(r·W, S)` with `S` the
`w`-weighted expected count of `act`-rounds. -/
theorem Dw_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (p : Θ → X → ℝ) (act : Θ → X → Prop)
    (H : TwoValued ρ p act) (probe : List Bool → X) :
    ∀ r h (w : Θ → ℝ), (∀ θ, 0 ≤ w θ) →
      Dw p probe w r h ≤ persp ρ (r * ∑ θ, w θ)
        (∑ θ, w θ * accCount (p θ) probe (act θ) r h) := by
  have hp := H.mem hρ0 hρ1
  intro r
  induction r with
  | zero => intro h w _; simp [Dw_zero, persp_zero]
  | succ r ih =>
    intro h w hw
    set x := probe h
    have hwb : ∀ b θ, 0 ≤ wb p x w b θ := fun b θ => mul_nonneg (hw θ) (bern_mem (hp θ x) b).1
    rw [Dw_succ p hp probe w hw r h,
      Fintype.sum_bool (fun b => Dw p probe (wb p x w b) r (h ++ [b]))]
    have h1 := T1_le hρ0 hρ1 p act H x w hw
    have hT := ih (h ++ [true]) (wb p x w true) (hwb true)
    have hF := ih (h ++ [false]) (wb p x w false) (hwb false)
    -- the bounds for the perspective
    have hacc := fun θ b => accCount_mem (p θ) (hp θ) probe (act θ) r (h ++ [b])
    have hS : ∀ b, 0 ≤ ∑ θ, wb p x w b θ * accCount (p θ) probe (act θ) r (h ++ [b]) ∧
        ∑ θ, wb p x w b θ * accCount (p θ) probe (act θ) r (h ++ [b]) ≤
          r * ∑ θ, wb p x w b θ := by
      intro b
      refine ⟨Finset.sum_nonneg fun θ _ => mul_nonneg (hwb b θ) (hacc θ b).1, ?_⟩
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun θ _ => by
        nlinarith [mul_le_mul_of_nonneg_left (hacc θ b).2 (hwb b θ)]
    set A := ∑ θ, w θ * if act θ x then (1 : ℝ) else 0
    have hA0 : 0 ≤ A :=
      Finset.sum_nonneg fun θ _ => mul_nonneg (hw θ) (by split_ifs <;> norm_num)
    have hAW : A ≤ ∑ θ, w θ := Finset.sum_le_sum fun θ _ => by
      have := hw θ; split_ifs <;> simp [this]
    have j1 := persp_add hρ0.le hρ1 hA0 hAW (hS true).1 (hS true).2
    have j2 := persp_add hρ0.le hρ1 (add_nonneg hA0 (hS true).1)
      (add_le_add hAW (hS true).2) (hS false).1 (hS false).2
    -- totals
    have hWsplit : ∑ θ, wb p x w true θ + ∑ θ, wb p x w false θ = ∑ θ, w θ := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun θ _ => ?_
      simp only [wb, bern, if_true, Bool.false_eq_true, if_false]; ring
    have hSsplit : A + ∑ θ, wb p x w true θ * accCount (p θ) probe (act θ) r (h ++ [true]) +
        ∑ θ, wb p x w false θ * accCount (p θ) probe (act θ) r (h ++ [false]) =
        ∑ θ, w θ * accCount (p θ) probe (act θ) (r + 1) h := by
      simp only [A, ← Finset.sum_add_distrib, accCount]
      refine Finset.sum_congr rfl fun θ _ => ?_
      simp only [wb, bern, if_true, Bool.false_eq_true, if_false, x]; ring
    have hlen : ∑ θ, w θ + r * ∑ θ, wb p x w true θ + r * ∑ θ, wb p x w false θ =
        ((r + 1 : ℕ) : ℝ) * ∑ θ, w θ := by
      push_cast; linear_combination (r : ℝ) * hWsplit
    rw [hlen, hSsplit] at j2
    linarith

lemma mutualInfo_eq_Dw (π : Θ → ℝ) (hπ1 : ∑ θ, π θ = 1) (p : Θ → X → ℝ)
    (hp : ∀ θ x, 0 ≤ p θ x ∧ p θ x ≤ 1) (probe : List Bool → X) (Q : ℕ) :
    Info.mutualInfo (fun te : Θ × (Fin Q → Bool) => π te.1 * pathProb (p te.1) probe Q [] te.2) =
      Dw p probe π Q [] := by
  unfold Info.mutualInfo Dw
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun θ _ => Finset.sum_congr rfl fun e _ => ?_
  have hm1 : Info.marg₁ (fun te : Θ × (Fin Q → Bool) =>
      π te.1 * pathProb (p te.1) probe Q [] te.2) θ = π θ := by
    simp [Info.marg₁, ← Finset.mul_sum, pathProb_sum probe (hp θ)]
  simp only [hm1, Info.marg₂, hπ1, mul_one]
  rcases eq_or_ne (π θ) 0 with h | h
  · simp [h]
  · rw [mul_div_mul_left _ _ h]

open Classical in
/-- **Theorem (★), generic form.** Hidden `θ ∼ π`, two-valued kernel (`TwoValued`), any adaptive
probe rule: `I(θ; b₁..b_Q) ≤ Q·[h(ρ + (1−2ρ)·E[S]/Q) − h(ρ)]`, `S` the number of `act`-rounds.
The probe space `X` is arbitrary; taking `X = List Bool` (with `probe = id`) allows the kernel to
depend on the whole history, which is how the capped oracle is covered below. -/
theorem info_le_concave_gen {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (π : Θ → ℝ)
    (hπ0 : ∀ θ, 0 ≤ π θ) (hπ1 : ∑ θ, π θ = 1) (p : Θ → X → ℝ) (act : Θ → X → Prop)
    (H : TwoValued ρ p act) (probe : List Bool → X) (Q : ℕ) :
    Info.mutualInfo (fun te : Θ × (Fin Q → Bool) => π te.1 * pathProb (p te.1) probe Q [] te.2)
      ≤ Q * (Real.binEntropy (ρ + (1 - 2 * ρ) *
          ((∑ θ, π θ * accCount (p θ) probe (act θ) Q []) / Q)) - Real.binEntropy ρ) := by
  rw [mutualInfo_eq_Dw π hπ1 p (H.mem hρ0 hρ1) probe Q]
  have := Dw_le hρ0 hρ1 p act H probe Q [] π hπ0
  rw [hπ1, mul_one] at this
  exact this

open Classical in
/-- **Fano consequence, generic.** If `E[S] ≤ C ≤ Q/2` and every `near`-ball has prior mass
`≤ p₀ ∈ (0,1)`, a single output guess is near the truth with probability
`≤ (Q·[h(ρ + (1−2ρ)C/Q) − h(ρ)] + log 2) / log(1/p₀)`. -/
theorem fano_gen [DecidableEq Θ] {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (π : Θ → ℝ)
    (hπ0 : ∀ θ, 0 ≤ π θ) (hπ1 : ∑ θ, π θ = 1) (p : Θ → X → ℝ) (act : Θ → X → Prop)
    (H : TwoValued ρ p act) (probe : List Bool → X) (Q : ℕ) (C : ℝ)
    (hES : ∑ θ, π θ * accCount (p θ) probe (act θ) Q [] ≤ C) (hC : 2 * C ≤ Q)
    {Cc : Type*} (near : Θ → Cc → Prop) (out : (Fin Q → Bool) → Cc) (p₀ : ℝ) (hp0 : 0 < p₀)
    (hp1 : p₀ < 1) (hball : ∀ c, (∑ θ ∈ Finset.univ.filter (near · c), π θ) ≤ p₀) :
    (∑ te : Θ × (Fin Q → Bool),
        if near te.1 (out te.2) then π te.1 * pathProb (p te.1) probe Q [] te.2 else 0)
      ≤ (Q * (Real.binEntropy (ρ + (1 - 2 * ρ) * (C / Q)) - Real.binEntropy ρ) + Real.log 2) /
          Real.log (1 / p₀) := by
  have hp := H.mem hρ0 hρ1
  set q : Θ × (Fin Q → Bool) → ℝ := fun te => π te.1 * pathProb (p te.1) probe Q [] te.2
  have hq0 : ∀ te, 0 ≤ q te := fun te =>
    mul_nonneg (hπ0 _) (pathProb_nonneg probe (hp te.1) Q [] te.2)
  have hm1 : ∀ θ, Info.marg₁ q θ = π θ := fun θ => by
    simp [q, Info.marg₁, ← Finset.mul_sum, pathProb_sum probe (hp θ)]
  have hqs : ∑ te, q te = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [q, ← Finset.mul_sum, pathProb_sum probe (hp _), mul_one, hπ1]
  have hb : ∀ c, (∑ a ∈ Finset.univ.filter (near · c), Info.marg₁ q a) ≤ p₀ := fun c => by
    simp only [hm1]; exact hball c
  have hF := small_ball_fano q hq0 hqs near 1 (fun y _ => out y) p₀ hp0.le (by simpa using hp1) hb
  simp only at hF
  set P := ∑ te : Θ × (Fin Q → Bool), if near te.1 (out te.2) then q te else 0
  have hPe : (∑ ab : Θ × (Fin Q → Bool),
      if ab.1 ∈ Finset.univ.filter (fun a => ∃ _j : Fin 1, near a (out ab.2)) then q ab else 0)
      = P := Finset.sum_congr rfl fun te _ => by simp
  rw [hPe] at hF
  have hI := info_le_concave_gen hρ0 hρ1 π hπ0 hπ1 p act H probe Q
  -- monotonicity in `E[S]`
  set ES := ∑ θ, π θ * accCount (p θ) probe (act θ) Q []
  have hES0 : 0 ≤ ES := Finset.sum_nonneg fun θ _ =>
    mul_nonneg (hπ0 θ) (accCount_mem (p θ) (hp θ) probe (act θ) Q []).1
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hCQ : C / Q ≤ 1 / 2 := by
    rcases eq_or_lt_of_le hQ0 with h | h
    · rw [← h, div_zero]; norm_num
    · rw [div_le_iff₀ h]; linarith
  have hmono := phi_mono hρ0.le hρ1 (div_nonneg hES0 hQ0) (div_le_div_of_nonneg_right hES hQ0) hCQ
  have hI2 : Info.mutualInfo q ≤ Q * phi ρ (C / Q) :=
    hI.trans (mul_le_mul_of_nonneg_left hmono hQ0)
  have hΛ : 0 < Real.log (1 / p₀) := Real.log_pos (by rw [lt_div_iff₀ hp0]; linarith)
  have hh : Real.binEntropy P ≤ Real.log 2 := Real.binEntropy_le_log_two
  rw [Nat.cast_one, one_mul] at hF
  rw [le_div_iff₀ hΛ]
  unfold phi at hI2
  linarith

end Generic

end OracleBounds.GeneralPrior.MatchCap

/-! ### The one-face setting of `Face.lean` -/

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Fine : Type*} [Fintype Fine]

namespace Face

variable (F : Face E Fine)

open Classical in
/-- `E[S]`: the expected number of rounds whose probe reaches the target entry. -/
noncomputable def ES (probe : List Bool → Sph E) (Q : ℕ) : ℝ :=
  ∑ l, F.π l * accCount (F.pT l) probe (F.reach l) Q []

/-- The target entry's joint information `I(g; b₁..b_Q)` (environment fixed). -/
noncomputable def faceInfo (probe : List Bool → Sph E) (Q : ℕ) : ℝ :=
  Info.mutualInfo (fun te : Fine × (Fin Q → Bool) => F.π te.1 * pathProb (F.pT te.1) probe Q [] te.2)

lemma twoValued {ρ : ℝ} (hκ2 : ∀ s, F.κ s = if F.thr < s then 1 - ρ else ρ) :
    MatchCap.TwoValued ρ F.pT F.reach := by
  intro x
  by_cases hm : F.thr < F.m x.1
  · left; intro l
    simp only [pT, hκ2, if_pos (lt_max_of_lt_right hm)]
  · right; intro l
    simp only [pT, hκ2, reach, lt_max_iff, hm, or_false]
    congr

/-- **Theorem (★) (match-cap §1, locked §3 `info_le_concave`).** One target face, the others
summarised by the environment `m`; kernel K1(ρ) (`κ s = 1−ρ` above `thr`, `ρ` at or below);
any adaptive probe rule:
`I(g; b₁..b_Q) ≤ Q·[h(ρ + (1−2ρ)·E[S]/Q) − h(ρ)]`. -/
theorem info_le_concave {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ2 : ∀ s, F.κ s = if F.thr < s then 1 - ρ else ρ) (probe : List Bool → Sph E) (Q : ℕ) :
    F.faceInfo probe Q ≤
      Q * (Real.binEntropy (ρ + (1 - 2 * ρ) * (F.ES probe Q / Q)) - Real.binEntropy ρ) :=
  MatchCap.info_le_concave_gen hρ0 hρ1 F.π F.hπ0 F.hπ1 F.pT F.reach (F.twoValued hκ2) probe Q

open Classical in
/-- Fano for the uncapped one-face oracle: if `E[S] ≤ C ≤ Q/2`, one output guess `out` is within
`ε` of the target with probability `≤ (Q·[h(ρ + (1−2ρ)C/Q) − h(ρ)] + log 2)/log(1/p₀)`. -/
theorem face_fano [DecidableEq Fine] {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ2 : ∀ s, F.κ s = if F.thr < s then 1 - ρ else ρ) (probe : List Bool → Sph E) (Q : ℕ)
    (C : ℝ) (hES : F.ES probe Q ≤ C) (hC : 2 * C ≤ Q) (out : (Fin Q → Bool) → Sph E)
    (ε p₀ : ℝ) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hball : ∀ y : Sph E, (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - F.g l‖ ≤ ε), F.π l) ≤ p₀) :
    (∑ le : Fine × (Fin Q → Bool), if ‖(out le.2).1 - F.g le.1‖ ≤ ε then
        F.π le.1 * pathProb (F.pT le.1) probe Q [] le.2 else 0)
      ≤ (Q * (Real.binEntropy (ρ + (1 - 2 * ρ) * (C / Q)) - Real.binEntropy ρ) + Real.log 2) /
          Real.log (1 / p₀) :=
  MatchCap.fano_gen hρ0 hρ1 F.π F.hπ0 F.hπ1 F.pT F.reach (F.twoValued hκ2) probe Q C hES hC
    (fun l (y : Sph E) => ‖y.1 - F.g l‖ ≤ ε) out p₀ hp0 hp1 hball

/-! ### The per-person cap

The service counts, for the target entry, the rounds whose probe reaches it (it computes the match
before adding noise). While fewer than `Cp` such rounds have occurred it answers truthfully; from
then on it answers as if the entry were absent (the ghost response `pG`). The kernel now depends
on the history, so the transcript process is run on `X = List Bool` with `probe = id`. -/

/-- Number of earlier rounds (in history `h`) whose probe reached template value `l`. -/
noncomputable def reachCount (probe : List Bool → Sph E) (l : Fine) (h : List Bool) : ℕ :=
  open Classical in ∑ k ∈ Finset.range h.length, if F.reach l (probe (h.take k)) then 1 else 0

/-- Round at history `h` is a *truthful match* on the entry: it reaches `l` and the cap is not yet
exhausted. -/
def truthful (probe : List Bool → Sph E) (Cp : ℕ) (l : Fine) (h : List Bool) : Prop :=
  F.reach l (probe h) ∧ F.reachCount probe l h < Cp

open Classical in
/-- The capped oracle's answer probability at history `h`. -/
noncomputable def pCap (probe : List Bool → Sph E) (Cp : ℕ) (l : Fine) (h : List Bool) : ℝ :=
  if F.truthful probe Cp l h then F.pT l (probe h) else F.pG (probe h)

open Classical in
/-- `E[S]` for the capped oracle (expected number of truthful matches). -/
noncomputable def EScap (probe : List Bool → Sph E) (Cp Q : ℕ) : ℝ :=
  ∑ l, F.π l * accCount (F.pCap probe Cp l) id (F.truthful probe Cp l) Q []

/-- `I(g; b₁..b_Q)` for the capped oracle. -/
noncomputable def capInfo (probe : List Bool → Sph E) (Cp Q : ℕ) : ℝ :=
  Info.mutualInfo (fun te : Fine × (Fin Q → Bool) =>
    F.π te.1 * pathProb (F.pCap probe Cp te.1) id Q [] te.2)

lemma reachCount_append (probe : List Bool → Sph E) (l : Fine) (h : List Bool) (b : Bool) :
    F.reachCount probe l (h ++ [b]) =
      F.reachCount probe l h + (open Classical in if F.reach l (probe h) then 1 else 0) := by
  classical
  unfold reachCount
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ,
    List.take_left' rfl]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [List.take_append_of_le_length (Finset.mem_range.1 hk).le]

lemma twoValued_cap {ρ : ℝ} (hκ2 : ∀ s, F.κ s = if F.thr < s then 1 - ρ else ρ)
    (probe : List Bool → Sph E) (Cp : ℕ) :
    MatchCap.TwoValued ρ (F.pCap probe Cp) (F.truthful probe Cp) := by
  classical
  intro h
  by_cases hm : F.thr < F.m (probe h).1
  · left; intro l
    unfold pCap
    split_ifs
    · simp only [pT, hκ2, if_pos (lt_max_of_lt_right hm)]
    · simp only [pG, hκ2, if_pos hm]
  · right; intro l
    unfold pCap
    by_cases ht : F.truthful probe Cp l h
    · rw [if_pos ht, if_pos ht]
      simp only [pT, hκ2, if_pos (lt_max_of_lt_left ht.1)]
    · rw [if_neg ht, if_neg ht]
      simp only [pG, hκ2, if_neg hm]

lemma pCap_mem {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ2 : ∀ s, F.κ s = if F.thr < s then 1 - ρ else ρ) (probe : List Bool → Sph E) (Cp : ℕ) :
    ∀ l h, 0 ≤ F.pCap probe Cp l h ∧ F.pCap probe Cp l h ≤ 1 :=
  (F.twoValued_cap hκ2 probe Cp).mem hρ0 hρ1

open Classical in
/-- Pathwise, the cap holds: the expected number of truthful matches from history `h` is at most
`Cp − (matches so far)` (truncated). -/
lemma accCount_cap_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ2 : ∀ s, F.κ s = if F.thr < s then 1 - ρ else ρ) (probe : List Bool → Sph E) (Cp : ℕ)
    (l : Fine) : ∀ r h, accCount (F.pCap probe Cp l) id (F.truthful probe Cp l) r h ≤
      ((Cp - F.reachCount probe l h : ℕ) : ℝ) := by
  intro r
  induction r with
  | zero => intro h; simp [accCount]
  | succ r ih =>
    intro h
    have hp := F.pCap_mem hρ0 hρ1 hκ2 probe Cp l h
    simp only [accCount, id]
    have h1 := ih (h ++ [true])
    have h2 := ih (h ++ [false])
    rw [F.reachCount_append] at h1 h2
    set c := F.reachCount probe l h
    have key : (if F.truthful probe Cp l h then (1 : ℝ) else 0) +
        ((Cp - (c + if F.reach l (probe h) then 1 else 0) : ℕ) : ℝ) ≤ ((Cp - c : ℕ) : ℝ) := by
      by_cases hr : F.reach l (probe h)
      · by_cases hc : c < Cp
        · rw [if_pos ⟨hr, hc⟩, if_pos hr, Nat.cast_sub (by omega), Nat.cast_sub hc.le]
          push_cast; linarith
        · rw [if_neg (fun ht => hc ht.2), if_pos hr]
          rw [show Cp - (c + 1) = 0 by omega, show Cp - c = 0 by omega]; simp
      · rw [if_neg (fun ht => hr ht.1), if_neg hr]; simp
    set B := ((Cp - (c + if F.reach l (probe h) then 1 else 0) : ℕ) : ℝ)
    have hm1 := mul_le_mul_of_nonneg_left h1 hp.1
    have hm2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - F.pCap probe Cp l h by linarith [hp.2])
    by_cases ht : F.truthful probe Cp l h <;> simp only [ht, if_true, if_false] at key ⊢ <;>
    nlinarith [mul_le_mul_of_nonneg_left h1 hp.1,
      mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - F.pCap probe Cp l h by linarith [hp.2])]

/-- Under the cap, `E[S] ≤ Cp`. -/
lemma EScap_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ2 : ∀ s, F.κ s = if F.thr < s then 1 - ρ else ρ) (probe : List Bool → Sph E) (Cp Q : ℕ) :
    F.EScap probe Cp Q ≤ Cp := by
  classical
  unfold EScap
  calc ∑ l, F.π l * accCount (F.pCap probe Cp l) id (F.truthful probe Cp l) Q []
      ≤ ∑ l, F.π l * (Cp : ℝ) := Finset.sum_le_sum fun l _ => by
        refine mul_le_mul_of_nonneg_left ?_ (F.hπ0 l)
        have := F.accCount_cap_le hρ0 hρ1 hκ2 probe Cp l Q []
        simpa [reachCount] using this
    _ = Cp := by rw [← Finset.sum_mul, F.hπ1, one_mul]

/-- **(★) for the capped oracle**: `I(g; b) ≤ Q·[h(ρ + (1−2ρ)·E[S]/Q) − h(ρ)]` with `S` the number
of truthful matches. -/
theorem capInfo_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ2 : ∀ s, F.κ s = if F.thr < s then 1 - ρ else ρ) (probe : List Bool → Sph E) (Cp Q : ℕ) :
    F.capInfo probe Cp Q ≤
      Q * (Real.binEntropy (ρ + (1 - 2 * ρ) * (F.EScap probe Cp Q / Q)) - Real.binEntropy ρ) :=
  MatchCap.info_le_concave_gen hρ0 hρ1 F.π F.hπ0 F.hπ1 (F.pCap probe Cp) (F.truthful probe Cp)
    (F.twoValued_cap hκ2 probe Cp) id Q

open Classical in
/-- **`match_cap_fano` (match-cap §1, Fano bullet).** Under a per-person cap `Cp` with
`2·Cp ≤ Q`, a single output guess `out` (a function of the transcript) is within `ε` of the target
with probability at most `(Q·[h(ρ + (1−2ρ)·Cp/Q) − h(ρ)] + log 2) / log(1/p₀)`, where `p₀ ∈ (0,1)`
bounds the prior mass of every `ε`-ball (`π` is the prior *given* the launch region `C`, so
`log(1/p₀) = Λ_C`). -/
theorem match_cap_fano [DecidableEq Fine] {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ2 : ∀ s, F.κ s = if F.thr < s then 1 - ρ else ρ) (probe : List Bool → Sph E) (Cp Q : ℕ)
    (hCp : 2 * Cp ≤ Q) (out : (Fin Q → Bool) → Sph E) (ε p₀ : ℝ) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hball : ∀ y : Sph E, (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - F.g l‖ ≤ ε), F.π l) ≤ p₀) :
    (∑ le : Fine × (Fin Q → Bool), if ‖(out le.2).1 - F.g le.1‖ ≤ ε then
        F.π le.1 * pathProb (F.pCap probe Cp le.1) id Q [] le.2 else 0)
      ≤ (Q * (Real.binEntropy (ρ + (1 - 2 * ρ) * ((Cp : ℝ) / Q)) - Real.binEntropy ρ) +
          Real.log 2) / Real.log (1 / p₀) :=
  MatchCap.fano_gen hρ0 hρ1 F.π F.hπ0 F.hπ1 (F.pCap probe Cp) (F.truthful probe Cp)
    (F.twoValued_cap hκ2 probe Cp) id Q Cp (F.EScap_le hρ0 hρ1 hκ2 probe Cp Q)
    (by exact_mod_cast hCp) (fun l (y : Sph E) => ‖y.1 - F.g l‖ ≤ ε) out p₀ hp0 hp1 hball

end Face

/-! ### The gallery, other entries conditioned on -/

namespace Gallery

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Fine] (G : Gallery E ι Fine)

/-- `I(Vᵢ; b₁..b_Q | V₋ᵢ)`: the information about entry `i` given the other entries, i.e.
`Σ_{γ'} P[V₋ᵢ = γ'] · I(Vᵢ; b | V₋ᵢ = γ')` with the gallery's own response. -/
noncomputable def condInfo [Nonempty ι] (i : ι) (probe : List Bool → Sph E) (Q : ℕ) : ℝ :=
  ∑ γ' : {j : ι // j ≠ i} → Fine, (∏ j : {x : ι // x ≠ i}, G.π j.1 (γ' j)) *
    Info.mutualInfo (fun te : Fine × (Fin Q → Bool) =>
      G.π i te.1 * pathProb (G.resp ((Equiv.funSplitAt i Fine).symm (te.1, γ'))) probe Q [] te.2)

open Classical in
/-- `E[S]` for entry `i`: expected number of rounds whose probe reaches `Vᵢ`, over
`V ∼ ∏ⱼπⱼ` and the transcript. -/
noncomputable def ESi [Nonempty ι] (i : ι) (probe : List Bool → Sph E) (Q : ℕ) : ℝ :=
  ∑ v, G.prior v * accCount (G.resp v) probe (G.reachG (v i)) Q []

open Classical in
/-- **Theorem (★), gallery form.** `I(Vᵢ; b | V₋ᵢ) ≤ Q·[h(ρ + (1−2ρ)·E[S]/Q) − h(ρ)]`, kernel
K1(ρ), any adaptive probe rule. (Per-environment (★) via `Face.info_le_concave`, then Jensen over
the other entries.) -/
theorem gallery_info_le_concave [Nonempty ι] [Nonempty Fine] {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1 / 2) (hκ2 : ∀ s, G.κ s = if G.thr < s then 1 - ρ else ρ) (i : ι)
    (probe : List Bool → Sph E) (Q : ℕ) :
    G.condInfo i probe Q ≤
      Q * (Real.binEntropy (ρ + (1 - 2 * ρ) * (G.ESi i probe Q / Q)) - Real.binEntropy ρ) := by
  obtain ⟨l₀⟩ := (inferInstance : Nonempty Fine)
  set e := Equiv.funSplitAt i Fine with he
  set W : ({j : ι // j ≠ i} → Fine) → ℝ := fun γ' => ∏ j : {x : ι // x ≠ i}, G.π j.1 (γ' j)
    with hW
  have hW0 : ∀ γ', 0 ≤ W γ' := fun γ' => Finset.prod_nonneg fun j _ => G.hπ0 j.1 _
  have hW1 : ∑ γ', W γ' = 1 := by
    simp only [hW]
    rw [← Fintype.prod_sum (fun (j : {x : ι // x ≠ i}) x => G.π j.1 x)]
    exact Finset.prod_eq_one fun j _ => G.hπ1 j.1
  set F : ({j : ι // j ≠ i} → Fine) → Face E Fine := fun γ' => G.face i (e.symm (l₀, γ'))
  have hresp : ∀ γ' l, G.resp (e.symm (l, γ')) = (F γ').pT l :=
    fun γ' l => funext fun x => G.resp_eq_pT i l l₀ γ' x
  have hκF : ∀ γ', ∀ s, (F γ').κ s = if (F γ').thr < s then 1 - ρ else ρ := fun γ' => hκ2
  -- per-environment bound
  have hface : ∀ γ', Info.mutualInfo (fun te : Fine × (Fin Q → Bool) =>
      G.π i te.1 * pathProb (G.resp (e.symm (te.1, γ'))) probe Q [] te.2) ≤
        MatchCap.persp ρ Q ((F γ').ES probe Q) := by
    intro γ'
    have := (F γ').info_le_concave hρ0 hρ1 (hκF γ') probe Q
    simp only [Face.faceInfo] at this
    simp only [hresp]
    exact this
  have hES : ∀ γ', 0 ≤ (F γ').ES probe Q ∧ (F γ').ES probe Q ≤ Q := by
    intro γ'
    have hb := fun l => accCount_mem ((F γ').pT l) ((F γ').pT_mem l) probe ((F γ').reach l) Q []
    constructor
    · exact Finset.sum_nonneg fun l _ => mul_nonneg ((F γ').hπ0 l) (hb l).1
    · calc (F γ').ES probe Q ≤ ∑ l, (F γ').π l * (Q : ℝ) :=
            Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hb l).2 ((F γ').hπ0 l)
        _ = Q := by rw [← Finset.sum_mul, (F γ').hπ1, one_mul]
  -- reindex `E[S]`
  have hre : G.ESi i probe Q = ∑ γ', W γ' * (F γ').ES probe Q := by
    unfold ESi
    rw [Fintype.sum_equiv e _ (fun p => G.prior (e.symm p) *
        accCount (G.resp (e.symm p)) probe (G.reachG (e.symm p i)) Q [])
      (fun v => by simp)]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ' _ => ?_
    unfold Face.ES
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hi : e.symm (l, γ') i = l := by simp [he, Equiv.funSplitAt_symm_apply]
    rw [hi, hresp, prior, G.prod_split i l γ']
    rw [mul_comm (G.π i l), mul_assoc]
    rfl
  unfold condInfo
  calc ∑ γ', W γ' * Info.mutualInfo (fun te : Fine × (Fin Q → Bool) =>
        G.π i te.1 * pathProb (G.resp (e.symm (te.1, γ'))) probe Q [] te.2)
      ≤ ∑ γ', W γ' * MatchCap.persp ρ Q ((F γ').ES probe Q) :=
        Finset.sum_le_sum fun γ' _ => mul_le_mul_of_nonneg_left (hface γ') (hW0 γ')
    _ = ∑ γ', MatchCap.persp ρ (W γ' * Q) (W γ' * (F γ').ES probe Q) :=
        Finset.sum_congr rfl fun γ' _ => (MatchCap.persp_smul (hW0 γ')).symm
    _ ≤ MatchCap.persp ρ (∑ γ', W γ' * Q) (∑ γ', W γ' * (F γ').ES probe Q) :=
        MatchCap.persp_sum hρ0.le hρ1 _ _ _ fun γ' _ =>
          ⟨mul_nonneg (hW0 γ') (hES γ').1, mul_le_mul_of_nonneg_left (hES γ').2 (hW0 γ')⟩
    _ = _ := by
        rw [← Finset.sum_mul, hW1, one_mul, ← hre]; rfl

end Gallery

end OracleBounds.GeneralPrior
