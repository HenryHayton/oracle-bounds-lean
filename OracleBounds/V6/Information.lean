import OracleBounds.V6.Wave1

/-!
# Information layer of v6 (§§5, 6, 8, 11): the problem-specific steps

**What is and is not checked here.** The information-theoretic *inputs* are standard results:
list-Fano (Lemma 5.3, [13]), non-negativity of mutual information, the chain rule (Prop 5.2), and
the stopped information bound with switching reference kernels (N1 Lemma 4.2, applied in Thm 5.1).
Formalising mutual information of an adaptive process in Lean would take a lot of machinery, so:

* `list_fano`, `mutualInfo_superadditive` (chain rule + independence) and `mutualInfo_nonneg` are
  stated for finite joint pmfs and proved from the pointwise Gibbs inequality `mul_log_div_ge_sub`
  (list-Fano via the log-sum inequality `log_sum_ineq`; superadditivity as a KL divergence against
  the reference `q(y) Πᵢ q(vᵢ | y)`). `OracleBounds.V6` has no `sorry`s.
* Everything *after* those inputs is proved: averaging conditional Fano (Jensen), the Thm 6.1 (4)
  summation with the convexity repair (F7), Cor 6.2 in corrected form (F1, F10, F13), the Cor 8.1
  second-branch contradiction and the `ε*` unwinding, eq. (5), the Markov step of Prop 8.3 and the
  Cor 11.2 constant. The inputs enter these theorems as explicitly named hypotheses
  (`hFano`, `hInfo`, …), so a reader can see exactly which cited fact each one stands for.

Not formalised: that v6's Thm 5.1 bound `I(V⁽¹ᐟⁿ⁾; b | U, W) ≤ β*·E[C_Q] + β₀Q` follows from
N1 Lemma 4.2 (v6 applies that lemma outside its `[ρ, 1−ρ]` range hypothesis; v7 request 8).
-/

namespace OracleBounds.V6.Info

open Real Finset

/-! ### Standard inputs (proved) -/

section literature

variable {α β : Type*} [Fintype α] [Fintype β]

/-- First marginal of a joint pmf. -/
noncomputable def marg₁ (q : α × β → ℝ) (a : α) : ℝ := ∑ b, q (a, b)

/-- Second marginal of a joint pmf. -/
noncomputable def marg₂ (q : α × β → ℝ) (b : β) : ℝ := ∑ a, q (a, b)

/-- Mutual information (nats) of a finite joint pmf, `∑ q log(q / (q₁ q₂))` with `0 log 0 = 0`. -/
noncomputable def mutualInfo (q : α × β → ℝ) : ℝ :=
  ∑ ab, q ab * Real.log (q ab / (marg₁ q ab.1 * marg₂ q ab.2))

/-- Gibbs, pointwise: `P log(P/R) ≥ P − R` for `P, R ≥ 0` with `R = 0 → P = 0`. -/
lemma mul_log_div_ge_sub {P R : ℝ} (hP : 0 ≤ P) (hR : 0 ≤ R) (hac : R = 0 → P = 0) :
    P - R ≤ P * Real.log (P / R) := by
  rcases eq_or_lt_of_le hP with h0 | h0
  · rw [← h0]; simp; exact hR
  have hR0 : 0 < R := lt_of_le_of_ne hR (fun h => h0.ne' (hac h.symm))
  have := Real.one_sub_inv_le_log_of_pos (div_pos h0 hR0)
  rw [inv_div] at this
  have e : P * (1 - R / P) = P - R := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left this h0.le]

/-- Mutual information is non-negative (Gibbs). Proved. -/
theorem mutualInfo_nonneg (q : α × β → ℝ) (hq : ∀ ab, 0 ≤ q ab) (hsum : ∑ ab, q ab = 1) :
    0 ≤ mutualInfo q := by
  have hm1 : ∀ a, 0 ≤ marg₁ q a := fun a => Finset.sum_nonneg fun b _ => hq (a, b)
  have hm2 : ∀ b, 0 ≤ marg₂ q b := fun b => Finset.sum_nonneg fun a _ => hq (a, b)
  have hle1 : ∀ ab : α × β, q ab ≤ marg₁ q ab.1 := fun ab =>
    Finset.single_le_sum (f := fun b => q (ab.1, b)) (fun b _ => hq _) (Finset.mem_univ ab.2)
  have hle2 : ∀ ab : α × β, q ab ≤ marg₂ q ab.2 := fun ab =>
    Finset.single_le_sum (f := fun a => q (a, ab.2)) (fun a _ => hq _) (Finset.mem_univ ab.1)
  have hpt : ∀ ab : α × β, q ab - marg₁ q ab.1 * marg₂ q ab.2 ≤
      q ab * Real.log (q ab / (marg₁ q ab.1 * marg₂ q ab.2)) := fun ab =>
    mul_log_div_ge_sub (hq ab) (mul_nonneg (hm1 _) (hm2 _)) (fun h0 => by
      rcases mul_eq_zero.1 h0 with h | h
      · exact le_antisymm (h ▸ hle1 ab) (hq ab)
      · exact le_antisymm (h ▸ hle2 ab) (hq ab))
  have hs1 : ∑ a, marg₁ q a = 1 := by
    rw [← hsum, Fintype.sum_prod_type]; rfl
  have hs2 : ∑ b, marg₂ q b = 1 := by
    rw [← hsum, Fintype.sum_prod_type, Finset.sum_comm]; rfl
  have hprod : ∑ ab : α × β, marg₁ q ab.1 * marg₂ q ab.2 = 1 := by
    rw [Fintype.sum_prod_type]; simp only [← Finset.mul_sum, ← Finset.sum_mul, hs2, hs1, mul_one]
  have := Finset.sum_le_sum fun ab (_ : ab ∈ Finset.univ) => hpt ab
  rw [Finset.sum_sub_distrib, hsum, hprod, sub_self] at this
  exact this

/-- Log-sum inequality (grouped Gibbs): `Σ aᵢ log(aᵢ/bᵢ) ≥ A log(A/B)`. -/
lemma log_sum_ineq {γ : Type*} (s : Finset γ) (a b : γ → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hac : ∀ i ∈ s, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
  set A := ∑ i ∈ s, a i
  set B := ∑ i ∈ s, b i
  have hA : 0 ≤ A := Finset.sum_nonneg ha
  have hB : 0 ≤ B := Finset.sum_nonneg hb
  rcases eq_or_lt_of_le hA with hA0 | hA0
  · rw [← hA0, zero_mul]
    have hz : ∀ i ∈ s, a i = 0 := (Finset.sum_eq_zero_iff_of_nonneg ha).1 hA0.symm
    rw [Finset.sum_eq_zero fun i hi => by rw [hz i hi, zero_mul]]
  have hB0 : 0 < B := by
    rcases eq_or_lt_of_le hB with h | h
    · exfalso
      have hz : ∀ i ∈ s, b i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hb).1 h.symm
      have : A = 0 := Finset.sum_eq_zero fun i hi => hac i hi (hz i hi)
      linarith
    · exact h
  have hpt : ∀ i ∈ s, a i * Real.log (A / B) + (a i - b i * (A / B)) ≤ a i * Real.log (a i / b i) := by
    intro i hi
    rcases eq_or_lt_of_le (ha i hi) with h0 | h0
    · rw [← h0]; simp only [zero_mul, zero_sub, zero_add]
      exact neg_nonpos.2 (mul_nonneg (hb i hi) (div_nonneg hA hB))
    have hbi : 0 < b i := lt_of_le_of_ne (hb i hi) (fun h => h0.ne' (hac i hi h.symm))
    have hx : 0 < a i / b i / (A / B) := by positivity
    have h1 := Real.one_sub_inv_le_log_of_pos hx
    rw [Real.log_div (by positivity) (by positivity), inv_div] at h1
    have e : a i * (1 - A / B / (a i / b i)) = a i - b i * (A / B) := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 h0.le]
  have := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_mul] at this
  have e2 : A - B * (A / B) = 0 := by field_simp; ring
  linarith

lemma le_marg₁ {q : α × β → ℝ} (hq : ∀ ab, 0 ≤ q ab) (ab : α × β) : q ab ≤ marg₁ q ab.1 :=
  Finset.single_le_sum (f := fun b => q (ab.1, b)) (fun _ _ => hq _) (Finset.mem_univ ab.2)

lemma le_marg₂ {q : α × β → ℝ} (hq : ∀ ab, 0 ≤ q ab) (ab : α × β) : q ab ≤ marg₂ q ab.2 :=
  Finset.single_le_sum (f := fun a => q (a, ab.2)) (fun _ _ => hq _) (Finset.mem_univ ab.1)

lemma sum_marg₂ (q : α × β → ℝ) : ∑ b, marg₂ q b = ∑ ab, q ab := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl

lemma sum_marg_mul (q : α × β → ℝ) (hsum : ∑ ab, q ab = 1) :
    ∑ ab : α × β, marg₁ q ab.1 * marg₂ q ab.2 = 1 := by
  have hs1 : ∑ a, marg₁ q a = 1 := by rw [← hsum, Fintype.sum_prod_type]; rfl
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, sum_marg₂, hsum, hs1, mul_one]

/-- **Superadditivity for independent inputs.** If `V = (Vᵢ)ᵢ` is uniform on `ι → Fine` (so the
coordinates are independent) and `Y | V = v ~ P v`, then `Σᵢ I(Vᵢ; Y) ≤ I(V; Y)`. Standard: chain rule
`I(V;Y) = Σᵢ I(Vᵢ; Y | V₍<ᵢ₎)` and, by independence, `I(Vᵢ; Y | V₍<ᵢ₎) = I(Vᵢ; Y, V₍<ᵢ₎) ≥ I(Vᵢ; Y)`
(Cover–Thomas Thm 2.5.2). Proved directly: `I(V;Y) − Σᵢ I(Vᵢ;Y) = Σ q log(q/R)` with
`R(v, y) = q(y) Πᵢ q(vᵢ | y)` of total mass `≤ 1`, which is `≥ 0` by Gibbs. -/
theorem mutualInfo_superadditive {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine]
    [DecidableEq Fine] (P : (ι → Fine) → β → ℝ) (hP : ∀ v b, 0 ≤ P v b) (hP1 : ∀ v, ∑ b, P v b = 1) :
    ∑ i, mutualInfo (fun lb : Fine × β => ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = lb.1),
        (1 / (Fintype.card (ι → Fine) : ℝ)) * P v lb.2)
      ≤ mutualInfo (fun vb : (ι → Fine) × β => (1 / (Fintype.card (ι → Fine) : ℝ)) * P vb.1 vb.2) := by
  rcases isEmpty_or_nonempty (ι → Fine) with hE | hNE
  · simp [mutualInfo]
  set M : ℝ := ((Fintype.card (ι → Fine) : ℕ) : ℝ) with hM
  set c : ℝ := 1 / M with hc
  set F : ℝ := ((Fintype.card Fine : ℕ) : ℝ) with hF
  have hMpos : 0 < M := by simp only [hM]; exact_mod_cast Fintype.card_pos
  have hcpos : 0 < c := by positivity
  have hMF : M = F ^ Fintype.card ι := by simp only [hM, hF, Fintype.card_fun]; push_cast; rfl
  set q : (ι → Fine) × β → ℝ := fun vb => c * P vb.1 vb.2 with hqdef
  set qi : ι → Fine × β → ℝ := fun i lb =>
    ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = lb.1), c * P v lb.2 with hqidef
  show ∑ i, mutualInfo (qi i) ≤ mutualInfo q
  have hq0 : ∀ vb, 0 ≤ q vb := fun vb => mul_nonneg hcpos.le (hP _ _)
  have hqi0 : ∀ i lb, 0 ≤ qi i lb := fun i lb => Finset.sum_nonneg fun v _ => mul_nonneg hcpos.le (hP _ _)
  set b : β → ℝ := marg₂ q with hbdef
  have hb0 : ∀ y, 0 ≤ b y := fun y => Finset.sum_nonneg fun _ _ => hq0 _
  have hm1 : ∀ v, marg₁ q v = c := fun v => by
    simp only [marg₁, q, ← Finset.mul_sum, hP1, mul_one]
  have hsumq : ∑ vb, q vb = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [q, ← Finset.mul_sum, hP1, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hc, ← hM]; field_simp
  have hsumb : ∑ y, b y = 1 := by
    rw [← hsumq, Fintype.sum_prod_type, Finset.sum_comm]; rfl
  have hmi2 : ∀ i y, marg₂ (qi i) y = b y := fun i y => by
    simp only [marg₂, qi, b]
    exact Finset.sum_fiberwise (Finset.univ) (fun v : ι → Fine => v i) (fun v => c * P v y)
  have hmi1 : ∀ i l, marg₁ (qi i) l = 1 / F := fun i l => by
    have hFpos : 0 < Fintype.card Fine := Fintype.card_pos_iff.2 ⟨l⟩
    have hn : Fintype.card ι ≠ 0 := (Fintype.card_pos_iff.2 ⟨i⟩).ne'
    simp only [marg₁, qi]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hP1, mul_one, Finset.sum_const, nsmul_eq_mul]
    have hcard := Fintype.card_filter_piFinset_const (Finset.univ : Finset Fine) i l
    simp only [Fintype.piFinset_univ, Finset.mem_univ, if_true, Finset.card_univ] at hcard
    rw [hcard, hc, hMF]
    have hF0 : F ≠ 0 := by simp only [hF]; exact_mod_cast hFpos.ne'
    rw [← pow_sub_one_mul hn F]
    push_cast
    field_simp
    rfl
  set R : (ι → Fine) × β → ℝ := fun vb =>
    c * b vb.2 * ∏ i, (qi i (vb.1 i, vb.2) / (1 / F * b vb.2)) with hRdef
  have hqi_ge : ∀ i (vb : (ι → Fine) × β), q vb ≤ qi i (vb.1 i, vb.2) := fun i vb =>
    Finset.single_le_sum (f := fun v => c * P v vb.2) (fun v _ => mul_nonneg hcpos.le (hP _ _))
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
  have hqb : ∀ vb : (ι → Fine) × β, q vb ≤ b vb.2 := fun vb =>
    Finset.single_le_sum (f := fun v => q (v, vb.2)) (fun v _ => hq0 _) (Finset.mem_univ vb.1)
  -- pointwise Gibbs against the product reference `R`
  have hpt : ∀ vb : (ι → Fine) × β, q vb - R vb ≤
      q vb * Real.log (q vb / (c * b vb.2)) -
        ∑ i, q vb * Real.log (qi i (vb.1 i, vb.2) / (1 / F * b vb.2)) := by
    intro vb
    rcases eq_or_lt_of_le (hq0 vb) with h0 | h0
    · rw [← h0]
      simp only [zero_mul, Finset.sum_const_zero, sub_zero, zero_sub, neg_nonpos]
      have hF0 : 0 ≤ F := by simp only [hF]; positivity
      exact mul_nonneg (mul_nonneg hcpos.le (hb0 _))
        (Finset.prod_nonneg fun i _ => div_nonneg (hqi0 _ _) (mul_nonneg (by positivity) (hb0 _)))
    have hbpos : 0 < b vb.2 := lt_of_lt_of_le h0 (hqb vb)
    have hX : ∀ i, 0 < qi i (vb.1 i, vb.2) / (1 / F * b vb.2) := fun i => by
      have : (0 : ℝ) < F := by simp only [hF]; exact_mod_cast Fintype.card_pos_iff.2 ⟨vb.1 i⟩
      exact div_pos (lt_of_lt_of_le h0 (hqi_ge i vb)) (by positivity)
    have hRpos : 0 < R vb := mul_pos (mul_pos hcpos hbpos) (Finset.prod_pos fun i _ => hX i)
    have g := mul_log_div_ge_sub (hq0 vb) hRpos.le (fun h => absurd h hRpos.ne')
    rw [Real.log_div h0.ne' hRpos.ne'] at g
    rw [Real.log_div h0.ne' (by positivity), ← Finset.mul_sum]
    have eR : Real.log (R vb) = Real.log (c * b vb.2) +
        ∑ i, Real.log (qi i (vb.1 i, vb.2) / (1 / F * b vb.2)) := by
      simp only [R]
      rw [Real.log_mul (by positivity) (Finset.prod_pos fun i _ => hX i).ne',
        Real.log_prod fun i _ => (hX i).ne']
    rw [eR] at g
    linarith
  -- the reference has total mass at most one
  have hR1 : ∑ vb, R vb ≤ 1 := by
    rw [← hsumb, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_le_sum fun y _ => ?_
    simp only [R, ← Finset.mul_sum]
    rw [← Fintype.prod_sum (fun i l => qi i (l, y) / (1 / F * b y))]
    have hi : ∀ i, ∑ l, qi i (l, y) / (1 / F * b y) = b y / (1 / F * b y) := fun i => by
      rw [← Finset.sum_div, ← hmi2 i y]; rfl
    simp only [hi, Finset.prod_const, Finset.card_univ]
    rcases eq_or_lt_of_le (hb0 y) with h0 | h0
    · rw [← h0]; simp
    obtain ⟨v⟩ := hNE
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
    · rw [hc, hMF]; simp
    have hFpos : (0 : ℝ) < F := by simp only [hF]; exact_mod_cast Fintype.card_pos_iff.2 ⟨v i⟩
    have e : b y / (1 / F * b y) = F := by field_simp
    rw [e, hc, hMF]
    exact le_of_eq (by field_simp)
  -- assemble: `I(V;Y) − Σᵢ I(Vᵢ;Y) = Σ (pointwise terms) ≥ Σ q − Σ R ≥ 0`
  have hIi : ∀ i, mutualInfo (qi i) =
      ∑ vb : (ι → Fine) × β, q vb * Real.log (qi i (vb.1 i, vb.2) / (1 / F * b vb.2)) := fun i => by
    simp only [mutualInfo, hmi1, hmi2]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm (s := (Finset.univ : Finset Fine)),
      Finset.sum_comm (s := (Finset.univ : Finset (ι → Fine)))]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [qi, Finset.sum_mul]
    rw [← Finset.sum_fiberwise Finset.univ (fun v : ι → Fine => v i)]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun v hv => ?_
    rw [(Finset.mem_filter.1 hv).2]
  have hI : mutualInfo q = ∑ vb : (ι → Fine) × β, q vb * Real.log (q vb / (c * b vb.2)) := by
    simp only [mutualInfo, hm1]; rfl
  rw [Finset.sum_congr rfl fun i _ => hIi i, Finset.sum_comm, hI, ← sub_nonneg, ← Finset.sum_sub_distrib]
  have := Finset.sum_le_sum fun vb (_ : vb ∈ Finset.univ) => hpt vb
  rw [Finset.sum_sub_distrib, hsumq] at this
  linarith

/-- **Lemma 5.3 (list Fano, entropy-tight).** `V` uniform on `[N]`, a list `L(Y)` of size `≤ κ₀ < N`,
`P = P[V ∈ L(Y)]`. Then `I(V;Y) ≥ P·log(N/κ₀) − h(P)`. Standard ([13]; Cover–Thomas §2.10).
Proved: log-sum over `{V ∈ L(Y)}` and its complement, with `P[V ∈ L(Y)] ≤ κ₀/N` under `q₁ × q₂`. -/
theorem list_fano {A : Type*} [Fintype A] [DecidableEq A] (q : A × β → ℝ) (hq : ∀ ab, 0 ≤ q ab)
    (hsum : ∑ ab, q ab = 1) (hunif : ∀ v, marg₁ q v = 1 / Fintype.card A) (L : β → Finset A)
    (κ₀ : ℕ) (hκ₀ : 0 < κ₀) (hκN : κ₀ < Fintype.card A) (hL : ∀ y, (L y).card ≤ κ₀) :
    let P := ∑ ab, if ab.1 ∈ L ab.2 then q ab else 0
    P * Real.log (Fintype.card A / κ₀) - Real.binEntropy P ≤ mutualInfo q := by
  intro P
  set N : ℝ := ((Fintype.card A : ℕ) : ℝ) with hN
  have hNpos : (0 : ℝ) < N := by
    have : 0 < Fintype.card A := lt_of_le_of_lt (Nat.zero_le _) hκN
    simp only [hN]; exact_mod_cast this
  have hκpos : (0 : ℝ) < κ₀ := by exact_mod_cast hκ₀
  set m : A × β → ℝ := fun ab => marg₁ q ab.1 * marg₂ q ab.2 with hm
  have hm0 : ∀ ab, 0 ≤ m ab := fun ab =>
    mul_nonneg (Finset.sum_nonneg fun _ _ => hq _) (Finset.sum_nonneg fun _ _ => hq _)
  have hac : ∀ ab, m ab = 0 → q ab = 0 := fun ab h0 => by
    rcases mul_eq_zero.1 h0 with h | h
    · exact le_antisymm (h ▸ le_marg₁ hq ab) (hq ab)
    · exact le_antisymm (h ▸ le_marg₂ hq ab) (hq ab)
  set S := Finset.univ.filter (fun ab : A × β => ab.1 ∈ L ab.2)
  set Sc := Finset.univ.filter (fun ab : A × β => ¬ ab.1 ∈ L ab.2)
  have hPS : P = ∑ ab ∈ S, q ab := (Finset.sum_filter _ _).symm
  have hPc : 1 - P = ∑ ab ∈ Sc, q ab := by
    rw [hPS, ← hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ab : A × β => ab.1 ∈ L ab.2)]
    ring
  set P₀ := ∑ ab ∈ S, m ab
  have hP₀c : 1 - P₀ = ∑ ab ∈ Sc, m ab := by
    rw [← sum_marg_mul q hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun ab : A × β => ab.1 ∈ L ab.2)]
    ring
  -- `P₀ ≤ κ₀ / N`
  have hP₀ : P₀ ≤ κ₀ / N := by
    have e : P₀ = ∑ b, marg₂ q b * ((L b).card / N) := by
      simp only [P₀, S, Finset.sum_filter, m, hunif, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have : (Finset.univ.filter fun a => a ∈ L b) = L b := by ext; simp
      rw [this]; ring
    rw [e]
    calc ∑ b, marg₂ q b * ((L b).card / N) ≤ ∑ b, marg₂ q b * (κ₀ / N) :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (by exact_mod_cast hL b) hNpos.le)
            (Finset.sum_nonneg fun _ _ => hq _)
      _ = κ₀ / N := by rw [← Finset.sum_mul, sum_marg₂, hsum, one_mul]
  have h1 := log_sum_ineq S q m (fun i _ => hq i) (fun i _ => hm0 i) (fun i _ => hac i)
  have h2 := log_sum_ineq Sc q m (fun i _ => hq i) (fun i _ => hm0 i) (fun i _ => hac i)
  rw [← hPS] at h1
  rw [← hPc, ← hP₀c] at h2
  have hsplit : mutualInfo q = ∑ ab ∈ S, q ab * Real.log (q ab / m ab) +
      ∑ ab ∈ Sc, q ab * Real.log (q ab / m ab) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hP0 : 0 ≤ P := hPS ▸ Finset.sum_nonneg fun i _ => hq i
  have hP1 : 0 ≤ 1 - P := hPc ▸ Finset.sum_nonneg fun i _ => hq i
  have hP₀0 : 0 ≤ P₀ := Finset.sum_nonneg fun i _ => hm0 i
  have hP₀1 : 0 ≤ 1 - P₀ := hP₀c ▸ Finset.sum_nonneg fun i _ => hm0 i
  -- the `Z = 0` term: `(1-P) log((1-P)/(1-P₀)) ≥ (1-P) log(1-P)`
  have k2 : (1 - P) * Real.log (1 - P) ≤ (1 - P) * Real.log ((1 - P) / (1 - P₀)) := by
    rcases eq_or_lt_of_le hP1 with h | h
    · rw [← h]; simp
    have hq0 : 0 < 1 - P₀ := by
      rcases eq_or_lt_of_le hP₀1 with h' | h'
      · exfalso
        have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hm0 i).1 (hP₀c ▸ h'.symm)
        have : 1 - P = 0 := hPc ▸ Finset.sum_eq_zero fun i hi => hac i (hz i hi)
        linarith
      · exact h'
    rw [Real.log_div h.ne' hq0.ne']
    have : Real.log (1 - P₀) ≤ 0 := Real.log_nonpos hq0.le (by linarith)
    nlinarith
  -- the `Z = 1` term: `P log(P/P₀) ≥ P log P + P log(N/κ₀)`
  have k1 : P * Real.log P + P * Real.log (N / κ₀) ≤ P * Real.log (P / P₀) := by
    rcases eq_or_lt_of_le hP0 with h | h
    · rw [← h]; simp
    have hq0 : 0 < P₀ := by
      rcases eq_or_lt_of_le hP₀0 with h' | h'
      · exfalso
        have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hm0 i).1 h'.symm
        have : P = 0 := hPS ▸ Finset.sum_eq_zero fun i hi => hac i (hz i hi)
        linarith
      · exact h'
    rw [Real.log_div h.ne' hq0.ne']
    have : Real.log (N / κ₀) ≤ -Real.log P₀ := by
      rw [← Real.log_inv, ← inv_div]
      exact Real.log_le_log (by positivity) ((inv_le_inv₀ (by positivity) hq0).2 hP₀)
    nlinarith
  have hH : Real.binEntropy P = -(P * Real.log P) - (1 - P) * Real.log (1 - P) := by
    simp only [Real.binEntropy, Real.log_inv]; ring
  rw [hH, hsplit]
  linarith

end literature

/-! ### Problem-specific steps (proved) -/

/-- **Conditional Fano, averaged** (Thm 6.1 (4) proof, "applied conditionally … and averaged").
If `I_c ≥ P_c Λ − h(P_c)` for each value `c` of the conditioning variable, then with weights `w`
the averages satisfy the same inequality: `h` is concave (Jensen). -/
theorem fano_average {ι : Type*} (s : Finset ι) (w P I : ι → ℝ) (Λ : ℝ)
    (hw : ∀ c ∈ s, 0 ≤ w c) (hw1 : ∑ c ∈ s, w c = 1) (hP : ∀ c ∈ s, 0 ≤ P c ∧ P c ≤ 1)
    (hc : ∀ c ∈ s, P c * Λ - Real.binEntropy (P c) ≤ I c) :
    (∑ c ∈ s, w c * P c) * Λ - Real.binEntropy (∑ c ∈ s, w c * P c) ≤ ∑ c ∈ s, w c * I c := by
  have hJ := Real.strictConcave_binEntropy.concaveOn.le_map_sum hw hw1
    (fun c hc => (⟨(hP c hc).1, (hP c hc).2⟩ : P c ∈ Set.Icc (0:ℝ) 1))
  simp only [smul_eq_mul] at hJ
  have : ∑ c ∈ s, w c * (P c * Λ - Real.binEntropy (P c)) ≤ ∑ c ∈ s, w c * I c :=
    Finset.sum_le_sum fun c hcs => mul_le_mul_of_nonneg_left (hc c hcs) (hw c hcs)
  simp only [mul_sub, Finset.sum_sub_distrib] at this
  have e : ∑ c ∈ s, w c * (P c * Λ) = (∑ c ∈ s, w c * P c) * Λ := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
  linarith

/-- `h(p) ≤ p(1 − log p) = p·log(e/p)` for `0 < p ≤ 1` (used in Cor 6.2 as `n·h(y/n) ≤ y·log(en/y)`). -/
theorem binEntropy_le_mul_one_sub_log {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Real.binEntropy p ≤ p * (1 - Real.log p) := by
  unfold Real.binEntropy
  rw [Real.log_inv]
  rcases eq_or_lt_of_le hp1 with h1 | h1
  · subst h1; simp
  · have hq : 0 < 1 - p := by linarith
    have hlog : Real.log (1 - p)⁻¹ ≤ (1 - p)⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have e : (1 - p) * ((1 - p)⁻¹ - 1) = p := by field_simp; ring
    have := mul_le_mul_of_nonneg_left hlog hq.le
    rw [e] at this
    nlinarith

/-- **Theorem 6.1 (4), with the convexity repair (F7 / task a18).**
Inputs, as hypotheses:
* `hFano` — per face, list-Fano applied conditionally on `(U, W, V⁽<ⁱ⁾)` and averaged
  (`list_fano` + `fano_average`): `Iᵢ ≥ PᵢΛ′ − h(Pᵢ)`, with `Λ′ = log(N₁/k_out)`;
* `hInfo` — chain rule (Prop 5.2) + Thm 5.1: `∑ Iᵢ ≤ B := β*S_n(Q) + β₀Q`;
* `hI0` — mutual informations are non-negative;
* `hx` — `x = E[N_ε] ≤ ∑ Pᵢ` (recovery puts `V⁽ⁱ⁾` in the decoder's list).
Conclusion: `xΛ′ ≤ B + n·h(min{x/n, ½}) + slack` for any `slack ≥ 0` (v6 carries
`slack = (2nk_out/M)Λ′`, which this argument shows is unnecessary). -/
theorem thm61_eq4 {ι : Type*} [Fintype ι] [Nonempty ι] (Λ B x slack : ℝ) (P I : ι → ℝ) (hΛ : 0 ≤ Λ)
    (hP : ∀ i, 0 ≤ P i ∧ P i ≤ 1)
    (hFano : ∀ i, P i * Λ - Real.binEntropy (P i) ≤ I i)
    (hInfo : ∑ i, I i ≤ B) (hI0 : ∀ i, 0 ≤ I i)
    (hx0 : 0 ≤ x) (hx : x ≤ ∑ i, P i) (hslack : 0 ≤ slack) :
    x * Λ ≤ B + (Fintype.card ι : ℝ) * Real.binEntropy (min (x / Fintype.card ι) (1 / 2)) + slack := by
  set n : ℕ := Fintype.card ι with hndef
  have hn' : (0 : ℝ) < n := by exact_mod_cast (Fintype.card_pos (α := ι))
  set y := ∑ i, P i with hy
  have hyn : y ≤ n := by
    calc y ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hP i).2
      _ = n := by simp [hndef]
  -- h(Pᵢ) ≤ h(min(Pᵢ, ½))
  have hmin : ∀ i, Real.binEntropy (P i) ≤ Real.binEntropy (min (P i) (1 / 2)) := by
    intro i
    rcases le_total (P i) (1 / 2) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, one_div, Real.binEntropy_two_inv]; exact Real.binEntropy_le_log_two
  -- Jensen: ∑ h(min(Pᵢ,½)) ≤ n·h(min(y/n, ½))
  have hJ := Wave1.concaveOn_binEntropy_min.le_map_sum (t := Finset.univ)
    (w := fun _ => (1 / n : ℝ)) (p := P) (fun _ _ => by positivity) (by simp [hndef])
    (fun i _ => ⟨(hP i).1, (hP i).2⟩)
  simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
  have hJ' : ∑ i, Real.binEntropy (P i) ≤ n * Real.binEntropy (min (y / n) (1 / 2)) := by
    have e : 1 / (n : ℝ) * y = y / n := by ring
    rw [e] at hJ
    calc ∑ i, Real.binEntropy (P i) ≤ ∑ i, Real.binEntropy (min (P i) (1 / 2)) :=
          Finset.sum_le_sum fun i _ => hmin i
      _ = n * (1 / n * ∑ i, Real.binEntropy (min (P i) (1 / 2))) := by field_simp
      _ ≤ n * Real.binEntropy (min (y / n) (1 / 2)) := by gcongr
  have hsumF : y * Λ - ∑ i, Real.binEntropy (P i) ≤ ∑ i, I i := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hFano i
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at this
    exact this
  have hfy : y * Λ - n * Real.binEntropy (min (y / n) (1 / 2)) ≤ B := by linarith
  have hB0 : 0 ≤ B := le_trans (Finset.sum_nonneg fun i _ => hI0 i) hInfo
  have hconv := Wave1.a18 n Λ x y hn' hΛ hx0 hx hyn
  have : x * Λ - n * Real.binEntropy (min (x / n) (1 / 2)) ≤ B :=
    hconv.trans (max_le hB0 hfy)
  linarith

/-- **Corollary 6.2, information branch, corrected and unconditional** (F1, F13).
From (4) at `ζ = 0` with `x = E[N_ε] ≥ m/2`, slack `tΛ′` with `t = 2nk_out/M ≤ m/8`, and
`S_n(Q) ≤ Q`:  `Q ≥ (m/(8β*))·(3Λ′ − 4·log(2en/m))`, written with
`log(2en/m) = 1 + log(2n/m)`. No validity condition is needed. The display of v6,
`Q ≥ (m/(4β*))(Λ′ − log(4en/m))`, follows from this iff `Λ′ ≥ 2·log(4en/m) − 4·log 2` (task a23). -/
theorem cor62_info_corrected (n m Λ β Q S x t : ℝ) (hm : 1 ≤ m) (hmn : m ≤ n) (hΛ : 0 ≤ Λ)
    (hβ : 0 < β) (hS0 : 0 ≤ S) (hSQ : S ≤ Q) (ht : t ≤ m / 8) (hxm : m / 2 ≤ x) (hxn : x ≤ n)
    (h4 : x * Λ ≤ β * S + n * Real.binEntropy (min (x / n) (1 / 2)) + t * Λ) :
    Q ≥ m / (8 * β) * (3 * Λ - 4 * (1 + Real.log (2 * n / m))) := by
  have hn : 0 < n := by linarith
  have hconv := Wave1.a18 n Λ (m / 2) x hn hΛ (by linarith) hxm hxn
  have hfx : x * Λ - n * Real.binEntropy (min (x / n) (1 / 2)) ≤ β * Q + m / 8 * Λ := by
    nlinarith [mul_le_mul_of_nonneg_left hSQ hβ.le, mul_le_mul_of_nonneg_right ht hΛ]
  have hR0 : 0 ≤ β * Q + m / 8 * Λ := by
    have : 0 ≤ Q := hS0.trans hSQ; positivity
  have hfm := hconv.trans (max_le hR0 hfx)
  -- n·h(m/2n) ≤ (m/2)(1 + log(2n/m))
  set p := m / 2 / n with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 / 2 := by rw [hp, div_le_iff₀ hn]; linarith
  rw [min_eq_left hp1] at hfm
  have hent := binEntropy_le_mul_one_sub_log hp0 (by linarith)
  have hlog : Real.log p = -Real.log (2 * n / m) := by
    rw [hp, ← Real.log_inv]; congr 1; field_simp
  have hnp : n * p = m / 2 := by rw [hp]; field_simp
  have key : m / 2 * Λ - m / 2 * (1 + Real.log (2 * n / m)) ≤ β * Q + m / 8 * Λ := by
    have : n * Real.binEntropy p ≤ m / 2 * (1 + Real.log (2 * n / m)) := by
      calc n * Real.binEntropy p ≤ n * (p * (1 - Real.log p)) := by gcongr
        _ = m / 2 * (1 + Real.log (2 * n / m)) := by rw [hlog, ← mul_assoc, hnp]; ring
    linarith
  rw [ge_iff_le, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- **Eq. (5)** (pathwise): average nearest-output distance `≥ ε·(1 − N_ε/n)`. -/
theorem eq5_pathwise {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (ε : ℝ) :
    ε * (1 - ((Finset.univ.filter fun i => d i ≤ ε).card : ℝ) / Fintype.card ι) ≤
      (∑ i, d i) / Fintype.card ι := by
  set n : ℕ := Fintype.card ι with hndef
  have hn' : (0 : ℝ) < n := by exact_mod_cast (Fintype.card_pos (α := ι))
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => d i ≤ ε) d
  have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
    (fun i => d i ≤ ε)
  set cp := (Finset.univ.filter fun i => d i ≤ ε).card
  set cn := (Finset.univ.filter fun i => ¬ d i ≤ ε).card
  have h1 : (cn : ℝ) * ε ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ d i ≤ ε), d i := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i hi => by simp only [Finset.mem_filter] at hi; linarith [hi.2]
  have h2 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => d i ≤ ε), d i :=
    Finset.sum_nonneg fun i _ => hd i
  simp only [Finset.card_univ] at hcard
  have hc : (cn : ℝ) = n - cp := by
    rw [eq_sub_iff_add_eq, add_comm]; exact_mod_cast hcard
  rw [le_div_iff₀ hn']
  have e : ε * (1 - (cp : ℝ) / n) * n = ε * n - ε * cp := by field_simp
  rw [e]
  have h3 : (cn : ℝ) * ε = n * ε - cp * ε := by rw [hc]; ring
  linarith

/-- **Corollary 8.1, second branch — the contradiction step.** With `B = β*S_n(Q) + β₀Q ≥ 0`,
`Λ′ ≥ Λ_{ε*}/2` where `ε*` is chosen so that `Λ_{ε*} = 6B/n + 4`, the slack
`(2nk_out/M)Λ′ ≤ (n/8)Λ′` (from `k_out ≤ M/16`) and (4) at `ε*`, the count satisfies
`E[N_{ε*}] < n/2`. (v6: "since 6 > 16/3 and 4 > (16/3) log 2".) -/
theorem cor81_branch2_count (n B Λ x : ℝ) (hn : 0 < n) (hB : 0 ≤ B) (hΛ : (6 * B / n + 4) / 2 ≤ Λ)
    (hx0 : 0 ≤ x) (hxn : x ≤ n)
    (h4 : x * Λ ≤ B + n * Real.binEntropy (min (x / n) (1 / 2)) + n / 8 * Λ) : x < n / 2 := by
  by_contra hx
  push Not at hx
  have hh : Real.binEntropy (min (x / n) (1 / 2)) ≤ Real.log 2 := Real.binEntropy_le_log_two
  have hlog := Real.log_two_lt_d9
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) hΛ
  have h1 : n / 2 * Λ ≤ x * Λ := mul_le_mul_of_nonneg_right hx hΛ0
  have h2 : 3 * n / 8 * Λ ≤ B + n * Real.log 2 := by nlinarith
  have h3 : 3 * n / 8 * ((6 * B / n + 4) / 2) = 9 / 8 * B + 3 / 4 * n := by field_simp; ring
  have h4' : 3 * n / 8 * ((6 * B / n + 4) / 2) ≤ 3 * n / 8 * Λ :=
    mul_le_mul_of_nonneg_left hΛ (by positivity)
  norm_num at hlog
  nlinarith

/-- **Corollary 8.1 — the `ε*` unwinding.** Defining
`ε* = r₀/(3√2) · exp(−(6B/n + 4 + log(C₂d))/(d−1))` makes
`Λ_{ε*} := (d−1)·log(r₀/(3√2 ε*)) − log(C₂d)` equal `6B/n + 4`, and `ε* ≤ r₀/(3√2)` (so Thm 6.1's
scale condition holds) as soon as `6B/n + 4 + log(C₂d) ≥ 0`. -/
theorem cor81_epsStar (d n B r₀ C₂ : ℝ) (hd : 1 < d) (hr₀ : 0 < r₀) :
    let εs := r₀ / (3 * Real.sqrt 2) * Real.exp (-(6 * B / n + 4 + Real.log (C₂ * d)) / (d - 1))
    (d - 1) * Real.log (r₀ / (3 * Real.sqrt 2 * εs)) - Real.log (C₂ * d) = 6 * B / n + 4 ∧
    (0 ≤ 6 * B / n + 4 + Real.log (C₂ * d) → εs ≤ r₀ / (3 * Real.sqrt 2)) := by
  intro εs
  have hd1 : 0 < d - 1 := by linarith
  have hs : 0 < 3 * Real.sqrt 2 := by positivity
  constructor
  · have e : r₀ / (3 * Real.sqrt 2 * εs) =
        Real.exp ((6 * B / n + 4 + Real.log (C₂ * d)) / (d - 1)) := by
      simp only [εs]
      rw [show -(6 * B / n + 4 + Real.log (C₂ * d)) / (d - 1) =
        -((6 * B / n + 4 + Real.log (C₂ * d)) / (d - 1)) by ring, Real.exp_neg]
      field_simp
    rw [e, Real.log_exp]; field_simp; ring
  · intro h
    have : Real.exp (-(6 * B / n + 4 + Real.log (C₂ * d)) / (d - 1)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]; exact neg_nonpos.2 (div_nonneg h hd1.le)
    show r₀ / (3 * Real.sqrt 2) * _ ≤ _
    calc _ ≤ r₀ / (3 * Real.sqrt 2) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _

/-- **Proposition 8.3, Markov step.** If the plant average of a non-negative per-gallery count is
`≤ B`, the plant mass of galleries with count `> 2B` is at most `1/2`. -/
theorem prop83_markov {ι : Type*} (s : Finset ι) (w X : ι → ℝ) (B : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hX : ∀ i ∈ s, 0 ≤ X i) (hB : 0 < B) (hmean : ∑ i ∈ s, w i * X i ≤ B) :
    ∑ i ∈ s.filter (fun i => 2 * B < X i), w i ≤ 1 / 2 := by
  have h : ∑ i ∈ s.filter (fun i => 2 * B < X i), w i * (2 * B) ≤ ∑ i ∈ s, w i * X i := by
    calc ∑ i ∈ s.filter (fun i => 2 * B < X i), w i * (2 * B)
        ≤ ∑ i ∈ s.filter (fun i => 2 * B < X i), w i * X i :=
          Finset.sum_le_sum fun i hi => by
            simp only [Finset.mem_filter] at hi
            exact mul_le_mul_of_nonneg_left hi.2.le (hw i hi.1)
      _ ≤ ∑ i ∈ s, w i * X i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun i hi _ => mul_nonneg (hw i hi) (hX i hi)
  rw [← Finset.sum_mul] at h
  have := h.trans hmean
  by_contra hc
  push Not at hc
  nlinarith [mul_lt_mul_of_pos_right hc (by linarith : (0:ℝ) < 2 * B)]

/-- **Corollary 11.2 constant.** `((d−1)/8 − log 2)/(648e) ≥ (d−1)/15000` once `d − 1 ≥ 92`
(v6: "for d ≥ d₁"; the crossover is `d − 1 ≈ 91.6`). -/
theorem cor112_constant (d : ℝ) (hd : 92 ≤ d - 1) :
    (d - 1) / 15000 ≤ ((d - 1) / 8 - Real.log 2) / (648 * Real.exp 1) := by
  have he := Real.exp_one_lt_d9
  have he' := Real.exp_one_gt_d9
  have hl := Real.log_two_lt_d9
  norm_num at he he' hl
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-! ### v7 forms (added 17 Sep against n-face-partial-v7) -/

/-- `n·h(min{x/n, ½}) ≤ x·(1 + log(n/x))` for `0 < x ≤ n` (v7 Cor 6.2 proof, "n h(y/n) ≤ y log(en/y)",
including the range `x > n/2` where the `min` is active). -/
theorem n_binEntropy_min_le {n x : ℝ} (hx : 0 < x) (hxn : x ≤ n) :
    n * Real.binEntropy (min (x / n) (1 / 2)) ≤ x * (1 + Real.log (n / x)) := by
  have hn : 0 < n := lt_of_lt_of_le hx hxn
  rcases le_total (x / n) (1 / 2) with h | h
  · rw [min_eq_left h]
    have hp0 : 0 < x / n := div_pos hx hn
    have := binEntropy_le_mul_one_sub_log hp0 (by linarith)
    have hlog : Real.log (x / n) = -Real.log (n / x) := by
      rw [← Real.log_inv, inv_div]
    calc n * Real.binEntropy (x / n) ≤ n * (x / n * (1 - Real.log (x / n))) := by gcongr
      _ = x * (1 + Real.log (n / x)) := by rw [hlog]; field_simp; ring
  · rw [min_eq_right h, one_div, Real.binEntropy_two_inv]
    have hx2 : n / 2 ≤ x := by rw [le_div_iff₀ hn] at h; linarith
    -- log(n/x) ≥ 1 − x/n
    have hl : 1 - x / n ≤ Real.log (n / x) := by
      have := Real.one_sub_inv_le_log_of_pos (div_pos hn hx)
      rwa [inv_div] at this
    have hl2 := Real.log_two_lt_d9
    norm_num at hl2
    have key : x * (1 + (1 - x / n)) ≥ 3 / 4 * n := by
      rw [ge_iff_le, ← sub_nonneg]
      have e : x * (1 + (1 - x / n)) - 3 / 4 * n = (x - n / 2) * (3 * n / 2 - x) / n := by
        field_simp; ring
      rw [e]; apply div_nonneg _ hn.le; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hl hx.le]

/-- **v7 Corollary 6.2, information branch (sharp and unconditional forms).** From (4) without
the slack term (v7 ledger 18), `x = E[N_ε] ≥ m/2`, `S_n(Q) ≤ Q`, with `L = log(2en/m) = 1 + log(2n/m)`:
`x(Λ′ − L) ≤ β*Q`; hence `Q ≥ (m/(2β*))(Λ′ − L)` when `Λ′ ≥ L`. -/
theorem cor62_v7 (n m Λ β Q S x : ℝ) (hm : 1 ≤ m) (hβ : 0 < β) (hS : S ≤ Q)
    (hxm : m / 2 ≤ x) (hxn : x ≤ n)
    (h4 : x * Λ ≤ β * S + n * Real.binEntropy (min (x / n) (1 / 2))) :
    x * (Λ - (1 + Real.log (2 * n / m))) ≤ β * Q ∧
    (1 + Real.log (2 * n / m) ≤ Λ → m / (2 * β) * (Λ - (1 + Real.log (2 * n / m))) ≤ Q) := by
  have hx : 0 < x := by linarith
  have hent := n_binEntropy_min_le hx hxn
  have hn : 0 < n := lt_of_lt_of_le hx hxn
  have hlog : Real.log (n / x) ≤ Real.log (2 * n / m) := by
    apply Real.log_le_log (div_pos hn hx)
    rw [div_le_div_iff₀ hx (by linarith)]; nlinarith
  have h1 : x * (Λ - (1 + Real.log (2 * n / m))) ≤ β * Q := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hx.le, mul_le_mul_of_nonneg_left hS hβ.le]
  refine ⟨h1, fun hΛ => ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hxm (sub_nonneg.2 hΛ)]

/-- **v7 Corollary 8.1, second branch (slack-free).** With `Λ′ ≥ Λ_{ε*}/2 = 3B/n + 2` and (4) without
slack, `E[N_{ε*}] < n/2` ("3 > 2, 2 > 2 log 2"). -/
theorem cor81_v7_count (n B Λ x : ℝ) (hn : 0 < n) (hB : 0 ≤ B) (hΛ : 3 * B / n + 2 ≤ Λ)
    (h4 : x * Λ ≤ B + n * Real.binEntropy (min (x / n) (1 / 2))) : x < n / 2 := by
  by_contra hx
  push Not at hx
  have hh : Real.binEntropy (min (x / n) (1 / 2)) ≤ Real.log 2 := Real.binEntropy_le_log_two
  have hlog := Real.log_two_lt_d9
  norm_num at hlog
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) hΛ
  have h1 : n / 2 * Λ ≤ x * Λ := mul_le_mul_of_nonneg_right hx hΛ0
  have h2 : n / 2 * (3 * B / n + 2) = 3 / 2 * B + n := by field_simp
  have h3 : n / 2 * (3 * B / n + 2) ≤ n / 2 * Λ := mul_le_mul_of_nonneg_left hΛ (by positivity)
  nlinarith

end OracleBounds.V6.Info
