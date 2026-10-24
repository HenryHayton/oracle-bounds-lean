import OracleBounds.GeneralPrior.Coupling
import OracleBounds.V6.Information

/-!
# Small-ball list-Fano for a general prior (`n-face-general-prior-v1` §5, Lemma 5.3 — G6)

Generalises `OracleBounds.V6.Info.list_fano` (which needed a *uniform* law on `A` and a plain
cardinality bound `|L y| ≤ κ₀`) to an arbitrary finite prior `π = marg₁ q`, with the list `L y`
a union of `k` balls of an abstract "nearness" relation, each of mass at most `p₀` under `π`. The
core Gibbs/log-sum argument (`Info.mul_log_div_ge_sub`, `Info.log_sum_ineq`) is reused verbatim
from `V6.Information`; only the derivation of the list's total mass `P₀ ≤ k·p₀` changes, and that
step is exactly `GeneralPrior.mass_reached_le` (built for `Coupling.ghost_bound_weighted`,
reused here with no change).

No `sorry`s.
-/

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6.Info

variable {A β : Type*} [Fintype A] [Fintype β] [DecidableEq A]

open Classical in
/-- **Lemma 5.3 (small-ball list-Fano), general prior — G6.** `V` has an arbitrary finite law
`marg₁ q` on `A` (no uniformity assumed). `L y` is the set of `a` near *some* of `k` centres
`centers y : Fin k → C` (a "list of size `≤ k`" in the note's sense; `C` is the type the
attacker's outputs live in — points of the sphere, not values of `A` — and `near` plays the role
of "within `ε`"). If every `near`-ball has `π`-mass at most `p₀ < 1`, then with
`P := P[V ∈ L(Y)]`:
`P · log(1/(k·p₀)) − h(P) ≤ I(V;Y)`. -/
theorem small_ball_fano {C : Type*} (q : A × β → ℝ) (hq : ∀ ab, 0 ≤ q ab) (hsum : ∑ ab, q ab = 1)
    (near : A → C → Prop) [∀ a c, Decidable (near a c)]
    (k : ℕ) (centers : β → Fin k → C) (p₀ : ℝ) (hp₀0 : 0 ≤ p₀) (hp₀1 : (k : ℝ) * p₀ < 1)
    (hballcov : ∀ c₀ : C, (∑ a ∈ Finset.univ.filter (near · c₀), marg₁ q a) ≤ p₀) :
    let L : β → Finset A := fun y => Finset.univ.filter (fun a => ∃ j, near a (centers y j))
    let P := ∑ ab, if ab.1 ∈ L ab.2 then q ab else 0
    P * Real.log (1 / ((k : ℝ) * p₀)) - Real.binEntropy P ≤ mutualInfo q := by
  intro L P
  set κp : ℝ := (k : ℝ) * p₀ with hκp
  have hκppos : 0 < κp ∨ κp = 0 := (lt_or_eq_of_le (by positivity : (0:ℝ) ≤ κp)).imp id Eq.symm
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
    rw [hPS, ← hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun ab : A × β => ab.1 ∈ L ab.2)]
    ring
  set P₀ := ∑ ab ∈ S, m ab
  have hP₀c : 1 - P₀ = ∑ ab ∈ Sc, m ab := by
    rw [← sum_marg_mul q hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun ab : A × β => ab.1 ∈ L ab.2)]
    ring
  -- `P₀ ≤ κp = k·p₀`, via the weighted union bound (`mass_reached_le`).
  have hP₀ : P₀ ≤ κp := by
    have e : P₀ = ∑ b, marg₂ q b * (∑ a, marg₁ q a *
        (if ∃ i ∈ (Finset.univ : Finset (Fin k)), near a (centers b i) then (1 : ℝ) else 0)) := by
      simp only [P₀, S, Finset.sum_filter, m, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : a ∈ L b
      · have ha' : ∃ i ∈ (Finset.univ : Finset (Fin k)), near a (centers b i) := by
          simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          obtain ⟨j, hj⟩ := ha; exact ⟨j, Finset.mem_univ j, hj⟩
        rw [if_pos ha, if_pos ha']; ring
      · have ha' : ¬ ∃ i ∈ (Finset.univ : Finset (Fin k)), near a (centers b i) := by
          simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          rintro ⟨j, _, hj⟩; exact ha ⟨j, hj⟩
        rw [if_neg ha, if_neg ha']; ring
    rw [e]
    calc ∑ b, marg₂ q b * (∑ a, marg₁ q a *
          (if ∃ i ∈ (Finset.univ : Finset (Fin k)), near a (centers b i) then (1 : ℝ) else 0))
        ≤ ∑ b, marg₂ q b * ((Finset.univ : Finset (Fin k)).card * p₀) := by
          apply Finset.sum_le_sum
          intro b _
          apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun _ _ => hq _)
          exact mass_reached_le (marg₁ q) near p₀ (fun a => Finset.sum_nonneg fun _ _ => hq _)
            hballcov Finset.univ (centers b)
      _ = κp := by
          simp only [Finset.card_univ, Fintype.card_fin]
          rw [← Finset.sum_mul, sum_marg₂, hsum, one_mul]
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
  -- the `Z = 1` term: `P log(P/P₀) ≥ P log P + P log(1/κp)`
  have k1 : P * Real.log P + P * Real.log (1 / κp) ≤ P * Real.log (P / P₀) := by
    rcases eq_or_lt_of_le hP0 with h | h
    · rw [← h]; simp
    have hκppos' : 0 < κp := by
      rcases hκppos with h' | h'
      · exact h'
      · exfalso
        have hP₀eq0 : P₀ = 0 := le_antisymm (h' ▸ hP₀) hP₀0
        have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hm0 i).1 hP₀eq0
        have : P = 0 := hPS ▸ Finset.sum_eq_zero fun i hi => hac i (hz i hi)
        linarith
    have hq0 : 0 < P₀ := by
      rcases eq_or_lt_of_le hP₀0 with h' | h'
      · exfalso
        have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hm0 i).1 h'.symm
        have : P = 0 := hPS ▸ Finset.sum_eq_zero fun i hi => hac i (hz i hi)
        linarith
      · exact h'
    rw [Real.log_div h.ne' hq0.ne']
    have : Real.log (1 / κp) ≤ -Real.log P₀ := by
      rw [← Real.log_inv, one_div]
      exact Real.log_le_log (by positivity) ((inv_le_inv₀ hκppos' hq0).mpr hP₀)
    nlinarith
  have hH : Real.binEntropy P = -(P * Real.log P) - (1 - P) * Real.log (1 - P) := by
    simp only [Real.binEntropy, Real.log_inv]; ring
  rw [hH, hsplit]
  linarith

/-! ### Product priors: marginal identities (reused by G7 and by the Thm 6.1(4) assembly) -/

/-- An independent product prior is a probability mass function. -/
lemma prodPrior_sum {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine]
    (π : ι → Fine → ℝ) (hπ1 : ∀ i, ∑ l, π i l = 1) :
    ∑ v : ι → Fine, ∏ j, π j (v j) = 1 := by
  rw [← Fintype.prod_sum (fun j x => π j x)]
  exact Finset.prod_eq_one fun j _ => hπ1 j

/-- **Marginal of a product prior.** Summing `∏ⱼ πⱼ(vⱼ)` over all `v` with `vᵢ = l` gives `πᵢ(l)`.
Proved by splitting off coordinate `i` with `Equiv.funSplitAt`; the remaining coordinates
collapse to `1` by `Fintype.prod_sum`. -/
lemma prodPrior_marg {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]
    (π : ι → Fine → ℝ) (hπ1 : ∀ i, ∑ l, π i l = 1) (i : ι) (l : Fine) :
    ∑ v : ι → Fine, (if v i = l then ∏ j, π j (v j) else 0) = π i l := by
  have hsub : ∀ v : ι → Fine,
      ∏ j : {x : ι // x ≠ i}, π j.1 (v j.1) = ∏ j ∈ Finset.univ.erase i, π j (v j) :=
    fun v => (Finset.prod_subtype (Finset.univ.erase i) (fun x => by simp)
      (fun j => π j (v j))).symm
  have key : ∀ v : ι → Fine, ∏ j, π j (v j) =
      π i ((Equiv.funSplitAt i Fine) v).1 *
        ∏ j : {x : ι // x ≠ i}, π j.1 (((Equiv.funSplitAt i Fine) v).2 j) := by
    intro v
    simp only [Equiv.funSplitAt_apply]
    rw [hsub]
    exact (Finset.mul_prod_erase Finset.univ (fun j => π j (v j)) (Finset.mem_univ i)).symm
  calc ∑ v : ι → Fine, (if v i = l then ∏ j, π j (v j) else 0)
      = ∑ v : ι → Fine, (if v i = l then
          π i ((Equiv.funSplitAt i Fine) v).1 *
            ∏ j : {x : ι // x ≠ i}, π j.1 (((Equiv.funSplitAt i Fine) v).2 j) else 0) :=
        Finset.sum_congr rfl fun v _ => by rw [key v]
    _ = ∑ p : Fine × ({x : ι // x ≠ i} → Fine), (if p.1 = l then
          π i p.1 * ∏ j : {x : ι // x ≠ i}, π j.1 (p.2 j) else 0) := by
        apply Fintype.sum_equiv (Equiv.funSplitAt i Fine)
        intro v; simp only [Equiv.funSplitAt_apply]
    _ = π i l := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single l (fun x _ hx => by simp [hx]) (by simp)]
        simp only [if_true]
        rw [← Finset.mul_sum]
        rw [← Fintype.prod_sum (fun (j : {x : ι // x ≠ i}) x => π j.1 x)]
        rw [Finset.prod_congr rfl (fun j _ => hπ1 j.1), Finset.prod_const_one, mul_one]

/-- The per-face joint law `(Vᵢ, Y)` of a product prior with any conditional kernel `P` has first
marginal `πᵢ`: conditioning on the other faces and summing them out leaves face `i`'s own prior. -/
lemma faceJoint_marg₁ {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine]
    [DecidableEq Fine] (π : ι → Fine → ℝ) (hπ1 : ∀ i, ∑ l, π i l = 1)
    (P : (ι → Fine) → β → ℝ) (hP1 : ∀ v, ∑ b, P v b = 1) (i : ι) (l : Fine) :
    marg₁ (fun lb : Fine × β => ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = lb.1),
        (∏ j, π j (v j)) * P v lb.2) l = π i l := by
  simp only [marg₁]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hP1, mul_one]
  rw [Finset.sum_filter]
  exact prodPrior_marg π hπ1 i l

/-! ### Superadditivity for independent, non-uniform priors (G7) -/

open Classical in
/-- **Superadditivity for independent inputs, general prior — G7.** Generalises
`V6.Info.mutualInfo_superadditive` (uniform prior on `ι → Fine`) to an arbitrary independent
product prior `∏ⱼ πⱼ`. Same Gibbs argument against the product reference
`R(v,y) = qV(v)·b(y)·∏ᵢ(qᵢ(vᵢ,y)/(πᵢ(vᵢ)·b(y)))`; the only new step is computing the marginals
`marg₁ q v = qV(v)` and `marg₁ (qᵢ i) l = πᵢ(l)` (no longer constant across `v`/`l`), both via
`Fintype.prod_sum` applied to a coordinate-modified weight function instead of the uniform
`Fintype.card_filter_piFinset_const`. -/
theorem mutualInfo_superadditive_prior {ι Fine : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Fine] [DecidableEq Fine] [Nonempty Fine]
    (π : ι → Fine → ℝ) (hπ0 : ∀ i l, 0 ≤ π i l) (hπ1 : ∀ i, ∑ l, π i l = 1)
    (P : (ι → Fine) → β → ℝ) (hP : ∀ v b, 0 ≤ P v b) (hP1 : ∀ v, ∑ b, P v b = 1) :
    ∑ i, mutualInfo (fun lb : Fine × β => ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = lb.1),
        (∏ j, π j (v j)) * P v lb.2)
      ≤ mutualInfo (fun vb : (ι → Fine) × β => (∏ j, π j (vb.1 j)) * P vb.1 vb.2) := by
  rcases isEmpty_or_nonempty ι with hE | hNE
  · haveI : Unique (ι → Fine) := Pi.uniqueOfIsEmpty (fun _ : ι => Fine)
    have hqV1 : ∀ v : ι → Fine, (∏ j, π j (v j)) = 1 := fun v => by
      rw [show (Finset.univ : Finset ι) = ∅ from Finset.univ_eq_empty]
      exact Finset.prod_empty
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty, one_mul]
    have hq0 : ∀ vb : (ι → Fine) × β, 0 ≤ P vb.1 vb.2 := fun vb => hP _ _
    have hqsum : ∑ vb : (ι → Fine) × β, P vb.1 vb.2 = 1 := by
      rw [Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]
      exact hP1 _
    exact mutualInfo_nonneg _ hq0 hqsum
  set qV : (ι → Fine) → ℝ := fun v => ∏ j, π j (v j) with hqVdef
  have hqV0 : ∀ v, 0 ≤ qV v := fun v => Finset.prod_nonneg fun j _ => hπ0 j (v j)
  have hqVsum : ∑ v, qV v = 1 := by
    rw [hqVdef, ← Fintype.prod_sum (fun j x => π j x)]
    exact Finset.prod_eq_one fun j _ => hπ1 j
  set q : (ι → Fine) × β → ℝ := fun vb => qV vb.1 * P vb.1 vb.2 with hqdef
  set qi : ι → Fine × β → ℝ := fun i lb =>
    ∑ v ∈ Finset.univ.filter (fun v : ι → Fine => v i = lb.1), qV v * P v lb.2 with hqidef
  show ∑ i, mutualInfo (qi i) ≤ mutualInfo q
  have hq0 : ∀ vb, 0 ≤ q vb := fun vb => mul_nonneg (hqV0 _) (hP _ _)
  have hqi0 : ∀ i lb, 0 ≤ qi i lb :=
    fun i lb => Finset.sum_nonneg fun v _ => mul_nonneg (hqV0 v) (hP _ _)
  set b : β → ℝ := marg₂ q with hbdef
  have hb0 : ∀ y, 0 ≤ b y := fun y => Finset.sum_nonneg fun _ _ => hq0 _
  have hm1 : ∀ v, marg₁ q v = qV v := fun v => by
    simp only [marg₁, q, ← Finset.mul_sum, hP1, mul_one]
  have hsumq : ∑ vb, q vb = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [q, ← Finset.mul_sum, hP1, mul_one]
    exact hqVsum
  have hsumb : ∑ y, b y = 1 := by
    rw [← hsumq, Fintype.sum_prod_type, Finset.sum_comm]; rfl
  have hmi2 : ∀ i y, marg₂ (qi i) y = b y := fun i y => by
    simp only [marg₂, qi, b]
    exact Finset.sum_fiberwise (Finset.univ) (fun v : ι → Fine => v i) (fun v => qV v * P v y)
  -- `marg₁ (qᵢ i) l = πᵢ(l)`: reindex the full sum over `v : ι → Fine` via `Equiv.funSplitAt i`,
  -- splitting off coordinate `i`; the other coordinates collapse to `1` by `Fintype.prod_sum`.
  have hmarg_split : ∀ (i : ι) (l : Fine),
      ∑ v : ι → Fine, (if v i = l then qV v else 0) = π i l :=
    fun i l => prodPrior_marg π hπ1 i l
  have hmi1 : ∀ i l, marg₁ (qi i) l = π i l := fun i l => by
    have hswap : marg₁ (qi i) l = ∑ v : ι → Fine, (if v i = l then qV v else 0) := by
      simp only [marg₁, qi]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hP1, mul_one]
      exact Finset.sum_filter _ _
    rw [hswap]; exact hmarg_split i l
  set R : (ι → Fine) × β → ℝ := fun vb =>
    qV vb.1 * b vb.2 * ∏ i, (qi i (vb.1 i, vb.2) / (π i (vb.1 i) * b vb.2)) with hRdef
  have hqi_ge : ∀ i (vb : (ι → Fine) × β), q vb ≤ qi i (vb.1 i, vb.2) := fun i vb =>
    Finset.single_le_sum (f := fun v => qV v * P v vb.2) (fun v _ => mul_nonneg (hqV0 v) (hP _ _))
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
  have hqb : ∀ vb : (ι → Fine) × β, q vb ≤ b vb.2 := fun vb =>
    Finset.single_le_sum (f := fun v => q (v, vb.2)) (fun v _ => hq0 _) (Finset.mem_univ vb.1)
  have hπi_ge : ∀ i (vb : (ι → Fine) × β), qi i (vb.1 i, vb.2) ≤ π i (vb.1 i) := fun i vb => by
    have := le_marg₁ (q := qi i) (fun lb => hqi0 i lb) (vb.1 i, vb.2)
    rwa [hmi1] at this
  -- pointwise Gibbs against the product reference `R`
  have hpt : ∀ vb : (ι → Fine) × β, q vb - R vb ≤
      q vb * Real.log (q vb / (qV vb.1 * b vb.2)) -
        ∑ i, q vb * Real.log (qi i (vb.1 i, vb.2) / (π i (vb.1 i) * b vb.2)) := by
    intro vb
    rcases eq_or_lt_of_le (hq0 vb) with h0 | h0
    · rw [← h0]
      simp only [zero_mul, Finset.sum_const_zero, sub_zero, zero_sub, neg_nonpos]
      exact mul_nonneg (mul_nonneg (hqV0 _) (hb0 _))
        (Finset.prod_nonneg fun i _ => div_nonneg (hqi0 _ _)
          (mul_nonneg (hπ0 i _) (hb0 _)))
    have hqVpos : 0 < qV vb.1 := by
      rcases eq_or_lt_of_le (hqV0 vb.1) with h | h
      · exfalso
        have hq0' : q vb = 0 := by rw [hqdef]; simp [← h]
        linarith
      · exact h
    have hbpos : 0 < b vb.2 := lt_of_lt_of_le h0 (hqb vb)
    have hX : ∀ i, 0 < qi i (vb.1 i, vb.2) / (π i (vb.1 i) * b vb.2) := fun i => by
      have hqipos : 0 < qi i (vb.1 i, vb.2) := lt_of_lt_of_le h0 (hqi_ge i vb)
      have hπpos : 0 < π i (vb.1 i) := lt_of_lt_of_le hqipos (hπi_ge i vb)
      exact div_pos hqipos (mul_pos hπpos hbpos)
    have hRpos : 0 < R vb := mul_pos (mul_pos hqVpos hbpos) (Finset.prod_pos fun i _ => hX i)
    have g := mul_log_div_ge_sub (hq0 vb) hRpos.le (fun h => absurd h hRpos.ne')
    rw [Real.log_div h0.ne' hRpos.ne'] at g
    rw [Real.log_div h0.ne' (mul_pos hqVpos hbpos).ne', ← Finset.mul_sum]
    have eR : Real.log (R vb) = Real.log (qV vb.1 * b vb.2) +
        ∑ i, Real.log (qi i (vb.1 i, vb.2) / (π i (vb.1 i) * b vb.2)) := by
      simp only [R]
      rw [Real.log_mul (mul_pos hqVpos hbpos).ne' (Finset.prod_pos fun i _ => hX i).ne',
        Real.log_prod fun i _ => (hX i).ne']
    rw [eR] at g
    linarith
  -- the reference has total mass exactly one
  have hR1 : ∑ vb, R vb ≤ 1 := by
    rw [← hsumb, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_le_sum fun y _ => ?_
    rcases eq_or_lt_of_le (hb0 y) with h0 | h0
    · simp [← h0, hRdef, mul_zero, div_zero]
    have hcomb : ∀ v : ι → Fine, qV v * ∏ i, (qi i (v i, y) / (π i (v i) * b y)) =
        ∏ i, (qi i (v i, y) / b y) := by
      intro v
      rw [hqVdef, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rcases eq_or_lt_of_le (hπ0 i (v i)) with hπ0' | hπpos
      · have hqi0' : qi i (v i, y) = 0 := le_antisymm (hπ0' ▸ hπi_ge i (v, y)) (hqi0 i _)
        rw [hqi0']; simp
      · field_simp
    have e : ∑ v : ι → Fine, qV v * b y * ∏ i, (qi i (v i, y) / (π i (v i) * b y)) =
        b y * ∑ v : ι → Fine, ∏ i, (qi i (v i, y) / b y) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by rw [← hcomb v]; ring
    show (∑ v, qV v * b y * ∏ i, (qi i (v i, y) / (π i (v i) * b y))) ≤ b y
    rw [e, ← Fintype.prod_sum (fun i x => qi i (x, y) / b y)]
    have hone : ∀ i, ∑ x, qi i (x, y) / b y = 1 := fun i => by
      have hnum : (∑ x, qi i (x, y)) = b y := hmi2 i y
      rw [← Finset.sum_div, hnum, div_self h0.ne']
    rw [Finset.prod_congr rfl fun i _ => hone i, Finset.prod_const_one, mul_one]
  -- assemble: `I(V;Y) − Σᵢ I(Vᵢ;Y) = Σ (pointwise terms) ≥ Σ q − Σ R ≥ 0`
  have hIi : ∀ i, mutualInfo (qi i) =
      ∑ vb : (ι → Fine) × β, q vb * Real.log (qi i (vb.1 i, vb.2) / (π i (vb.1 i) * b vb.2)) :=
    fun i => by
    simp only [mutualInfo, hmi1, hmi2]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
      Finset.sum_comm (s := (Finset.univ : Finset Fine)),
      Finset.sum_comm (s := (Finset.univ : Finset (ι → Fine)))]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [qi, Finset.sum_mul]
    rw [← Finset.sum_fiberwise Finset.univ (fun v : ι → Fine => v i)]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun v hv => ?_
    rw [(Finset.mem_filter.1 hv).2]
  have hI : mutualInfo q = ∑ vb : (ι → Fine) × β, q vb * Real.log (q vb / (qV vb.1 * b vb.2)) := by
    simp only [mutualInfo, hm1, hbdef]
  rw [Finset.sum_congr rfl fun i _ => hIi i, Finset.sum_comm, hI, ← sub_nonneg,
    ← Finset.sum_sub_distrib]
  have hsum_le := Finset.sum_le_sum fun vb (_ : vb ∈ Finset.univ) => hpt vb
  rw [Finset.sum_sub_distrib, hsumq] at hsum_le
  linarith

end OracleBounds.GeneralPrior
