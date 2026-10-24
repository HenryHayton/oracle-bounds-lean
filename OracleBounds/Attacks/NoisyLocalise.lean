import OracleBounds.GeneralPrior.FixedSample

/-!
# Noisy comparisons by majority vote (airlock-draft-v11.1, Remark 4.3.7, the (P) half)

**UNSIGNED — statements drafted by a subagent, awaiting administrator sign-off.**

The note's Remark 4.3.7 (P) half, verbatim:

> Under `K1(ρ)`, taking each of the `B` comparisons by majority of
> `N₂ := ⌈log(2B/δ)/C_ch(ρ)⌉` probes costs `B N₂` and succeeds with probability `≥ 1 − δ`
> (Lemma 4.1.2, union bound) — a multiplicative `log` (P).

The (S) half of the remark (the posterior-median search paying the cost *additively*) is
simulation evidence and is **not** formalised here.

**Model.** A deterministic noiseless comparison algorithm is a pair
`qry : List Bool → X` (the next comparison point, given the answers so far) and
`out : List Bool → Y` (the output after `B` answers); `truth : X → Bool` is the noiseless
oracle `x ↦ [⟨x,g⟩ > thr]`. `L0` (`Attacks.Localise`) and `L2` (`Attacks.Localise2`) are such
algorithms with `B = Q_loc` comparisons; as elsewhere in this repo the *number* of queries is
read off the algorithm's definition rather than formalised, so `B` here is a parameter.

Under `K1(ρ)` the oracle answers a probe `x` with `1` with probability `1 − ρ` if `truth x` and
`ρ` otherwise, independently across rounds (`hp`); this is `Definition 4.1.1`, and it is the
`val` process of `OracleBounds.V6.Process`.

**Wrapper.** `probeMaj N qry` runs the noiseless algorithm on the *decoded* answers `dec N h`:
the history is cut into blocks of `N` consecutive rounds and block `j` is decoded by majority
vote (`majBit`, ties → `false`). Round `j·N + i` therefore probes `qry (dec N h)`, which is
constant across a block.

**Results.**
* `chernoff_block` — Lemma 4.1.2 at an arbitrary starting history (`val_pow_count` + Markov).
* `block_err` — one block decodes wrongly with probability `≤ exp(−N·C_ch(ρ))`.
* `decode_union` — union bound: `P[dec N h ≠ ideal B] ≤ B·exp(−N·C_ch(ρ))` after `B·N` rounds.
* `noisy_majority` — hence `P[dec = ideal] ≥ 1 − B·exp(−N·C_ch(ρ))`.
* `noisy_majority_succeeds` — **Remark 4.3.7 (P)**: at `N = N₂ = ⌈log(2B/δ)/C_ch(ρ)⌉`, for any
  success predicate `S` that the noiseless run satisfies, the noisy run satisfies it with
  probability `≥ 1 − δ`, at `B·N₂` queries.

No `sorry`s.
-/

set_option linter.unusedSectionVars false

namespace OracleBounds.Attacks

open Finset OracleBounds.V6 OracleBounds.GeneralPrior

/-! ### Generic `val` lemmas (prefix versions of `val_mono`, congruence in the probe rule) -/

section ValGeneric

variable {X : Type*} {p : X → ℝ}

/-- `val_mono` with the comparison only required on extensions of the starting history. -/
lemma val_mono_pre (probe : List Bool → X) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    {F G : List Bool → ℝ} :
    ∀ r h, (∀ h', h <+: h' → h'.length = h.length + r → F h' ≤ G h') →
      val p probe F r h ≤ val p probe G r h := by
  intro r
  induction r with
  | zero => intro h hFG; exact hFG h (List.prefix_refl h) (by simp)
  | succ r ih =>
    intro h hFG
    have h1 := ih (h ++ [true]) (fun h' hpre hl =>
      hFG h' ((List.prefix_append h [true]).trans hpre) (by simp at hl ⊢; omega))
    have h2 := ih (h ++ [false]) (fun h' hpre hl =>
      hFG h' ((List.prefix_append h [false]).trans hpre) (by simp at hl ⊢; omega))
    simp only [val_succ]
    have hp0 := (hp (probe h)).1
    have hp1 : 0 ≤ 1 - p (probe h) := by linarith [(hp (probe h)).2]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hp0) (mul_le_mul_of_nonneg_left h2 hp1)

/-- Only the probes issued strictly inside the next `r` rounds matter. -/
lemma val_congr_probe (probe probe' : List Bool → X) (F : List Bool → ℝ) :
    ∀ r h, (∀ h', h <+: h' → h'.length < h.length + r → probe h' = probe' h') →
      val p probe F r h = val p probe' F r h := by
  intro r
  induction r with
  | zero => intro h _; rfl
  | succ r ih =>
    intro h hpr
    have hx : probe h = probe' h := hpr h (List.prefix_refl h) (by omega)
    have h1 := ih (h ++ [true]) (fun h' hpre hl =>
      hpr h' ((List.prefix_append h [true]).trans hpre) (by simp at hl ⊢; omega))
    have h2 := ih (h ++ [false]) (fun h' hpre hl =>
      hpr h' ((List.prefix_append h [false]).trans hpre) (by simp at hl ⊢; omega))
    simp only [val_succ, hx, h1, h2]

/-- A leaf function constant on all extensions of `h` has that value as its expectation. -/
lemma val_of_const_on (probe : List Bool → X) (F : List Bool → ℝ) (r : ℕ) (h : List Bool)
    (hF : ∀ h', h <+: h' → h'.length = h.length + r → F h' = F h) :
    val p probe F r h = F h := by
  rw [val_congr_prefix' p probe r h (G := fun _ => F h) (fun h' hpre hl => hF h' hpre hl),
    val_const]

end ValGeneric

/-! ### The Chernoff exponent -/

/-- `C_ch(ρ) = ½ log(1/(4ρ(1−ρ)))` (Definition 4.1.1). -/
noncomputable def Cch (ρ : ℝ) : ℝ := (1 / 2) * Real.log (1 / (4 * ρ * (1 - ρ)))

lemma Cch_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) : 0 < Cch ρ := by
  have h4 : 0 < 4 * ρ * (1 - ρ) := by nlinarith
  have hlt : 4 * ρ * (1 - ρ) < 1 := by nlinarith [sq_nonneg (1 - 2 * ρ)]
  have : 1 < 1 / (4 * ρ * (1 - ρ)) := by rw [lt_div_iff₀ h4]; linarith
  have := Real.log_pos this
  unfold Cch; linarith

/-- `2√(ρ(1−ρ)) = e^{−C_ch(ρ)}`: the Chernoff bound of `FixedSample` in exponential form. -/
lemma two_sqrt_eq_exp {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    2 * Real.sqrt (ρ * (1 - ρ)) = Real.exp (-Cch ρ) := by
  have h4 : 0 < 4 * ρ * (1 - ρ) := by nlinarith
  have h4s : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hs : Real.sqrt (4 * ρ * (1 - ρ)) = 2 * Real.sqrt (ρ * (1 - ρ)) := by
    rw [mul_assoc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4s]
  rw [← hs, Real.sqrt_eq_rpow, Real.rpow_def_of_pos h4]
  unfold Cch
  rw [one_div (4 * ρ * (1 - ρ)), Real.log_inv]
  ring_nf

lemma pow_two_sqrt_eq_exp {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (N : ℕ) :
    (2 * Real.sqrt (ρ * (1 - ρ))) ^ N = Real.exp (-(N * Cch ρ)) := by
  rw [two_sqrt_eq_exp hρ0 hρ1, ← Real.exp_nat_mul]
  ring_nf

/-! ### Blocks, decoding, and the noiseless run -/

variable {X Y : Type*}

/-- Majority vote of a block of bits (ties decode to `false`). -/
def majBit (N : ℕ) (w : List Bool) : Bool := N < 2 * w.count true

/-- The decoded answer of block `j` of the history `h`. -/
def blk (N j : ℕ) (h : List Bool) : Bool := majBit N ((h.drop (j * N)).take N)

/-- The list of answers decoded from the *complete* blocks of `h`. -/
def dec (N : ℕ) (h : List Bool) : List Bool :=
  (List.range (h.length / N)).map (fun j => blk N j h)

/-- The transcript of the noiseless run after `j` comparisons. -/
def ideal (truth : X → Bool) (qry : List Bool → X) : ℕ → List Bool
  | 0 => []
  | j + 1 => ideal truth qry j ++ [truth (qry (ideal truth qry j))]

/-- The correct answer to comparison `j` of the noiseless run. -/
def ibit (truth : X → Bool) (qry : List Bool → X) (j : ℕ) : Bool :=
  truth (qry (ideal truth qry j))

/-- The noisy attacker: run the noiseless algorithm on the decoded answers. -/
def probeMaj (N : ℕ) (qry : List Bool → X) (h : List Bool) : X := qry (dec N h)

/-- Every block before `j` decoded correctly. -/
def Ok (truth : X → Bool) (qry : List Bool → X) (N j : ℕ) (h : List Bool) : Prop :=
  ∀ r < j, blk N r h = ibit truth qry r

instance (truth : X → Bool) (qry : List Bool → X) (N j : ℕ) (h : List Bool) :
    Decidable (Ok truth qry N j h) := Nat.decidableBallLT _ _

/-- The event "blocks `0 … j−1` decoded correctly but block `j` did not". -/
noncomputable def errAt (truth : X → Bool) (qry : List Bool → X) (N j : ℕ) (h : List Bool) : ℝ :=
  if Ok truth qry N j h ∧ blk N j h ≠ ibit truth qry j then 1 else 0

/-! ### Elementary block bookkeeping -/

/-- Block `r` is determined by the first `(r+1)·N` bits. -/
lemma blk_append {N r : ℕ} (h₁ w : List Bool) (hlen : (r + 1) * N ≤ h₁.length) :
    blk N r (h₁ ++ w) = blk N r h₁ := by
  have hexp : (r + 1) * N = r * N + N := by ring
  have h1 : r * N ≤ h₁.length := by omega
  have h2 : N ≤ (h₁.drop (r * N)).length := by
    rw [List.length_drop]; omega
  unfold blk
  rw [List.drop_append_of_le_length h1, List.take_append_of_le_length h2]

/-- The last block of `h₀ ++ w` is `w` itself. -/
lemma blk_last {N j : ℕ} (h₀ w : List Bool) (hlen : h₀.length = j * N) (hw : w.length = N) :
    blk N j (h₀ ++ w) = majBit N w := by
  unfold blk
  rw [← hlen, List.drop_left, ← hw, List.take_length]

lemma ideal_length (truth : X → Bool) (qry : List Bool → X) (j : ℕ) :
    (ideal truth qry j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [ideal, ih]

lemma ideal_getElem? (truth : X → Bool) (qry : List Bool → X) :
    ∀ (B j : ℕ), j < B → (ideal truth qry B)[j]? = some (ibit truth qry j) := by
  intro B
  induction B with
  | zero => intro j hj; omega
  | succ B ih =>
    intro j hj
    have hlen : (ideal truth qry B).length = B := ideal_length truth qry B
    have he : ideal truth qry (B + 1) = ideal truth qry B ++ [ibit truth qry B] := rfl
    rw [he]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · rw [List.getElem?_append_left (by omega)]
      exact ih j h
    · subst h
      rw [List.getElem?_append_right (by omega), hlen]
      simp

lemma dec_length (N : ℕ) (h : List Bool) : (dec N h).length = h.length / N := by
  simp [dec]

/-- On the event that every block decoded correctly, the decoded list *is* the noiseless run. -/
lemma dec_eq_ideal {truth : X → Bool} {qry : List Bool → X} {N B : ℕ} (hN : 0 < N)
    (h : List Bool) (hlen : h.length = B * N) (hOk : Ok truth qry N B h) :
    dec N h = ideal truth qry B := by
  have hdiv : h.length / N = B := by rw [hlen]; exact Nat.mul_div_cancel _ hN
  refine List.ext_getElem? fun j => ?_
  by_cases hj : j < B
  · rw [ideal_getElem? truth qry B j hj]
    simp only [dec, hdiv, List.getElem?_map, List.getElem?_range hj, Option.map_some]
    rw [hOk j hj]
  · have h1 : (dec N h).length = B := by rw [dec_length, hdiv]
    have h2 : (ideal truth qry B).length = B := ideal_length truth qry B
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- Decoding does not change inside an incomplete block. -/
lemma dec_append_short {N j : ℕ} (hN : 0 < N) (h₀ w : List Bool) (hlen : h₀.length = j * N)
    (hw : w.length < N) : dec N (h₀ ++ w) = dec N h₀ := by
  have hd0 : h₀.length / N = j := by rw [hlen]; exact Nat.mul_div_cancel _ hN
  have hd1 : (h₀ ++ w).length / N = j := by
    rw [List.length_append, hlen]
    rw [Nat.mul_comm j N, Nat.mul_add_div hN, Nat.div_eq_of_lt hw, Nat.add_zero]
  unfold dec
  rw [hd0, hd1]
  refine List.map_congr_left ?_
  intro r hr
  rw [List.mem_range] at hr
  exact blk_append h₀ w (by rw [hlen]; nlinarith)

/-- `Ok` depends only on the first `j·N` bits. -/
lemma Ok_append {truth : X → Bool} {qry : List Bool → X} {N j : ℕ} (h₁ w : List Bool)
    (hlen : j * N ≤ h₁.length) :
    Ok truth qry N j (h₁ ++ w) ↔ Ok truth qry N j h₁ := by
  have hb : ∀ r < j, blk N r (h₁ ++ w) = blk N r h₁ := by
    intro r hr
    exact blk_append h₁ w (by nlinarith)
  constructor
  · intro hok r hr; rw [← hb r hr]; exact hok r hr
  · intro hok r hr; rw [hb r hr]; exact hok r hr

/-- `errAt j` depends only on the first `(j+1)·N` bits. -/
lemma errAt_append {truth : X → Bool} {qry : List Bool → X} {N j : ℕ} (h₂ w : List Bool)
    (hlen : (j + 1) * N ≤ h₂.length) :
    errAt truth qry N j (h₂ ++ w) = errAt truth qry N j h₂ := by
  have hj : j * N ≤ h₂.length := by nlinarith
  have hb : blk N j (h₂ ++ w) = blk N j h₂ := blk_append h₂ w hlen
  unfold errAt
  exact if_congr (and_congr (Ok_append h₂ w hj) (by rw [hb])) rfl rfl

/-! ### Lemma 4.1.2 (Chernoff) at an arbitrary starting history -/

/-- **Lemma 4.1.2**, in the form needed for one block: if the probe is `x` throughout the next
`N` rounds, `b₀` is the bit that `x` returns with probability `ρ`, and `F` is dominated by the
indicator that `b₀` occurs at least `N/2` times in those rounds, then `E[F] ≤ e^{−N·C_ch(ρ)}`. -/
lemma chernoff_block {p : X → ℝ} (probe : List Bool → X) (x : X) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hp : ∀ y, 0 ≤ p y ∧ p y ≤ 1)
    (b₀ : Bool) (hq : bern (p x) b₀ = ρ) (N : ℕ) (h₁ : List Bool)
    (hprobe : ∀ h', h₁ <+: h' → h'.length < h₁.length + N → probe h' = x)
    (F : List Bool → ℝ)
    (hF : ∀ h', h₁ <+: h' → h'.length = h₁.length + N →
      F h' ≤ (if (N : ℝ) / 2 ≤ ((h'.count b₀ : ℝ) - (h₁.count b₀ : ℝ)) then 1 else 0)) :
    val p probe F N h₁ ≤ Real.exp (-(N * Cch ρ)) := by
  set μ := Real.sqrt ((1 - ρ) / ρ) with hμdef
  have hr : 1 ≤ (1 - ρ) / ρ := by rw [le_div_iff₀ hρ0]; linarith
  have hμ : 1 ≤ μ := by rw [hμdef]; exact Real.one_le_sqrt.2 hr
  have hμ0 : 0 < μ := by linarith
  have hμ2 : μ ^ 2 = (1 - ρ) / ρ := Real.sq_sqrt (by linarith)
  set c₀ := h₁.count b₀ with hc₀
  set M : List Bool → ℝ := fun h' => (μ ^ 2) ^ (h'.count b₀) / (μ ^ N * (μ ^ 2) ^ c₀) with hM
  -- Step 1: dominate the leaf function by the exponential moment.
  have step1 : val p probe F N h₁ ≤ val p probe M N h₁ := by
    refine val_mono_pre probe hp N h₁ ?_
    intro h' hpre hl
    obtain ⟨w, rfl⟩ := hpre
    have hcnt : (h₁ ++ w).count b₀ = c₀ + w.count b₀ := by rw [List.count_append]
    have hmom := ind_le_moment (μ := μ) hμ N (w.count b₀)
    have hind : (if (N : ℝ) / 2 ≤ ((h₁ ++ w).count b₀ : ℝ) - (c₀ : ℝ) then (1 : ℝ) else 0)
        = (if (N : ℝ) / 2 ≤ (w.count b₀ : ℝ) then (1 : ℝ) else 0) := by
      refine if_congr ?_ rfl rfl
      rw [hcnt]; push_cast; constructor <;> intro h <;> linarith
    have hMeq : M (h₁ ++ w) = (μ ^ 2) ^ (w.count b₀) / μ ^ N := by
      have hne : ((μ ^ 2) ^ c₀ : ℝ) ≠ 0 := by positivity
      have hnN : (μ ^ N : ℝ) ≠ 0 := by positivity
      simp only [hM, hcnt, pow_add]
      field_simp
    calc F (h₁ ++ w)
        ≤ (if (N : ℝ) / 2 ≤ ((h₁ ++ w).count b₀ : ℝ) - (c₀ : ℝ) then (1 : ℝ) else 0) :=
          hF _ ⟨w, rfl⟩ hl
      _ = (if (N : ℝ) / 2 ≤ (w.count b₀ : ℝ) then (1 : ℝ) else 0) := hind
      _ ≤ (μ ^ 2) ^ (w.count b₀) / μ ^ N := hmom
      _ = M (h₁ ++ w) := hMeq.symm
  -- Step 2: the probe is constant over the block.
  have step2 : val p probe M N h₁ = val p (fun _ => x) M N h₁ :=
    val_congr_probe probe (fun _ => x) M N h₁ (fun h' hpre hl => hprobe h' hpre hl)
  -- Step 3: evaluate the exponential moment.
  have step3 : val p (fun _ => x) M N h₁ = (2 * (1 - ρ)) ^ N / μ ^ N := by
    have haff : val p (fun _ => x) M N h₁ =
        val p (fun _ => x) (fun h' => 0 + (μ ^ N * (μ ^ 2) ^ c₀)⁻¹ * (μ ^ 2) ^ (h'.count b₀))
          N h₁ := by
      refine val_mono_eq (fun h' _ => ?_)
      simp only [hM]; ring
    rw [haff, val_affine p (fun _ => x) 0 ((μ ^ N * (μ ^ 2) ^ c₀)⁻¹)
      (fun h' => (μ ^ 2) ^ (h'.count b₀)) N h₁,
      val_pow_count p (fun _ => x) (p x) (fun _ => rfl) b₀ (μ ^ 2) N h₁, hq, hμ2]
    have hk : ρ * ((1 - ρ) / ρ) + (1 - ρ) = 2 * (1 - ρ) := by field_simp; ring
    rw [hk, ← hc₀]
    have hne : (μ ^ N * (μ ^ 2) ^ c₀) ≠ 0 := by positivity
    field_simp
    ring
  -- Step 4: identify the constant with `e^{−N C_ch(ρ)}`.
  have step4 : (2 * (1 - ρ)) ^ N / μ ^ N = (2 * Real.sqrt (ρ * (1 - ρ))) ^ N := by
    rw [← div_pow]
    congr 1
    have hs : Real.sqrt (ρ * (1 - ρ)) = (1 - ρ) * Real.sqrt (ρ / (1 - ρ)) := by
      rw [show ρ * (1 - ρ) = (1 - ρ) ^ 2 * (ρ / (1 - ρ)) by field_simp,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
    rw [hs, hμdef, div_eq_mul_inv, ← Real.sqrt_inv, inv_div]
    ring
  rw [step2, step3, step4] at step1
  rwa [pow_two_sqrt_eq_exp hρ0 hρ1 N] at step1

/-! ### One block decodes wrongly with probability `≤ e^{−N C_ch(ρ)}` -/

variable {p : X → ℝ} {truth : X → Bool} {qry : List Bool → X} {ρ : ℝ}

lemma p_mem_Icc (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hp : ∀ x, p x = if truth x then 1 - ρ else ρ)
    (x : X) : 0 ≤ p x ∧ p x ≤ 1 := by
  rw [hp]; split_ifs <;> constructor <;> linarith

/-- **Block error bound.** Started from any history of length `j·N`, the probability that block
`j` decodes to the wrong answer *and* all earlier blocks were right is `≤ e^{−N·C_ch(ρ)}`. -/
theorem block_err (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hp : ∀ x, p x = if truth x then 1 - ρ else ρ) {N : ℕ} (hN : 0 < N) (j : ℕ) (h₁ : List Bool)
    (hlen : h₁.length = j * N) :
    val p (probeMaj N qry) (errAt truth qry N j) N h₁ ≤ Real.exp (-(N * Cch ρ)) := by
  have hpb := p_mem_Icc hρ0 hρ1 hp
  by_cases hok : Ok truth qry N j h₁
  · -- the interesting case: apply Chernoff to this block
    have hdec : dec N h₁ = ideal truth qry j := dec_eq_ideal hN h₁ hlen hok
    set x := qry (ideal truth qry j) with hx
    have htx : truth x = ibit truth qry j := rfl
    refine chernoff_block (probeMaj N qry) x hρ0 hρ1 hpb (!(ibit truth qry j)) ?_ N h₁ ?_
      (errAt truth qry N j) ?_
    · -- `x` returns the *wrong* bit with probability `ρ`
      rw [hp, htx]
      cases hb : ibit truth qry j <;> simp [bern]
    · -- the probe is `x` throughout the block
      intro h' hpre hl
      obtain ⟨w, rfl⟩ := hpre
      have hw : w.length < N := by simp at hl; omega
      rw [probeMaj, dec_append_short hN h₁ w hlen hw, hdec]
    · -- the error indicator is dominated by "the wrong bit occurred ≥ N/2 times"
      intro h' hpre hl
      obtain ⟨w, rfl⟩ := hpre
      have hwl : w.length = N := by simp at hl; omega
      have hcnt : ((h₁ ++ w).count (!(ibit truth qry j)) : ℝ) - (h₁.count (!(ibit truth qry j)) : ℝ)
          = (w.count (!(ibit truth qry j)) : ℝ) := by
        rw [List.count_append]; push_cast; ring
      have hsum : w.count true + w.count false = N := by
        rw [← hwl]; exact Gallery.count_true_add_false w
      rw [hcnt]
      unfold errAt
      by_cases herr : Ok truth qry N j (h₁ ++ w) ∧ blk N j (h₁ ++ w) ≠ ibit truth qry j
      · -- the error happened: the wrong bit occurred at least `N/2` times
        have hcond : (N : ℝ) / 2 ≤ (w.count (!(ibit truth qry j)) : ℝ) := by
          obtain ⟨-, hne⟩ := herr
          rw [blk_last h₁ w hlen hwl] at hne
          cases hb : ibit truth qry j
          · -- correct answer `false`, decoded `true`: `count true > N/2`
            rw [hb] at hne
            have hmt : majBit N w = true := by
              cases hm : majBit N w
              · exact absurd hm hne
              · rfl
            have hlt : N < 2 * w.count true := by
              simpa [majBit] using hmt
            simp only [Bool.not_false]
            have hle : (N : ℝ) ≤ 2 * (w.count true : ℝ) := by exact_mod_cast hlt.le
            linarith
          · -- correct answer `true`, decoded `false`: `count false ≥ N/2`
            rw [hb] at hne
            have hmf : majBit N w = false := by
              cases hm : majBit N w
              · rfl
              · exact absurd hm hne
            have hnot : ¬ (N < 2 * w.count true) := by
              simpa [majBit] using hmf
            have hge : N ≤ 2 * w.count false := by omega
            simp only [Bool.not_true]
            have hle : (N : ℝ) ≤ 2 * (w.count false : ℝ) := by exact_mod_cast hge
            linarith
        rw [if_pos herr, if_pos hcond]
      · rw [if_neg herr]
        split_ifs <;> norm_num
  · -- an earlier block was already wrong: the indicator vanishes identically
    refine le_trans (le_of_eq ?_) (Real.exp_nonneg _)
    refine val_eq_zero_of_vanish (probeMaj N qry) (errAt truth qry N j) N h₁
      (fun h' hpre hl => ?_)
    obtain ⟨w, rfl⟩ := hpre
    unfold errAt
    refine if_neg ?_
    rintro ⟨hok', -⟩
    exact hok ((Ok_append (truth := truth) (qry := qry) (j := j) h₁ w (by omega)).1 hok')

/-! ### Union bound over the `B` comparisons -/

lemma errAt_val_le (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hp : ∀ x, p x = if truth x then 1 - ρ else ρ) {N : ℕ} (hN : 0 < N) {B j : ℕ} (hj : j < B) :
    val p (probeMaj N qry) (errAt truth qry N j) (B * N) [] ≤ Real.exp (-(N * Cch ρ)) := by
  have hpb := p_mem_Icc hρ0 hρ1 hp
  obtain ⟨c, hc⟩ : ∃ c, B = j + 1 + c := ⟨B - j - 1, by omega⟩
  have hsplit : B * N = j * N + (N + c * N) := by subst hc; ring
  rw [hsplit, val_add_rounds]
  refine le_trans (val_mono _ hpb (j * N) [] ?_)
    (le_of_eq (val_const p (probeMaj N qry) (Real.exp (-(N * Cch ρ))) (j * N) []))
  intro h₁ hl
  simp only [List.length_nil, zero_add] at hl
  rw [val_add_rounds]
  have hinner : val p (probeMaj N qry)
      (fun h₂ => val p (probeMaj N qry) (errAt truth qry N j) (c * N) h₂) N h₁ =
      val p (probeMaj N qry) (errAt truth qry N j) N h₁ := by
    refine val_congr_prefix' p (probeMaj N qry) N h₁ (fun h₂ hpre hl2 => ?_)
    refine val_of_const_on (probeMaj N qry) (errAt truth qry N j) (c * N) h₂
      (fun h₃ hpre3 hl3 => ?_)
    obtain ⟨w, rfl⟩ := hpre3
    exact errAt_append h₂ w (by rw [hl2, hl]; ring_nf; omega)
  rw [hinner]
  exact block_err hρ0 hρ1 hp hN j h₁ hl

open Classical in
/-- If the decoded list is not the noiseless transcript, some block was the first to go wrong. -/
lemma not_ok_le_sum {N : ℕ} (hN : 0 < N) (B : ℕ) (h : List Bool) (hlen : h.length = B * N) :
    (if dec N h = ideal truth qry B then (0 : ℝ) else 1) ≤
      ∑ j ∈ Finset.range B, errAt truth qry N j h := by
  split_ifs with hd
  · exact Finset.sum_nonneg fun j _ => by unfold errAt; split_ifs <;> norm_num
  · have hnok : ¬ Ok truth qry N B h := fun hok => hd (dec_eq_ideal hN h hlen hok)
    have hex : ∃ r, r < B ∧ blk N r h ≠ ibit truth qry r := by
      by_contra hcon
      push Not at hcon
      exact hnok fun r hr => hcon r hr
    classical
    set j := Nat.find hex with hjdef
    obtain ⟨hjB, hjne⟩ := Nat.find_spec hex
    have hmin : Ok truth qry N j h := by
      intro r hr
      by_contra hne
      exact absurd ⟨lt_trans hr hjB, hne⟩ (Nat.find_min hex hr)
    have h1 : errAt truth qry N j h = 1 := by unfold errAt; rw [if_pos ⟨hmin, hjne⟩]
    calc (1 : ℝ) = errAt truth qry N j h := h1.symm
      _ ≤ ∑ j ∈ Finset.range B, errAt truth qry N j h :=
        Finset.single_le_sum (f := fun j => errAt truth qry N j h)
          (fun i _ => by unfold errAt; split_ifs <;> norm_num) (Finset.mem_range.2 hjB)

open Classical in
/-- **Union bound.** After `B·N` rounds the decoded transcript differs from the noiseless one
with probability at most `B·e^{−N·C_ch(ρ)}`. -/
theorem decode_union (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hp : ∀ x, p x = if truth x then 1 - ρ else ρ) {N : ℕ} (hN : 0 < N) (B : ℕ) :
    val p (probeMaj N qry) (fun h => if dec N h = ideal truth qry B then (0 : ℝ) else 1)
      (B * N) [] ≤ B * Real.exp (-(N * Cch ρ)) := by
  have hpb := p_mem_Icc hρ0 hρ1 hp
  calc val p (probeMaj N qry) (fun h => if dec N h = ideal truth qry B then (0 : ℝ) else 1)
        (B * N) []
      ≤ val p (probeMaj N qry) (fun h => ∑ j ∈ Finset.range B, errAt truth qry N j h)
        (B * N) [] := by
        refine val_mono _ hpb (B * N) [] (fun h' hl => ?_)
        exact not_ok_le_sum hN B h' (by simpa using hl)
    _ = ∑ j ∈ Finset.range B, val p (probeMaj N qry) (errAt truth qry N j) (B * N) [] :=
        val_sum p (probeMaj N qry) (Finset.range B) (fun j h => errAt truth qry N j h) (B * N) []
    _ ≤ ∑ _j ∈ Finset.range B, Real.exp (-(N * Cch ρ)) :=
        Finset.sum_le_sum fun j hj =>
          errAt_val_le hρ0 hρ1 hp hN (Finset.mem_range.1 hj)
    _ = B * Real.exp (-(N * Cch ρ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

open Classical in
/-- **Remark 4.3.7, (P) half, per-block form.** Majority vote over blocks of `N` probes
reproduces the whole noiseless run with probability `≥ 1 − B·e^{−N·C_ch(ρ)}`, at `B·N` queries. -/
theorem noisy_majority (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hp : ∀ x, p x = if truth x then 1 - ρ else ρ) {N : ℕ} (hN : 0 < N) (B : ℕ) :
    1 - B * Real.exp (-(N * Cch ρ)) ≤
      val p (probeMaj N qry) (fun h => if dec N h = ideal truth qry B then (1 : ℝ) else 0)
        (B * N) [] := by
  have hid : ∀ h : List Bool, (if dec N h = ideal truth qry B then (0 : ℝ) else 1) =
      1 + (-1) * (if dec N h = ideal truth qry B then (1 : ℝ) else 0) := by
    intro h; split_ifs <;> ring
  have hval := decode_union hρ0 hρ1 hp hN (qry := qry) B
  rw [show (fun h => if dec N h = ideal truth qry B then (0 : ℝ) else 1) =
      (fun h => 1 + (-1) * (if dec N h = ideal truth qry B then (1 : ℝ) else 0)) from
      funext hid,
    val_affine p (probeMaj N qry) 1 (-1)
      (fun h => if dec N h = ideal truth qry B then (1 : ℝ) else 0) (B * N) []] at hval
  linarith

/-! ### Remark 4.3.7, (P) half -/

/-- `N₂ = ⌈log(2B/δ)/C_ch(ρ)⌉`, the block size of Remark 4.3.7. -/
noncomputable def N₂ (ρ δ : ℝ) (B : ℕ) : ℕ := ⌈Real.log (2 * B / δ) / Cch ρ⌉₊

lemma N₂_pos {δ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {B : ℕ}
    (hB : 0 < B) : 0 < N₂ ρ δ B := by
  have hC := Cch_pos hρ0 hρ1
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have h2 : (1 : ℝ) < 2 * B / δ := by
    rw [lt_div_iff₀ hδ0]; nlinarith
  have hlog : 0 < Real.log (2 * B / δ) := Real.log_pos h2
  exact Nat.ceil_pos.2 (div_pos hlog hC)

lemma B_exp_le {δ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hδ0 : 0 < δ) {B : ℕ} (hB : 0 < B) :
    (B : ℝ) * Real.exp (-((N₂ ρ δ B : ℝ) * Cch ρ)) ≤ δ / 2 := by
  have hC := Cch_pos hρ0 hρ1
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hx : (0 : ℝ) < 2 * B / δ := by positivity
  have hceil : Real.log (2 * B / δ) / Cch ρ ≤ (N₂ ρ δ B : ℝ) := Nat.le_ceil _
  have hmul : Real.log (2 * B / δ) ≤ (N₂ ρ δ B : ℝ) * Cch ρ := by
    rw [div_le_iff₀ hC] at hceil; exact hceil
  have hexp : Real.exp (-((N₂ ρ δ B : ℝ) * Cch ρ)) ≤ Real.exp (-Real.log (2 * B / δ)) :=
    Real.exp_le_exp.2 (by linarith)
  have hval : Real.exp (-Real.log (2 * B / δ)) = δ / (2 * B) := by
    rw [Real.exp_neg, Real.exp_log hx]
    field_simp
  calc (B : ℝ) * Real.exp (-((N₂ ρ δ B : ℝ) * Cch ρ))
      ≤ (B : ℝ) * (δ / (2 * B)) := by rw [← hval]; exact mul_le_mul_of_nonneg_left hexp hB0.le
    _ = δ / 2 := by field_simp

open Classical in
/-- **Remark 4.3.7, the (P) half.** Under `K1(ρ)`, taking each of the `B` comparisons of a
deterministic noiseless algorithm `(qry, out)` by majority vote of `N₂ = ⌈log(2B/δ)/C_ch(ρ)⌉`
probes costs `B·N₂` queries and succeeds with probability `≥ 1 − δ`: for *any* success predicate
`S` that the noiseless run satisfies (`hS`), the noisy run satisfies it with probability
`≥ 1 − δ`. -/
theorem noisy_majority_succeeds {Y : Type*} (out : List Bool → Y) (S : Y → Prop)
    {δ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hp : ∀ x, p x = if truth x then 1 - ρ else ρ) {B : ℕ} (hB : 0 < B)
    (hS : S (out (ideal truth qry B))) :
    1 - δ ≤ val p (probeMaj (N₂ ρ δ B) qry)
      (fun h => if S (out (dec (N₂ ρ δ B) h)) then (1 : ℝ) else 0) (B * N₂ ρ δ B) [] := by
  have hpb := p_mem_Icc hρ0 hρ1 hp
  have hN := N₂_pos hρ0 hρ1 hδ0 hδ1 hB
  have hmain := noisy_majority (qry := qry) hρ0 hρ1 hp hN B
  have hmono : val p (probeMaj (N₂ ρ δ B) qry)
      (fun h => if dec (N₂ ρ δ B) h = ideal truth qry B then (1 : ℝ) else 0)
      (B * N₂ ρ δ B) [] ≤
      val p (probeMaj (N₂ ρ δ B) qry)
      (fun h => if S (out (dec (N₂ ρ δ B) h)) then (1 : ℝ) else 0) (B * N₂ ρ δ B) [] := by
    refine val_mono _ hpb (B * N₂ ρ δ B) [] (fun h' _ => ?_)
    split_ifs with h1 h2
    · exact le_refl _
    · exact absurd (by rw [h1]; exact hS) h2
    · norm_num
    · exact le_refl _
  have hBexp := B_exp_le hρ0 hρ1 hδ0 hB
  linarith

/-! ### Sanity checks on the wrapper (non-vacuity of the definitions) -/

section Sanity

/-- With blocks of one probe, decoding is the identity: the wrapper degenerates to the
noiseless attacker driven by the raw bits. -/
example : dec 1 [true, false, true] = [true, false, true] := by decide

/-- Majority of three: two `true`s decode to `true`, one does not. -/
example : majBit 3 [true, true, false] = true := by decide

example : majBit 3 [true, false, false] = false := by decide

/-- Ties decode to `false`. -/
example : majBit 2 [true, false] = false := by decide

/-- Incomplete blocks are not decoded. -/
example : dec 3 [true, true, true, true] = [true] := by decide

/-- The noiseless run of a constant algorithm. -/
example (x : Bool) : ideal (fun _ : Unit => x) (fun _ => ()) 2 = [x, x] := by
  simp [ideal]

end Sanity

end OracleBounds.Attacks
