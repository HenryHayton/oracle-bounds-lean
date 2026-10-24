import OracleBounds.V6.Process

/-!
# Weighted ghost coupling for a general (non-uniform) prior

This is the `n-face-general-prior-v1` note's Lemma 4.1 engine, generalising
`OracleBounds.V6.ghost_union_bound` (built for a *uniform* average over a finite set of caps `S`,
with `|S|` in the denominator) to an arbitrary finite prior weight `π : Fine → ℝ` (`π ≥ 0`,
`∑ π = 1`) with no division needed, and no set `S` (the whole `Fine` type is the support).

Everything here is proved; there are no `sorry`s. `OracleBounds.V6.val`, `hitBy`, `val_coupling`
and `hitInd` are reused unchanged — the ghost coupling itself does not care whether the average
over the hidden value is uniform or not.
-/

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {X : Type*}

/-- Weighted analogue of `OracleBounds.V6.card_reached_le`: if every point `x` has prior mass at
most `c` under the "reached" caps, then along any indexed list of points, the expected mass of
values reached by *some* point is at most `(number of points) · c`. -/
lemma mass_reached_le {Fine ι : Type*} [Fintype Fine] (π : Fine → ℝ) (reach : Fine → X → Prop)
    [∀ l x, Decidable (reach l x)] (c : ℝ) (hπ0 : ∀ l, 0 ≤ π l)
    (hcov : ∀ x, (∑ l ∈ Finset.univ.filter (reach · x), π l) ≤ c)
    (pts : Finset ι) (y : ι → X) [∀ l, Decidable (∃ i ∈ pts, reach l (y i))] :
    ∑ l, π l * (if ∃ i ∈ pts, reach l (y i) then (1 : ℝ) else 0) ≤ pts.card * c := by
  calc ∑ l, π l * (if ∃ i ∈ pts, reach l (y i) then (1 : ℝ) else 0)
      ≤ ∑ l, π l * ∑ i ∈ pts, (if reach l (y i) then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro l _
        apply mul_le_mul_of_nonneg_left _ (hπ0 l)
        split_ifs with hl
        · obtain ⟨i, hi, hr⟩ := hl
          calc (1 : ℝ) = if reach l (y i) then 1 else 0 := by simp [hr]
            _ ≤ _ := Finset.single_le_sum (f := fun i => if reach l (y i) then (1 : ℝ) else 0)
                (fun _ _ => by split_ifs <;> norm_num) hi
        · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    _ = ∑ i ∈ pts, ∑ l, π l * (if reach l (y i) then (1 : ℝ) else 0) := by
        rw [show (∑ l, π l * ∑ i ∈ pts, (if reach l (y i) then (1 : ℝ) else 0)) =
          ∑ l, ∑ i ∈ pts, π l * (if reach l (y i) then (1 : ℝ) else 0) from
          Finset.sum_congr rfl fun l _ => Finset.mul_sum _ _ _]
        exact Finset.sum_comm
    _ = ∑ i ∈ pts, ∑ l ∈ Finset.univ.filter (reach · (y i)), π l := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun l _ => by split_ifs <;> ring
    _ ≤ ∑ _i ∈ pts, c := Finset.sum_le_sum (fun i _ => hcov (y i))
    _ = pts.card * c := by simp

open Classical in
/-- **Weighted ghost union bound** (Lemma 4.1's engine for a general prior).

Setting: one face, hidden value `l ∼ π`. `pT l` is the true response probability when the face
takes value `l`; `pG` is the ghost one (face deleted / replaced by a fixed environment). `A l` is
the bad event for value `l` (`[0,1]`-valued leaf function), contained in "`l` was hit, or `E l`
happened", where `E l` are `[0,1]`-valued leaf events with total weighted mass at most `K` on
every length-`Q` transcript.

Conclusion: `∑ₗ π(l)·val (pT l) probe (A l) Q [] ≤ Q·c + K + 2Qζ`. No division by a cardinality
is needed: the prior already sums to `1`. -/
theorem ghost_bound_weighted {Fine : Type*} [Fintype Fine] (π : Fine → ℝ)
    (reach : Fine → X → Prop) [∀ l x, Decidable (reach l x)]
    (probe : List Bool → X) (pT : Fine → X → ℝ) (pG : X → ℝ) (ζ c K : ℝ) (Q : ℕ)
    (A E : Fine → List Bool → ℝ)
    (hπ0 : ∀ l, 0 ≤ π l) (hπ1 : ∑ l, π l = 1)
    (hpT : ∀ l x, 0 ≤ pT l x ∧ pT l x ≤ 1) (hpG : ∀ x, 0 ≤ pG x ∧ pG x ≤ 1) (hζ : 0 ≤ ζ)
    (hloc : ∀ l, ∀ x, ¬ reach l x → |pT l x - pG x| ≤ 2 * ζ)
    (hcov : ∀ x, (∑ l ∈ Finset.univ.filter (reach · x), π l) ≤ c)
    (hE : ∀ l h, 0 ≤ E l h ∧ E l h ≤ 1)
    (hK : ∀ h : List Bool, h.length = Q → ∑ l, π l * E l h ≤ K)
    (hA : ∀ l, ∀ h : List Bool, h.length = Q →
      A l h ≤ 1 - (1 - hitInd reach probe l h) * (1 - E l h)) :
    ∑ l, π l * val (pT l) probe (A l) Q [] ≤ Q * c + K + 2 * Q * ζ := by
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
      Q * c + K := by
    have hb : val pG probe (fun h => ∑ l, π l * (hitInd reach probe l h + E l h)) Q [] ≤
        val pG probe (fun _ => Q * c + K) Q [] := by
      apply val_mono probe hpG Q []
      intro h' hl
      simp only [List.length_nil, zero_add] at hl
      have hc : ∑ l, π l * hitInd reach probe l h' ≤ (h'.length : ℝ) * c := by
        have hpts := mass_reached_le π reach c hπ0 hcov (Finset.range h'.length)
          (fun k => probe (h'.take k))
        rw [Finset.card_range] at hpts
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_)) hpts
        congr 1
        unfold hitInd hitBy
        by_cases hx : ∃ k < h'.length, reach l (probe (h'.take k)) <;> simp [hx]
      have hKb := hK h' hl
      rw [hl] at hc
      calc ∑ l, π l * (hitInd reach probe l h' + E l h')
          = ∑ l, π l * hitInd reach probe l h' + ∑ l, π l * E l h' := by
            rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun l _ => by ring
        _ ≤ Q * c + K := by linarith
    rwa [val_const] at hb
  linarith [step1, step2 ▸ step3]

end OracleBounds.GeneralPrior
