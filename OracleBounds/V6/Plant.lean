import OracleBounds.V6.Operational

/-!
# The full n-face plant (v6/v7 §3) and plant-level operational theorems

This removes the per-face caveats of `OracleBounds.V6.Operational`: galleries are
`W : ι → Cap` injective (distinct caps) and `V : ι → Fine`, averaged uniformly; the oracle answers
with `κ(maxᵢ ⟨x, g(Wᵢ, Vᵢ)⟩)`. For each face `i` we build the `FaceSetting` of the environment
(the other faces) and transfer the per-face bounds by an exact double-counting identity
(`sum_injs_update`): re-sampling face `i`'s cap over the free caps permutes the injections.

No `sorry`s. Hypotheses: spread-family coverage over all caps, unit 1-separated centres,
`‖g c l − z c‖ ≤ r₀`, the kernel, and condition (1) `2 ≤ n`, `2n ≤ M` (`n = |ι|`, `M = |Cap|`).
Sums over `V` are kept outside: every bound holds for each fixed `V`, hence for the average.
-/

namespace OracleBounds.V6

open Finset Function Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Cap Fine : Type*} [Fintype ι] [Nonempty ι] [Fintype Cap] [Fintype Fine]

/-- The planted construction: cap centres, the fine templates in each cap, the kernel. -/
structure PlantData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Cap Fine : Type*) where
  z : Cap → E
  g : Cap → Fine → E
  thr : ℝ
  r₀ : ℝ
  κ : ℝ → ℝ
  ν₀ : ℝ
  ζ : ℝ
  hz : ∀ c, ‖z c‖ = 1
  hsep : ∀ c c', c ≠ c' → 1 ≤ ‖z c - z c'‖
  hg : ∀ c l, ‖g c l - z c‖ ≤ r₀
  hκ : ∀ s, 0 ≤ κ s ∧ κ s ≤ 1
  hband : ∀ s ≤ thr, |κ s - ν₀| ≤ ζ

namespace PlantData

variable (P : PlantData E Cap Fine)

/-- Oracle score of probe `x` against gallery `(W, V)`: `maxᵢ ⟨x, g(Wᵢ, Vᵢ)⟩`. -/
noncomputable def score (W : ι → Cap) (V : ι → Fine) (x : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => inner ℝ x (P.g (W j) (V j)))

/-- Probability of answer 1 to probe `x` against gallery `(W, V)`. -/
noncomputable def resp (W : ι → Cap) (V : ι → Fine) (x : Sph E) : ℝ := P.κ (P.score W V x.1)

/-- Galleries' cap assignments: injective maps faces → caps. -/
noncomputable def injs : Finset (ι → Cap) := Finset.univ.filter Injective

/-- Caps not used by faces other than `i`. -/
noncomputable def free (W : ι → Cap) (i : ι) : Finset Cap :=
  Finset.univ.filter (fun c => ∀ j, j ≠ i → W j ≠ c)

lemma card_free {W : ι → Cap} (hW : Injective W) (i : ι) :
    ((free W i).card : ℝ) = Fintype.card Cap - Fintype.card ι + 1 := by
  have himg : free W i = Finset.univ \ (Finset.univ.erase i).image W := by
    ext c; simp [free]
  have hcard_img : ((Finset.univ.erase i).image W).card = Fintype.card ι - 1 := by
    rw [Finset.card_image_of_injective _ hW, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ]
  have hle : Fintype.card ι ≤ Fintype.card Cap := Fintype.card_le_of_injective W hW
  have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos
  rw [himg, Finset.card_sdiff_of_subset (Finset.subset_univ _), hcard_img, Finset.card_univ]
  rw [Nat.cast_sub (by omega), Nat.cast_sub hpos]
  ring

omit [Nonempty ι] in
/-- **Exact double counting.** Re-sampling face `i`'s cap uniformly over its free caps is a
permutation-invariant operation on injections. -/
theorem sum_injs_update (i : ι) (F : (ι → Cap) → ℝ) :
    ∑ W ∈ injs, ∑ w ∈ free W i, F (update W i w) = ∑ W ∈ injs, ((free W i).card : ℝ) * F W := by
  set T := (injs (ι := ι) (Cap := Cap) ×ˢ (Finset.univ : Finset Cap)).filter (fun x => x.2 ∈ free x.1 i)
  have hL : ∑ W ∈ injs, ∑ w ∈ free W i, F (update W i w) = ∑ x ∈ T, F (update x.1 i x.2) := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun W _ => ?_
    rw [← Finset.sum_filter]; congr 1; ext c; simp
  have hR : ∑ W ∈ injs, ((free W i).card : ℝ) * F W = ∑ x ∈ T, F x.1 := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun W _ => ?_
    rw [← Finset.sum_filter]; simp
  rw [hL, hR]
  -- the involution (W, w) ↦ (update W i w, W i)
  have hmem : ∀ x ∈ T, ((update x.1 i x.2, x.1 i) : (ι → Cap) × Cap) ∈ T := by
    intro x hx
    simp only [T, injs, free, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      and_true] at hx ⊢
    obtain ⟨hinj, hfree⟩ := hx
    constructor
    · intro a b hab
      by_cases ha : a = i <;> by_cases hb : b = i
      · rw [ha, hb]
      · subst ha; rw [update_self, update_of_ne hb] at hab; exact absurd hab.symm (hfree b hb)
      · subst hb; rw [update_self, update_of_ne ha] at hab; exact absurd hab (hfree a ha)
      · rw [update_of_ne ha, update_of_ne hb] at hab; exact hinj hab
    · intro j hj; rw [update_of_ne hj]; exact fun h => hj (hinj h)
  refine Finset.sum_nbij' (fun x => (update x.1 i x.2, x.1 i)) (fun x => (update x.1 i x.2, x.1 i))
    hmem hmem ?_ ?_ ?_
  · intro x _; simp
  · intro x _; simp
  · intro x _; simp

/-- Transfer a per-environment sum bound to the plant average over injections. -/
theorem plant_bound (i : ι) (F : (ι → Cap) → ℝ) (B : ℝ) (hn : Fintype.card ι ≤ Fintype.card Cap)
    (hface : ∀ W ∈ injs, ∑ w ∈ free W i, F (update W i w) ≤ B * (free W i).card) :
    ∑ W ∈ injs, F W ≤ B * (injs : Finset (ι → Cap)).card := by
  set s : ℝ := Fintype.card Cap - Fintype.card ι + 1
  have hs : 0 < s := by
    have : (Fintype.card ι : ℝ) ≤ Fintype.card Cap := by exact_mod_cast hn
    simp only [s]; linarith
  have hcard : ∀ W ∈ (injs : Finset (ι → Cap)), ((free W i).card : ℝ) = s := by
    intro W hW; simp only [injs, Finset.mem_filter] at hW; exact card_free hW.2 i
  have h := sum_injs_update i F
  have h' : ∑ W ∈ injs, ((free W i).card : ℝ) * F W = s * ∑ W ∈ injs, F W := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun W hW => by rw [hcard W hW]
  have h2 : s * ∑ W ∈ injs, F W ≤ s * (B * (injs : Finset (ι → Cap)).card) := by
    rw [← h', ← h]
    calc ∑ W ∈ injs, ∑ w ∈ free W i, F (update W i w) ≤ ∑ W ∈ (injs : Finset (ι → Cap)), B * s :=
          Finset.sum_le_sum fun W hW => by rw [← hcard W hW]; exact hface W hW
      _ = s * (B * (injs : Finset (ι → Cap)).card) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  exact le_of_mul_le_mul_left h2 hs

/-- Face `i`'s environment in gallery `(W, V)` as a `FaceSetting` (needs a second face). -/
noncomputable def face (W : ι → Cap) (V : ι → Fine) (i : ι) (hn : 2 ≤ Fintype.card ι) :
    FaceSetting E Cap where
  S := free W i
  z := P.z
  g := fun c => P.g c (V i)
  thr := P.thr
  r₀ := P.r₀
  κ := P.κ
  ν₀ := P.ν₀
  ζ := P.ζ
  m := fun x => (Finset.univ.erase i).sup'
    (Finset.card_pos.1 (by rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]; omega))
    (fun j => inner ℝ x (P.g (W j) (V j)))
  hg := fun w _ => P.hg w (V i)
  hκ := P.hκ
  hband := P.hband

/-- The true process of `face W V i` in cap `w` is the gallery `(update W i w, V)`. -/
lemma face_pT (W : ι → Cap) (V : ι → Fine) (i : ι) (hn : 2 ≤ Fintype.card ι) (w : Cap) :
    (P.face W V i hn).pT w = P.resp (update W i w) V := by
  funext x
  simp only [FaceSetting.pT, face, resp, score]
  congr 1
  rw [Finset.sup'_congr Finset.univ_nonempty (Finset.insert_erase (Finset.mem_univ i)).symm
    (fun _ _ => rfl), Finset.sup'_insert, update_self]
  congr 1
  exact Finset.sup'_congr _ rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]

lemma face_cov (W : ι → Cap) (V : ι → Fine) (i : ι) (hn : 2 ≤ Fintype.card ι) (μ : ℝ)
    (hcov : ∀ x : Sph E, ((Finset.univ.filter fun c => P.thr - P.r₀ < inner ℝ x.1 (P.z c)).card : ℝ)
      ≤ μ * Fintype.card Cap) :
    ∀ x, (((P.face W V i hn).S.filter ((P.face W V i hn).reach · x)).card : ℝ) ≤ μ * Fintype.card Cap := by
  intro x
  refine le_trans ?_ (hcov x)
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _)) |>.trans
    (le_of_eq (by simp [FaceSetting.reach, face]))

/-! ### Plant-level theorems -/

/-- **Proposition 7.3 / Theorem 6.1 (3), plant level, face `i`.** For every attacker and every `V`,
the plant average over distinct caps of `P[face i recovered at precision ε]` is at most
`2μ₁Q + 2k_out/M + 2Qζ`. -/
theorem prop73_plant (hn2 : 2 ≤ Fintype.card ι) (hnM : 2 * Fintype.card ι ≤ Fintype.card Cap)
    (probe : List Bool → Sph E) (kout : ℕ) (out : List Bool → Fin kout → Sph E) (ε : ℝ)
    (hε : ε + P.r₀ ≤ 1 / 2) (μ : ℝ) (hμ : 0 ≤ μ)
    (hcov : ∀ x : Sph E, ((Finset.univ.filter fun c => P.thr - P.r₀ < inner ℝ x.1 (P.z c)).card : ℝ)
      ≤ μ * Fintype.card Cap) (Q : ℕ) (V : ι → Fine) (i : ι) :
    ∑ W ∈ injs, val (P.resp W V) probe
        (fun h => if ∃ j, ‖(out h j).1 - P.g (W i) (V i)‖ ≤ ε then 1 else 0) Q []
      ≤ (2 * μ * Q + 2 * kout / Fintype.card Cap + 2 * Q * P.ζ) * (injs : Finset (ι → Cap)).card := by
  apply plant_bound i _ _ (by omega)
  intro W hW
  simp only [injs, Finset.mem_filter] at hW
  have hcard := card_free hW.2 i
  have hM : 0 < Fintype.card Cap := by omega
  have h := (P.face W V i hn2).prop73_coarse_recovery probe kout out ε hε
    (fun w _ => P.hz w) (fun w _ w' _ hne => P.hsep w w' hne) Q (Fintype.card Cap) (Fintype.card ι)
    μ hM hnM hcard hμ (P.face_cov W V i hn2 μ hcov)
  have hpos : (0 : ℝ) < (free W i).card := by
    rw [hcard]; have : (2 * Fintype.card ι : ℝ) ≤ Fintype.card Cap := by exact_mod_cast hnM
    linarith
  rw [div_le_iff₀ (show (0:ℝ) < ((P.face W V i hn2).S.card : ℝ) from hpos)] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [P.face_pT W V i hn2 w, update_self]
  rfl

/-- **Theorem 10.1, plant level, face `i`** (`k_out = k + 1`, `r₀ ≤ 1/8`). -/
theorem thm101_plant (hn2 : 2 ≤ Fintype.card ι) (hnM : 2 * Fintype.card ι ≤ Fintype.card Cap)
    (probe : List Bool → Sph E) (k : ℕ) (out : List Bool → Fin (k + 1) → Sph E)
    (hr : P.r₀ ≤ 1 / 8) (μ : ℝ) (hμ : 0 ≤ μ)
    (hcov : ∀ x : Sph E, ((Finset.univ.filter fun c => P.thr - P.r₀ < inner ℝ x.1 (P.z c)).card : ℝ)
      ≤ μ * Fintype.card Cap) (Q : ℕ) (V : ι → Fine) (i : ι) :
    3 / 8 * (1 - (2 * μ * Q + 2 * ((k + 1 : ℕ) : ℝ) / Fintype.card Cap + 2 * Q * P.ζ)) * (injs : Finset (ι → Cap)).card ≤
    ∑ W ∈ injs, val (P.resp W V) probe (fun h =>
        Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out h j).1 - P.g (W i) (V i)‖)) Q [] := by
  -- apply `plant_bound` to the negated loss
  have := plant_bound i (fun W => - val (P.resp W V) probe (fun h =>
        Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out h j).1 - P.g (W i) (V i)‖)) Q [])
    (-(3 / 8 * (1 - (2 * μ * Q + 2 * ((k + 1 : ℕ) : ℝ) / Fintype.card Cap + 2 * Q * P.ζ))))
    (by omega) (by
      intro W hW
      simp only [injs, Finset.mem_filter] at hW
      have hcard := card_free hW.2 i
      have hM : 0 < Fintype.card Cap := by omega
      have h := (P.face W V i hn2).thm101_plateau probe k out hr
        (fun w _ => P.hz w) (fun w _ w' _ hne => P.hsep w w' hne) Q (Fintype.card Cap)
        (Fintype.card ι) μ hM hnM hcard hμ (P.face_cov W V i hn2 μ hcov)
      have hpos : (0 : ℝ) < (free W i).card := by
        rw [hcard]; have : (2 * Fintype.card ι : ℝ) ≤ Fintype.card Cap := by exact_mod_cast hnM
        linarith
      rw [le_div_iff₀ (show (0:ℝ) < ((P.face W V i hn2).S.card : ℝ) from hpos)] at h
      have e : ∑ w ∈ free W i, val (P.resp (update W i w) V) probe (fun h =>
            Finset.univ.inf' Finset.univ_nonempty
              (fun j => ‖(out h j).1 - P.g (update W i w i) (V i)‖)) Q [] =
          ∑ w ∈ (P.face W V i hn2).S, val ((P.face W V i hn2).pT w) probe (fun h =>
            Finset.univ.inf' Finset.univ_nonempty
              (fun j => ‖(out h j).1 - (P.face W V i hn2).g w‖)) Q [] := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [P.face_pT W V i hn2 w]; simp [face]
      simp only [Finset.sum_neg_distrib, e]
      simp only [face] at h ⊢
      linarith)
  simp only [Finset.sum_neg_distrib] at this
  linarith

/-- **Corollary 8.1, first branch (plateau), plant level.** Averaged over the whole plant (distinct
caps and fine indices), for every attacker, the average nearest-output distance
`E[(1/n) Σᵢ minⱼ ‖ĝⱼ − g⁽ⁱ⁾‖] ≥ 3/8 · (1 − 2μ₁Q − 2k_out/M − 2Qζ)`. -/
theorem cor81_branch1_plant (hn2 : 2 ≤ Fintype.card ι) (hnM : 2 * Fintype.card ι ≤ Fintype.card Cap)
    (probe : List Bool → Sph E) (k : ℕ) (out : List Bool → Fin (k + 1) → Sph E)
    (hr : P.r₀ ≤ 1 / 8) (μ : ℝ) (hμ : 0 ≤ μ)
    (hcov : ∀ x : Sph E, ((Finset.univ.filter fun c => P.thr - P.r₀ < inner ℝ x.1 (P.z c)).card : ℝ)
      ≤ μ * Fintype.card Cap) (Q : ℕ) :
    3 / 8 * (1 - (2 * μ * Q + 2 * ((k + 1 : ℕ) : ℝ) / Fintype.card Cap + 2 * Q * P.ζ)) *
        ((injs : Finset (ι → Cap)).card * Fintype.card (ι → Fine)) ≤
    ∑ V : ι → Fine, ∑ W ∈ injs, val (P.resp W V) probe (fun h =>
        (1 / Fintype.card ι : ℝ) * ∑ i, Finset.univ.inf' Finset.univ_nonempty
          (fun j => ‖(out h j).1 - P.g (W i) (V i)‖)) Q [] := by
  set c := 3 / 8 * (1 - (2 * μ * Q + 2 * ((k + 1 : ℕ) : ℝ) / Fintype.card Cap + 2 * Q * P.ζ))
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α := ι))
  have e : ∀ (V : ι → Fine) (W : ι → Cap), val (P.resp W V) probe (fun h =>
        (1 / Fintype.card ι : ℝ) * ∑ i, Finset.univ.inf' Finset.univ_nonempty
          (fun j => ‖(out h j).1 - P.g (W i) (V i)‖)) Q [] =
      (1 / Fintype.card ι : ℝ) * ∑ i, val (P.resp W V) probe (fun h =>
        Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out h j).1 - P.g (W i) (V i)‖)) Q [] := by
    intro V W
    have := val_affine (P.resp W V) probe 0 (1 / Fintype.card ι) (fun h => ∑ i,
      Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out h j).1 - P.g (W i) (V i)‖)) Q []
    simp only [zero_add] at this
    rw [this, val_sum]
  simp only [e, ← Finset.mul_sum]
  have hi : ∀ V : ι → Fine, ∀ i, c * (injs : Finset (ι → Cap)).card ≤
      ∑ W ∈ injs, val (P.resp W V) probe (fun h =>
        Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out h j).1 - P.g (W i) (V i)‖)) Q [] :=
    fun V i => P.thm101_plant hn2 hnM probe k out hr μ hμ hcov Q V i
  have hsum : (Fintype.card (ι → Fine) : ℝ) * (Fintype.card ι * (c * (injs : Finset (ι → Cap)).card)) ≤
      ∑ V : ι → Fine, ∑ W ∈ injs, ∑ i, val (P.resp W V) probe (fun h =>
        Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out h j).1 - P.g (W i) (V i)‖)) Q [] := by
    calc _ = ∑ _V : ι → Fine, ∑ _i : ι, c * (injs : Finset (ι → Cap)).card := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ V : ι → Fine, ∑ i : ι, ∑ W ∈ injs, val (P.resp W V) probe (fun h =>
            Finset.univ.inf' Finset.univ_nonempty (fun j => ‖(out h j).1 - P.g (W i) (V i)‖)) Q [] :=
          Finset.sum_le_sum fun V _ => Finset.sum_le_sum fun i _ => hi V i
      _ = _ := Finset.sum_congr rfl fun V _ => Finset.sum_comm
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hn]
  have e2 : c * ((injs : Finset (ι → Cap)).card * Fintype.card (ι → Fine)) * Fintype.card ι =
      (Fintype.card (ι → Fine) : ℝ) * (Fintype.card ι * (c * (injs : Finset (ι → Cap)).card)) := by ring
  linarith

/-- The reach of cap `c` (`⟨x, z_c⟩ > t₀`). -/
def reach (c : Cap) (x : Sph E) : Prop := P.thr - P.r₀ < inner ℝ x.1 (P.z c)

/-- **Corollary 4.2, plant level, face `i`**: `P[T⁽ⁱ⁾ ≤ K] ≤ 2μ₁K + 2Kζ`, averaged over caps. -/
theorem cor42_plant (hn2 : 2 ≤ Fintype.card ι) (hnM : 2 * Fintype.card ι ≤ Fintype.card Cap)
    (probe : List Bool → Sph E) (μ : ℝ) (hμ : 0 ≤ μ)
    (hcov : ∀ x : Sph E, ((Finset.univ.filter fun c => P.thr - P.r₀ < inner ℝ x.1 (P.z c)).card : ℝ)
      ≤ μ * Fintype.card Cap) (K : ℕ) (V : ι → Fine) (i : ι) :
    ∑ W ∈ injs, val (P.resp W V) probe (hitInd P.reach probe (W i)) K []
      ≤ (2 * μ * K + 2 * K * P.ζ) * (injs : Finset (ι → Cap)).card := by
  apply plant_bound i _ _ (by omega)
  intro W hW
  simp only [injs, Finset.mem_filter] at hW
  have hcard := card_free hW.2 i
  have hM : 0 < Fintype.card Cap := by omega
  have h := (P.face W V i hn2).cor42_hitting probe K (Fintype.card Cap) (Fintype.card ι) μ hM hnM
    hcard hμ (P.face_cov W V i hn2 μ hcov)
  have hpos : (0 : ℝ) < (free W i).card := by
    rw [hcard]; have : (2 * Fintype.card ι : ℝ) ≤ Fintype.card Cap := by exact_mod_cast hnM
    linarith
  rw [div_le_iff₀ (show (0:ℝ) < ((P.face W V i hn2).S.card : ℝ) from hpos)] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [P.face_pT W V i hn2 w, update_self]
  rfl

/-- **Corollary 4.4 (staircase), plant level.** The expected number of probes that land in some
face's reach satisfies `E[C_Q] ≤ S_n(Q) = Σ_{k=1}^{Q} min{1, n(2μ₁ + 2ζ)k}`. -/
theorem staircase_plant (hn2 : 2 ≤ Fintype.card ι) (hnM : 2 * Fintype.card ι ≤ Fintype.card Cap)
    (probe : List Bool → Sph E) (μ : ℝ) (hμ : 0 ≤ μ)
    (hcov : ∀ x : Sph E, ((Finset.univ.filter fun c => P.thr - P.r₀ < inner ℝ x.1 (P.z c)).card : ℝ)
      ≤ μ * Fintype.card Cap) (Q : ℕ) (V : ι → Fine) :
    ∑ W ∈ injs, val (P.resp W V) probe (fun h => ∑ k ∈ Finset.range Q,
        if ∃ i, P.reach (W i) (probe (h.take k)) then 1 else 0) Q []
      ≤ (injs : Finset (ι → Cap)).card * ∑ k ∈ Finset.range Q,
          min 1 (Fintype.card ι * (2 * μ * (k + 1) + 2 * (k + 1) * P.ζ)) := by
  simp only [val_sum]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  set G : (ι → Cap) → List Bool → ℝ := fun W h' =>
    if ∃ i, P.reach (W i) (probe (h'.take k)) then 1 else 0 with hG
  -- horizon reduction to k + 1 rounds
  have hred : ∀ W, val (P.resp W V) probe (fun h =>
      if ∃ i, P.reach (W i) (probe (h.take k)) then (1 : ℝ) else 0) Q [] =
      val (P.resp W V) probe (G W) (k + 1) [] := by
    intro W
    have := val_of_prefix (P.resp W V) probe (G W) (k + 1) (Q - (k + 1))
    rw [show k + 1 + (Q - (k + 1)) = Q by omega] at this
    rw [← this]
    congr 1; funext h; simp only [hG, List.take_take, min_eq_left (Nat.le_succ k)]
  simp only [hred]
  have hresp : ∀ W x, 0 ≤ P.resp W V x ∧ P.resp W V x ≤ 1 := fun W x => P.hκ _
  have h1 : ∀ W, val (P.resp W V) probe (G W) (k + 1) [] ≤ 1 := by
    intro W
    have := val_mono probe (hresp W) (G := fun _ => (1 : ℝ)) (k + 1) [] (fun h' _ => by
      show G W h' ≤ 1
      rw [hG]; dsimp only; split_ifs <;> norm_num)
    rwa [val_const] at this
  have h2 : ∀ W, val (P.resp W V) probe (G W) (k + 1) [] ≤
      ∑ i, val (P.resp W V) probe (hitInd P.reach probe (W i)) (k + 1) [] := by
    intro W
    rw [← val_sum]
    apply val_mono probe (hresp W)
    intro h' hl
    simp only [List.length_nil, zero_add] at hl
    simp only [hG]
    split_ifs with hc
    · obtain ⟨i, hi⟩ := hc
      have : hitInd P.reach probe (W i) h' = 1 := by
        unfold hitInd; rw [if_pos ⟨k, by omega, hi⟩]
      calc (1 : ℝ) = hitInd P.reach probe (W i) h' := this.symm
        _ ≤ ∑ i, hitInd P.reach probe (W i) h' :=
          Finset.single_le_sum (f := fun i => hitInd P.reach probe (W i) h')
            (fun i _ => by unfold hitInd; split_ifs <;> norm_num) (Finset.mem_univ i)
    · exact Finset.sum_nonneg fun i _ => by unfold hitInd; split_ifs <;> norm_num
  have hsumi : ∑ W ∈ (injs : Finset (ι → Cap)),
      ∑ i, val (P.resp W V) probe (hitInd P.reach probe (W i)) (k + 1) [] ≤
      (injs : Finset (ι → Cap)).card * (Fintype.card ι * (2 * μ * (k + 1) + 2 * (k + 1) * P.ζ)) := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _i : ι, (2 * μ * ((k + 1 : ℕ) : ℝ) + 2 * ((k + 1 : ℕ) : ℝ) * P.ζ) *
          (injs : Finset (ι → Cap)).card :=
          Finset.sum_le_sum fun i _ => P.cor42_plant hn2 hnM probe μ hμ hcov (k + 1) V i
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; push_cast; ring
  rcases le_total 1 (Fintype.card ι * (2 * μ * (k + 1) + 2 * (k + 1) * P.ζ)) with hm | hm
  · rw [min_eq_left hm, mul_one]
    calc _ ≤ ∑ _W ∈ (injs : Finset (ι → Cap)), (1 : ℝ) := Finset.sum_le_sum fun W _ => h1 W
      _ = _ := by simp
  · rw [min_eq_right hm]
    exact (Finset.sum_le_sum fun W _ => h2 W).trans hsumi

end PlantData

end OracleBounds.V6
