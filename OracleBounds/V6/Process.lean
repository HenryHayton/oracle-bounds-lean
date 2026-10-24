import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The adaptive one-bit process and the ghost coupling (v6 §4)

**Model.** Fix the attacker's internal randomness `U = u` (a randomised attacker is a mixture of
deterministic ones; every bound below is uniform in `u`, so it survives averaging over `u`).
The attacker is then a map `probe : List Bool → X` sending the transcript so far to the next probe.
The oracle answers probe `x` with bit `true` with probability `p x ∈ [0,1]`, independently across
rounds given the past. For a function `F` of the full transcript, `val p probe F r h` is the
expectation of `F` over the next `r` rounds started from history `h`; so `val p probe F Q []` is
`E[F(b₁,…,b_Q)]`. This is the textbook definition of the law of an adaptive protocol with binary
responses, written as a recursion instead of a product measure.

**Ghost coupling.** For face `i` of the gallery, `pT` is the response probability with face `i`
present and `pG` with it deleted. `R` is the reach region of face `i`'s cap. v6's `ζ`-band-null
hypothesis gives *locality*: off `R`, `|pT − pG| ≤ 2ζ` (proved from the kernel in
`OracleBounds.V6.Geometry`). `hitBy R probe h` is the event `T⁽ⁱ⁾ ≤ |h|`.

Everything in this file is proved; there are no `sorry`s.
-/

namespace OracleBounds.V6

open Finset

variable {X : Type*}

/-- Expectation of `F` over the next `r` rounds of the adaptive process, started at history `h`. -/
noncomputable def val (p : X → ℝ) (probe : List Bool → X) (F : List Bool → ℝ) :
    ℕ → List Bool → ℝ
  | 0, h => F h
  | r + 1, h => p (probe h) * val p probe F r (h ++ [true]) +
      (1 - p (probe h)) * val p probe F r (h ++ [false])

/-- Some probe issued along history `h` lies in `R` (i.e. the hitting time is `≤ |h|`). -/
def hitBy (R : X → Prop) (probe : List Bool → X) (h : List Bool) : Prop :=
  ∃ k < h.length, R (probe (h.take k))

section basic

variable (p : X → ℝ) (probe : List Bool → X)

@[simp] lemma val_zero (F : List Bool → ℝ) (h : List Bool) : val p probe F 0 h = F h := rfl

lemma val_succ (F : List Bool → ℝ) (r : ℕ) (h : List Bool) :
    val p probe F (r + 1) h = p (probe h) * val p probe F r (h ++ [true]) +
      (1 - p (probe h)) * val p probe F r (h ++ [false]) := rfl

/-- `val` is affine in the leaf function. -/
lemma val_affine (a b : ℝ) (F : List Bool → ℝ) :
    ∀ r h, val p probe (fun h' => a + b * F h') r h = a + b * val p probe F r h := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih => intro h; simp only [val_succ, ih]; ring

lemma val_const (c : ℝ) : ∀ r h, val p probe (fun _ => c) r h = c := by
  intro r h
  simpa using val_affine p probe c 0 (fun _ => 0) r h

lemma val_add (F G : List Bool → ℝ) :
    ∀ r h, val p probe (fun h' => F h' + G h') r h = val p probe F r h + val p probe G r h := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih => intro h; simp only [val_succ, ih]; ring

lemma val_sum {ι : Type*} (s : Finset ι) (F : ι → List Bool → ℝ) :
    ∀ r h, val p probe (fun h' => ∑ i ∈ s, F i h') r h = ∑ i ∈ s, val p probe (F i) r h := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
    intro h
    simp only [val_succ, ih, Finset.mul_sum, ← Finset.sum_add_distrib]

variable {p}

/-- Monotonicity; only leaves reachable from `h` in `r` rounds matter. -/
lemma val_mono (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) {F G : List Bool → ℝ} :
    ∀ r h, (∀ h', h'.length = h.length + r → F h' ≤ G h') →
      val p probe F r h ≤ val p probe G r h := by
  intro r
  induction r with
  | zero => intro h hFG; exact hFG h (by simp)
  | succ r ih =>
    intro h hFG
    have h1 := ih (h ++ [true]) (fun h' hl => hFG h' (by simp at hl; omega))
    have h2 := ih (h ++ [false]) (fun h' hl => hFG h' (by simp at hl; omega))
    simp only [val_succ]
    have hp0 := (hp (probe h)).1
    have hp1 : 0 ≤ 1 - p (probe h) := by linarith [(hp (probe h)).2]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hp0) (mul_le_mul_of_nonneg_left h2 hp1)

lemma val_mem_Icc (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) {F : List Bool → ℝ}
    (hF : ∀ h', 0 ≤ F h' ∧ F h' ≤ 1) (r : ℕ) (h : List Bool) :
    0 ≤ val p probe F r h ∧ val p probe F r h ≤ 1 := by
  constructor
  · simpa [val_const] using val_mono probe hp (F := fun _ => 0) r h (fun h' _ => (hF h').1)
  · simpa [val_const] using val_mono probe hp (G := fun _ => 1) r h (fun h' _ => (hF h').2)

/-- If `F` vanishes on every leaf extending `h`, the expectation from `h` is zero. -/
lemma val_eq_zero_of_vanish (F : List Bool → ℝ) :
    ∀ r h, (∀ h', h <+: h' → h'.length = h.length + r → F h' = 0) → val p probe F r h = 0 := by
  intro r
  induction r with
  | zero =>
    intro h hF
    exact hF h (List.prefix_refl h) (by simp)
  | succ r ih =>
    intro h hF
    have ht := ih (h ++ [true]) (fun h' hpre hl =>
      hF h' ((List.prefix_append h [true]).trans hpre) (by simp at hl; omega))
    have hf := ih (h ++ [false]) (fun h' hpre hl =>
      hF h' ((List.prefix_append h [false]).trans hpre) (by simp at hl; omega))
    simp [val_succ, ht, hf]

end basic

/-- `val` congruence for leaf functions agreeing on extensions of `h` (prefix form). -/
lemma val_congr_prefix' (p : X → ℝ) (probe : List Bool → X) {F G : List Bool → ℝ} :
    ∀ r h, (∀ h', h <+: h' → h'.length = h.length + r → F h' = G h') →
      val p probe F r h = val p probe G r h := by
  intro r
  induction r with
  | zero => intro h hFG; exact hFG h (List.prefix_refl h) (by simp)
  | succ r ih =>
    intro h hFG
    simp only [val_succ]
    rw [ih (h ++ [true]) (fun h' hpre hl =>
        hFG h' ((List.prefix_append h [true]).trans hpre) (by simp at hl; omega)),
      ih (h ++ [false]) (fun h' hpre hl =>
        hFG h' ((List.prefix_append h [false]).trans hpre) (by simp at hl; omega))]

/-- `val` congruence on leaves (length form). -/
lemma val_mono_eq {p : X → ℝ} {probe : List Bool → X} {F G : List Bool → ℝ} {r : ℕ} {h : List Bool}
    (hFG : ∀ h', h'.length = h.length + r → F h' = G h') : val p probe F r h = val p probe G r h :=
  val_congr_prefix' p probe r h (fun h' _ hl => hFG h' hl)

/-- Tower property: `r + s` rounds = `r` rounds of the `s`-round expectation. -/
theorem val_add_rounds (p : X → ℝ) (probe : List Bool → X) (F : List Bool → ℝ) :
    ∀ r s h, val p probe F (r + s) h = val p probe (fun h' => val p probe F s h') r h := by
  intro r
  induction r with
  | zero => intro s h; simp
  | succ r ih =>
    intro s h
    rw [show r + 1 + s = (r + s) + 1 by omega, val_succ, val_succ, ih, ih]

/-- A leaf function that depends only on the first `k` bits has the same expectation over any
horizon `k + s` as over `k`. -/
theorem val_of_prefix (p : X → ℝ) (probe : List Bool → X) (G : List Bool → ℝ) (k s : ℕ) :
    val p probe (fun h => G (h.take k)) (k + s) [] = val p probe G k [] := by
  rw [val_add_rounds]
  apply val_mono_eq
  intro h' hl
  simp only [List.length_nil, zero_add] at hl
  have hc := val_const p probe (G h') s h'
  rw [← hc]
  -- leaves below `h'` have first `k` bits equal to `h'`
  exact val_congr_prefix' p probe s h' (fun h hpre _ => by
    rw [← hl, ← List.prefix_iff_eq_take.mp hpre])

/-- **Lemma 4.1 (ghost coupling), transfer form.** For a leaf function `F ∈ [0,1]` that vanishes
on every transcript in which the target reach `R` has been hit, the true and ghost expectations
differ by at most `2rζ` after `r` rounds. For `ζ = 0` they coincide. -/
theorem val_coupling (probe : List Bool → X) (pT pG : X → ℝ) (R : X → Prop) (ζ : ℝ)
    (hpT : ∀ x, 0 ≤ pT x ∧ pT x ≤ 1) (hpG : ∀ x, 0 ≤ pG x ∧ pG x ≤ 1) (hζ : 0 ≤ ζ)
    (hloc : ∀ x, ¬ R x → |pT x - pG x| ≤ 2 * ζ)
    (F : List Bool → ℝ) (hF : ∀ h', 0 ≤ F h' ∧ F h' ≤ 1)
    (hFhit : ∀ h', hitBy R probe h' → F h' = 0) :
    ∀ (r : ℕ) h, |val pT probe F r h - val pG probe F r h| ≤ 2 * r * ζ := by
  intro r
  induction r with
  | zero => intro h; simp
  | succ r ih =>
    intro h
    by_cases hR : R (probe h)
    · -- every leaf below `h` has already hit `R`
      have hvan : ∀ h', h <+: h' → h'.length = h.length + (r + 1) → F h' = 0 := by
        intro h' hpre hl
        apply hFhit
        refine ⟨h.length, by omega, ?_⟩
        rwa [← List.prefix_iff_eq_take.mp hpre]
      rw [val_eq_zero_of_vanish probe F (r + 1) h hvan,
        val_eq_zero_of_vanish probe F (r + 1) h hvan]
      simp only [sub_self, abs_zero]
      positivity
    · set aT := val pT probe F r (h ++ [true])
      set bT := val pT probe F r (h ++ [false])
      set aG := val pG probe F r (h ++ [true])
      set bG := val pG probe F r (h ++ [false])
      set t := pT (probe h)
      set g := pG (probe h)
      have e : val pT probe F (r + 1) h - val pG probe F (r + 1) h =
          t * (aT - aG) + (1 - t) * (bT - bG) + (t - g) * (aG - bG) := by
        simp only [val_succ, aT, bT, aG, bG, t, g]; ring
      rw [e]
      have ht0 : 0 ≤ t := (hpT _).1
      have ht1 : 0 ≤ 1 - t := by linarith [(hpT (probe h)).2]
      have haG := val_mem_Icc probe hpG hF r (h ++ [true])
      have hbG := val_mem_Icc probe hpG hF r (h ++ [false])
      have hab : |aG - bG| ≤ 1 := abs_le.2 ⟨by linarith [haG.1, hbG.2], by linarith [haG.2, hbG.1]⟩
      have t1 : |t * (aT - aG)| ≤ t * (2 * r * ζ) := by
        rw [abs_mul, abs_of_nonneg ht0]; exact mul_le_mul_of_nonneg_left (ih _) ht0
      have t2 : |(1 - t) * (bT - bG)| ≤ (1 - t) * (2 * r * ζ) := by
        rw [abs_mul, abs_of_nonneg ht1]; exact mul_le_mul_of_nonneg_left (ih _) ht1
      have t3 : |(t - g) * (aG - bG)| ≤ 2 * ζ * 1 := by
        rw [abs_mul]; exact mul_le_mul (hloc _ hR) hab (abs_nonneg _) (by linarith)
      calc |t * (aT - aG) + (1 - t) * (bT - bG) + (t - g) * (aG - bG)|
          ≤ |t * (aT - aG)| + |(1 - t) * (bT - bG)| + |(t - g) * (aG - bG)| :=
            (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans_eq (by ring)
        _ ≤ t * (2 * r * ζ) + (1 - t) * (2 * r * ζ) + 2 * ζ * 1 := by linarith
        _ = 2 * ((r + 1 : ℕ) : ℝ) * ζ := by push_cast; ring

/-- Pathwise coverage count: if every point lies in the reach of at most `c` caps of `S`, then
along any list of points indexed by `pts`, at most `|pts|·c` caps of `S` are reached. -/
lemma card_reached_le {Cap ι : Type*} (S : Finset Cap) (reach : Cap → X → Prop)
    [∀ w x, Decidable (reach w x)] (c : ℝ) (hcov : ∀ x, ((S.filter (reach · x)).card : ℝ) ≤ c)
    (pts : Finset ι) (y : ι → X) [∀ w, Decidable (∃ i ∈ pts, reach w (y i))] :
    ∑ w ∈ S, (if ∃ i ∈ pts, reach w (y i) then (1 : ℝ) else 0) ≤ pts.card * c := by
  calc ∑ w ∈ S, (if ∃ i ∈ pts, reach w (y i) then (1 : ℝ) else 0)
      ≤ ∑ w ∈ S, ∑ i ∈ pts, (if reach w (y i) then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro w _
        split_ifs with hw
        · obtain ⟨i, hi, hr⟩ := hw
          calc (1 : ℝ) = if reach w (y i) then 1 else 0 := by simp [hr]
            _ ≤ _ := Finset.single_le_sum (f := fun i => if reach w (y i) then (1 : ℝ) else 0)
                (fun _ _ => by split_ifs <;> norm_num) hi
        · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    _ = ∑ i ∈ pts, ∑ w ∈ S, (if reach w (y i) then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ i ∈ pts, ((S.filter (reach · (y i))).card : ℝ) := by simp
    _ ≤ ∑ _i ∈ pts, c := Finset.sum_le_sum (fun i _ => hcov (y i))
    _ = pts.card * c := by simp

open Classical in
/-- Indicator of `T⁽ⁱ⁾ ≤ |h|` for the cap `w`. -/
noncomputable def hitInd {Cap : Type*} (reach : Cap → X → Prop) (probe : List Bool → X)
    (w : Cap) (h : List Bool) : ℝ :=
  if hitBy (reach w) probe h then 1 else 0

open Classical in
/-- **Ghost union bound** — the engine behind Cor 4.2, Thm 7.1, Prop 7.3 / Thm 6.1 (3), Thm 10.1.

Setting (one face `i`, environment `Eᵢ = (U, W₋ᵢ, V⁽⁻ⁱ⁾)` fixed): the hidden cap `w` of face `i`
ranges over `S = [M] ∖ W₋ᵢ`; `pT w` is the true response probability when face `i` sits in cap `w`
(with any fine index), `pG` the ghost one (face `i` deleted, independent of `w`).
`A w` is the bad event for cap `w` (as a `[0,1]`-valued leaf function), and it is contained in
"`w` was hit, or `E w` happened", where `E w` are `[0,1]`-valued leaf events whose total over
`w ∈ S` is at most `K` on every transcript.

Conclusion: `∑_{w ∈ S} P_true(w)[A w] ≤ Q·c + K + 2Qζ·|S|`. Dividing by `|S|` gives the average
over `W_i` uniform on `S`, i.e. the plant probability conditional on the environment. -/
theorem ghost_union_bound {Cap : Type*} (S : Finset Cap) (reach : Cap → X → Prop)
    (probe : List Bool → X) (pT : Cap → X → ℝ) (pG : X → ℝ) (ζ c K : ℝ) (Q : ℕ)
    (A E : Cap → List Bool → ℝ)
    (hpT : ∀ w x, 0 ≤ pT w x ∧ pT w x ≤ 1) (hpG : ∀ x, 0 ≤ pG x ∧ pG x ≤ 1) (hζ : 0 ≤ ζ)
    (hloc : ∀ w ∈ S, ∀ x, ¬ reach w x → |pT w x - pG x| ≤ 2 * ζ)
    (hcov : ∀ x, ((S.filter (reach · x)).card : ℝ) ≤ c)
    (hE : ∀ w h, 0 ≤ E w h ∧ E w h ≤ 1)
    (hK : ∀ h : List Bool, h.length = Q → ∑ w ∈ S, E w h ≤ K)
    (hA : ∀ w ∈ S, ∀ h : List Bool, h.length = Q →
      A w h ≤ 1 - (1 - hitInd reach probe w h) * (1 - E w h)) :
    ∑ w ∈ S, val (pT w) probe (A w) Q [] ≤ Q * c + K + 2 * Q * ζ * S.card := by
  -- `N w` = "not hit and not `E w`", a `[0,1]` leaf function vanishing on hits.
  set N : Cap → List Bool → ℝ := fun w h => (1 - hitInd reach probe w h) * (1 - E w h) with hN
  have hit01 : ∀ w h, 0 ≤ hitInd reach probe w h ∧ hitInd reach probe w h ≤ 1 := by
    intro w h; unfold hitInd; split_ifs <;> norm_num
  have hN01 : ∀ w h, 0 ≤ N w h ∧ N w h ≤ 1 := by
    intro w h
    have := hit01 w h; have := hE w h
    exact ⟨mul_nonneg (by linarith) (by linarith), by nlinarith⟩
  have hNhit : ∀ w h, hitBy (reach w) probe h → N w h = 0 := by
    intro w h hh; simp [hN, hitInd, hh]
  -- per-cap bound
  have per : ∀ w ∈ S, val (pT w) probe (A w) Q [] ≤
      val pG probe (fun h => hitInd reach probe w h + E w h) Q [] + 2 * Q * ζ := by
    intro w hw
    have c1 : val (pT w) probe (A w) Q [] ≤ val (pT w) probe (fun h => 1 + (-1) * N w h) Q [] :=
      val_mono probe (hpT w) Q [] (fun h' hl => by
        have := hA w hw h' (by simpa using hl); simp only [hN] at *; linarith)
    have c2 := val_coupling probe (pT w) pG (reach w) ζ (hpT w) hpG hζ (hloc w hw) (N w)
      (hN01 w) (hNhit w) Q []
    have c3 : val pG probe (fun h => 1 + (-1) * N w h) Q [] ≤
        val pG probe (fun h => hitInd reach probe w h + E w h) Q [] :=
      val_mono probe hpG Q [] (fun h' _ => by
        have := hit01 w h'; have := hE w h'; simp only [hN]; nlinarith)
    rw [val_affine] at c1 c3
    have := (abs_le.mp c2).1
    linarith
  calc ∑ w ∈ S, val (pT w) probe (A w) Q []
      ≤ ∑ w ∈ S, (val pG probe (fun h => hitInd reach probe w h + E w h) Q [] + 2 * Q * ζ) :=
        Finset.sum_le_sum per
    _ = val pG probe (fun h => ∑ w ∈ S, (hitInd reach probe w h + E w h)) Q []
          + 2 * Q * ζ * S.card := by
        rw [Finset.sum_add_distrib, val_sum]; simp [mul_comm]
    _ ≤ val pG probe (fun _ => Q * c + K) Q [] + 2 * Q * ζ * S.card := by
        gcongr
        apply val_mono probe hpG Q []
        intro h' hl
        simp only [List.length_nil, zero_add] at hl
        rw [Finset.sum_add_distrib]
        have hc : ∑ w ∈ S, hitInd reach probe w h' ≤ (h'.length : ℝ) * c := by
          have := card_reached_le S reach c hcov (Finset.range h'.length)
            (fun k => probe (h'.take k))
          rw [Finset.card_range] at this
          refine le_trans (le_of_eq (Finset.sum_congr rfl fun w _ => ?_)) this
          unfold hitInd hitBy
          by_cases hx : ∃ k < h'.length, reach w (probe (h'.take k)) <;> simp [hx]
        have := hK h' hl
        rw [hl] at hc
        linarith
    _ = Q * c + K + 2 * Q * ζ * S.card := by rw [val_const]

/-! ### Sanity checks on the model (guard against a mis-specified `val`) -/

/-- One fair coin: `P[b₁ = 1] = 1/2`. -/
example : val (fun _ : Unit => (1 / 2 : ℝ)) (fun _ => ()) (fun h => if h = [true] then 1 else 0) 1 []
    = 1 / 2 := by
  simp [val_succ]

/-- Adaptivity: the first probe answers 1 w.p. 1/2; the second probe depends on the first bit and
answers 1 w.p. 1/4 after a `1`, w.p. 1 after a `0`. So `P[b₂ = 1] = 1/2·1/4 + 1/2·1 = 5/8`. -/
example : val (fun x : Option Bool => (match x with
      | none => (1 / 2 : ℝ) | some true => 1 / 4 | some false => 1))
    (fun h => h.head?) (fun h => if h.getLast? = some true then 1 else 0) 2 [] = 5 / 8 := by
  simp [val_succ]; norm_num

end OracleBounds.V6
