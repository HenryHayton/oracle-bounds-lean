import OracleBounds.GeneralPrior.Gallery

/-!
# Gallery-level coupling bounds (`n-face-general-prior-v2` Cor 4.2, Prop 7.3, Thm 7.1)

`GeneralPrior.Face` proves the coupling-side bounds for one face with the *other* faces frozen
(an arbitrary environment `m`). Here they are lifted to the full random gallery `V ∼ ∏ᵢ πᵢ`.

The lift is one averaging lemma, `gallery_avg`: split `V` into face `i`'s value `l` and the rest
`γ'` (`Equiv.funSplitAt`), factor the prior as `πᵢ(l) · W(γ')`, identify the gallery response at
`V` with the per-face response `(G.face i ·).pT l` (via `Gallery.score_eq_max`), and average the
per-environment bound over `γ'` with weights `W` summing to `1`. Because the per-face bound does
not depend on the environment, the average is the same bound — no combinatorial correction, unlike
`OracleBounds.V6.Plant.sum_injs_update`.

No `sorry`s.
-/

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] [DecidableEq Fine]

namespace Gallery

variable (G : Gallery E ι Fine)

/-- The product prior splits off face `i`: `∏ⱼ πⱼ(Vⱼ) = πᵢ(l) · ∏_{j ≠ i} πⱼ(γ' j)`. -/
lemma prod_split (i : ι) (l : Fine) (γ' : {j : ι // j ≠ i} → Fine) :
    ∏ j, G.π j ((Equiv.funSplitAt i Fine).symm (l, γ') j) =
      G.π i l * ∏ j : {x : ι // x ≠ i}, G.π j.1 (γ' j) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp [Equiv.funSplitAt_symm_apply]
  · have hsub : ∏ j ∈ Finset.univ.erase i, G.π j ((Equiv.funSplitAt i Fine).symm (l, γ') j) =
        ∏ j : {x : ι // x ≠ i}, G.π j.1 ((Equiv.funSplitAt i Fine).symm (l, γ') j.1) :=
      Finset.prod_subtype (Finset.univ.erase i) (fun x => by simp) _
    rw [hsub]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [Equiv.funSplitAt_symm_apply, j.2]

/-- Reassembling `(l, γ')` is updating any base gallery with the same other faces. -/
lemma symm_eq_update (i : ι) (l l₀ : Fine) (γ' : {j : ι // j ≠ i} → Fine) :
    (Equiv.funSplitAt i Fine).symm (l, γ') =
      Function.update ((Equiv.funSplitAt i Fine).symm (l₀, γ')) i l := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [Equiv.funSplitAt_symm_apply]
  · simp [Equiv.funSplitAt_symm_apply, hj]

/-- The gallery response at `V = (l, γ')` is the per-face response of `G.face i` at value `l`. -/
lemma resp_eq_pT [Nonempty ι] (i : ι) (l l₀ : Fine) (γ' : {j : ι // j ≠ i} → Fine)
    (x : Sph E) :
    G.resp ((Equiv.funSplitAt i Fine).symm (l, γ')) x =
      (G.face i ((Equiv.funSplitAt i Fine).symm (l₀, γ'))).pT l x := by
  rw [Gallery.symm_eq_update i l l₀ γ']
  show G.κ (G.score _ x) = G.κ (max (inner ℝ x.1 (G.g l)) (G.env i _ x.1))
  rw [G.score_eq_max]

/-- **Gallery averaging.** If for every environment the per-face average
`Σₗ πᵢ(l)·val(pT l)(F l)` is at most `c`, then so is the full-gallery expectation
`Σ_V ∏ⱼπⱼ(Vⱼ) · val(resp V)(F (V i))`. -/
theorem gallery_avg [Nonempty ι] [Nonempty Fine] (i : ι) (probe : List Bool → Sph E) (Q : ℕ)
    (F : Fine → List Bool → ℝ) (c : ℝ)
    (hface : ∀ γ : ι → Fine, ∑ l, G.π i l * val ((G.face i γ).pT l) probe (F l) Q [] ≤ c) :
    ∑ v : ι → Fine, (∏ j, G.π j (v j)) * val (G.resp v) probe (F (v i)) Q [] ≤ c := by
  obtain ⟨l₀⟩ := (inferInstance : Nonempty Fine)
  set e := Equiv.funSplitAt i Fine with he
  set W : ({j : ι // j ≠ i} → Fine) → ℝ := fun γ' => ∏ j : {x : ι // x ≠ i}, G.π j.1 (γ' j)
    with hW
  have hW0 : ∀ γ', 0 ≤ W γ' := fun γ' => Finset.prod_nonneg fun j _ => G.hπ0 j.1 _
  have hW1 : ∑ γ', W γ' = 1 := by
    simp only [hW]
    rw [← Fintype.prod_sum (fun (j : {x : ι // x ≠ i}) x => G.π j.1 x)]
    exact Finset.prod_eq_one fun j _ => G.hπ1 j.1
  -- reindex by `(l, γ')`
  have hre : ∑ v : ι → Fine, (∏ j, G.π j (v j)) * val (G.resp v) probe (F (v i)) Q [] =
      ∑ γ', W γ' * ∑ l, G.π i l *
        val ((G.face i (e.symm (l₀, γ'))).pT l) probe (F l) Q [] := by
    rw [Fintype.sum_equiv e _ (fun p => (∏ j, G.π j (e.symm p j)) *
        val (G.resp (e.symm p)) probe (F (e.symm p i)) Q [])
      (fun v => by simp)]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hi : e.symm (l, γ') i = l := by simp [he, Equiv.funSplitAt_symm_apply]
    have hresp : G.resp (e.symm (l, γ')) = (G.face i (e.symm (l₀, γ'))).pT l :=
      funext fun x => G.resp_eq_pT i l l₀ γ' x
    rw [hi, hresp, G.prod_split i l γ']
    simp only [hW]; ring
  rw [hre]
  calc ∑ γ', W γ' * ∑ l, G.π i l * val ((G.face i (e.symm (l₀, γ'))).pT l) probe (F l) Q []
      ≤ ∑ γ', W γ' * c :=
        Finset.sum_le_sum fun γ' _ => mul_le_mul_of_nonneg_left (hface _) (hW0 γ')
    _ = c := by rw [← Finset.sum_mul, hW1, one_mul]

/-- `x` reaches template value `l` (gallery form, environment-free). -/
def reachG (l : Fine) (x : Sph E) : Prop := G.thr < inner ℝ x.1 (G.g l)

/-- `y` is accepted by template value `l` (gallery form). -/
def acceptsG (l : Fine) (y : Sph E) : Prop := G.τacc ≤ inner ℝ y.1 (G.g l)

open Classical in
/-- **Corollary 4.2 (hitting), full gallery — G1.** `P[T(i) ≤ K] ≤ K(μ₁ + 2ζ)`. -/
theorem gallery_hitting [Nonempty ι] [Nonempty Fine] (i : ι) (probe : List Bool → Sph E)
    (K : ℕ) (μ₁ : ℝ) (hμ : 0 ≤ μ₁)
    (hcov : ∀ x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁) :
    ∑ v : ι → Fine, (∏ j, G.π j (v j)) * val (G.resp v) probe (hitInd G.reachG probe (v i)) K []
      ≤ K * (μ₁ + 2 * G.ζ) :=
  G.gallery_avg i probe K (fun l => hitInd G.reachG probe l) _
    (fun γ => (G.face i γ).hitting_bound probe K μ₁ hμ hcov)

open Classical in
/-- **Proposition 7.3 (recovery of a specified entry), full gallery — G4.** With `p(ε)` the
largest prior mass of an `ε`-ball, `P[face i recovered at ε] ≤ Q(μ₁ + 2ζ) + k_out · p(ε)`. This is
the bound that answers "how many queries to reconstruct a *nominated* list entry": it forces
`Q ≳ 1/(2μ₁)`. -/
theorem gallery_recovery [Nonempty ι] [Nonempty Fine] (i : ι) (probe : List Bool → Sph E)
    (kout : ℕ) (out : List Bool → Fin kout → Sph E) (Q : ℕ) (μ₁ ε pε : ℝ) (hμ : 0 ≤ μ₁)
    (hp : 0 ≤ pε)
    (hcov : ∀ x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (hballcov : ∀ y : Sph E,
      (∑ l ∈ Finset.univ.filter (fun l => ‖y.1 - G.g l‖ ≤ ε), G.π i l) ≤ pε) :
    ∑ v : ι → Fine, (∏ j, G.π j (v j)) * val (G.resp v) probe
      (fun h => if ∃ j, ‖(out h j).1 - G.g (v i)‖ ≤ ε then (1 : ℝ) else 0) Q []
      ≤ Q * (μ₁ + 2 * G.ζ) + kout * pε :=
  G.gallery_avg i probe Q (fun l h => if ∃ j, ‖(out h j).1 - G.g l‖ ≤ ε then (1 : ℝ) else 0) _
    (fun γ => (G.face i γ).coarse_recovery_bound probe kout out Q μ₁ ε pε hμ hp hcov hballcov)

open Classical in
/-- **Theorem 7.1 (impersonation of a specified entry), full gallery — G5.**
`P[entry i accepts some probe or output] ≤ Q(μ₁ + 2ζ) + k_out · μ_acc`. -/
theorem gallery_impersonation [Nonempty ι] [Nonempty Fine] (i : ι) (probe : List Bool → Sph E)
    (kout : ℕ) (out : List Bool → Fin kout → Sph E) (Q : ℕ) (μ₁ μacc : ℝ) (hμ : 0 ≤ μ₁)
    (hacc : 0 ≤ μacc)
    (hcov : ∀ x, (∑ l ∈ Finset.univ.filter (G.reachG · x), G.π i l) ≤ μ₁)
    (haccov : ∀ y, (∑ l ∈ Finset.univ.filter (G.acceptsG · y), G.π i l) ≤ μacc) :
    ∑ v : ι → Fine, (∏ j, G.π j (v j)) * val (G.resp v) probe (fun h =>
        if (∃ k < h.length, G.acceptsG (v i) (probe (h.take k))) ∨
          (∃ j, G.acceptsG (v i) (out h j)) then (1 : ℝ) else 0) Q []
      ≤ Q * (μ₁ + 2 * G.ζ) + kout * μacc :=
  G.gallery_avg i probe Q (fun l h =>
      if (∃ k < h.length, G.acceptsG l (probe (h.take k))) ∨ (∃ j, G.acceptsG l (out h j))
        then (1 : ℝ) else 0) _
    (fun γ => (G.face i γ).impersonation_bound probe kout out Q μ₁ μacc hμ hacc hcov haccov)

end Gallery

end OracleBounds.GeneralPrior
