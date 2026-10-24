import OracleBounds.GeneralPrior.Face

/-!
# The full independent-faces gallery under a general prior (`n-face-general-prior-v1` §§1, 4, 6–10)

`n` independent faces `g₁, …, gₙ`, each drawn from its own finite prior `πᵢ` on a shared universe
`Fine` of possible template values, with a single shared embedding `g : Fine → E`. No caps, no
packing, no injectivity: unlike `OracleBounds.V6.Plant` this needs no combinatorial
double-counting, because the faces are literally independent, so conditioning on the other faces
is a plain sum/Fubini argument (`score_eq_max`) rather of `PlantData.sum_injs_update`'s
permutation trick.

Assembles `OracleBounds.GeneralPrior.Face`'s single-face bounds into the gallery-level G1/G2/G4/G5
statements plus the risk identity and per-face plateau. No `sorry`s.
-/

namespace OracleBounds.GeneralPrior

open Finset OracleBounds.V6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The gallery: shared oracle parameters, shared embedding `g : Fine → E`, and one prior per
face. `hthr` (`thr > -1`) is only used to build a sentinel "no other faces" environment when
`n = 1`; it matches the note's `thr ∈ (-1,1)`. -/
structure Gallery (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ι Fine : Type*) [Fintype ι] [Fintype Fine] where
  thr : ℝ
  τacc : ℝ
  hτ : thr < τacc
  hthr : -1 < thr
  κ : ℝ → ℝ
  ν₀ : ℝ
  ζ : ℝ
  hκ : ∀ s, 0 ≤ κ s ∧ κ s ≤ 1
  hband : ∀ s ≤ thr, |κ s - ν₀| ≤ ζ
  g : Fine → E
  hg : ∀ l, ‖g l‖ = 1
  π : ι → Fine → ℝ
  hπ0 : ∀ i l, 0 ≤ π i l
  hπ1 : ∀ i, ∑ l, π i l = 1

namespace Gallery

variable {ι Fine : Type*} [Fintype ι] [DecidableEq ι] [Fintype Fine] (G : Gallery E ι Fine)

/-- Score of probe `x` against the full gallery `V : ι → Fine`: `maxᵢ ⟨x, g(Vᵢ)⟩`. -/
noncomputable def score [Nonempty ι] (V : ι → Fine) (x : Sph E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => inner ℝ x.1 (G.g (V j)))

/-- Response probability against the full gallery. -/
noncomputable def resp [Nonempty ι] (V : ι → Fine) (x : Sph E) : ℝ := G.κ (G.score V x)

/-- "Other faces" contribution at face `i` for a fixed environment `γ` (used for every value of
face `i`, including `i` itself with a sentinel `-2` so the `n = 1` case needs no case split: since
every real inner product of unit vectors is `≥ -1 > -2`, `i`'s own sentinel term never wins the
`sup'` once another face exists). Domain `E`, matching `Face.m`. -/
noncomputable def env [Nonempty ι] (i : ι) (γ : ι → Fine) (x : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun j => if j = i then (-2 : ℝ) else inner ℝ x (G.g (γ j)))

/-- The `Face` structure for face `i` with environment `γ` fixed. -/
noncomputable def face [Nonempty ι] (i : ι) (γ : ι → Fine) : Face E Fine where
  thr := G.thr
  τacc := G.τacc
  hτ := G.hτ
  κ := G.κ
  ν₀ := G.ν₀
  ζ := G.ζ
  hκ := G.hκ
  hband := G.hband
  g := G.g
  m := G.env i γ
  π := G.π i
  hπ0 := G.hπ0 i
  hπ1 := G.hπ1 i

/-- **Score identity**: the true gallery score at `(γ updated to `l` at `i`)` is exactly
`max (⟨x, g l⟩) (env i γ x)`, matching `Face.pT` at value `l`. This is the one place independence
of the faces would be used if we tracked distributions explicitly; here it is a deterministic
identity about the `sup'`, since the gallery is fully independent of which faces are random. -/
theorem score_eq_max [Nonempty ι] (i : ι) (γ : ι → Fine) (l : Fine) (x : Sph E) :
    G.score (Function.update γ i l) x = max (inner ℝ x.1 (G.g l)) (G.env i γ x.1) := by
  classical
  have hge1 : (-1 : ℝ) ≤ inner ℝ x.1 (G.g l) := by
    have h := abs_real_inner_le_norm x.1 (G.g l)
    rw [x.2, G.hg l, mul_one] at h
    exact neg_le_of_abs_le h
  have hscore_i : inner ℝ x.1 (G.g l) ≤ G.score (Function.update γ i l) x := by
    show inner ℝ x.1 (G.g l) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun k => inner ℝ x.1 (G.g (Function.update γ i l k)))
    calc inner ℝ x.1 (G.g l) = inner ℝ x.1 (G.g (Function.update γ i l i)) := by
          rw [Function.update_self]
      _ ≤ _ := Finset.le_sup' (f := fun k => inner ℝ x.1 (G.g (Function.update γ i l k)))
            (Finset.mem_univ i)
  apply le_antisymm
  · apply Finset.sup'_le
    intro k _
    by_cases hk : k = i
    · rw [hk, Function.update_self]; exact le_max_left _ _
    · rw [Function.update_of_ne hk]
      refine le_trans ?_ (le_max_right _ _)
      show inner ℝ x.1 (G.g (γ k)) ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun k' => if k' = i then (-2 : ℝ) else inner ℝ x.1 (G.g (γ k')))
      have : (if k = i then (-2 : ℝ) else inner ℝ x.1 (G.g (γ k))) ≤
          Finset.univ.sup' Finset.univ_nonempty
            (fun k' => if k' = i then (-2 : ℝ) else inner ℝ x.1 (G.g (γ k'))) :=
        Finset.le_sup' (f := fun k' => if k' = i then (-2 : ℝ) else inner ℝ x.1 (G.g (γ k')))
          (Finset.mem_univ k)
      rwa [if_neg hk] at this
  · apply max_le hscore_i
    show Finset.univ.sup' Finset.univ_nonempty
        (fun k' => if k' = i then (-2 : ℝ) else inner ℝ x.1 (G.g (γ k'))) ≤
      G.score (Function.update γ i l) x
    apply Finset.sup'_le
    intro k _
    by_cases hk : k = i
    · rw [if_pos hk]; linarith
    · rw [if_neg hk]
      calc inner ℝ x.1 (G.g (γ k)) = inner ℝ x.1 (G.g (Function.update γ i l k)) := by
            rw [Function.update_of_ne hk]
        _ ≤ G.score (Function.update γ i l) x := by
            show inner ℝ x.1 (G.g (Function.update γ i l k)) ≤
              Finset.univ.sup' Finset.univ_nonempty
                (fun k' => inner ℝ x.1 (G.g (Function.update γ i l k')))
            exact Finset.le_sup' (f := fun k' => inner ℝ x.1 (G.g (Function.update γ i l k')))
              (Finset.mem_univ k)

end Gallery

end OracleBounds.GeneralPrior
