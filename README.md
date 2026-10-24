# oracle-bounds-lean

Machine-checked bounds on what can be learned from a one-bit face-watchlist oracle.

The setting: a service holds a list of face templates (unit vectors in a face-embedding space).
A query is one template; the service answers a single bit, "match" or "no match", flipped with a
fixed probability so that the answer carries noise. These files prove, in Lean 4 against Mathlib,
how many queries an attacker needs to (i) decide whether a given person is listed, (ii) learn about
people who never appear, and (iii) recover stored templates from nothing; and they prove what the
best known attacks achieve, so the two sides can be compared.

The results are stated and used in *Airlock: practical implications of the technical analysis* (H. Hayton, 2026). Appendix B
of that document gives the mathematics in paper form, and its §B.9 lists the declaration here that
checks each result. The table below is the same map.

## Build

Toolchain and Mathlib are pinned (`lean-toolchain`, `lake-manifest.json`: Lean `v4.32.0`,
Mathlib `v4.32.0`). With [elan](https://github.com/leanprover/elan) installed:

```
lake exe cache get   # fetch the pre-built Mathlib binaries (several GB)
lake build           # builds every module imported by OracleBounds.lean
```

The build prints `#print axioms` output for the headline theorems. Every declaration depends only
on `propext`, `Classical.choice` and `Quot.sound`; no module contains `sorry`.

To replay a module through the independent kernel checker:

```
lake env leanchecker OracleBounds.GeneralPrior.MatchCap
```

(`leanchecker` replays only the named module's own declarations, so loop over the imports in
`OracleBounds.lean` for a full replay.)

## Layout

| directory | contents |
|---|---|
| `OracleBounds/V6/` | the adaptive query process and its ghost coupling (`Process`), the transcript information calculus (`InfoProcess`), and the earlier uniform-prior ("plant") results these grew out of |
| `OracleBounds/GeneralPrior/` | lower bounds for an arbitrary finite prior over templates: coupling, membership, information budget, Fano, contact bound, density and continuous-prior transfer, match cap |
| `OracleBounds/Attacks/` | upper bounds: concrete attacks (pool probing, SPRT, bisection localisers, random search, noisy search, candidate sieve, passive-venue mining) with their costs |

Module docstrings record which internal working note each statement was transcribed from; those
notes are not part of this repository. The public statement of each result is Appendix B of the
document above.

## Results to declarations

| Appendix B result | declaration(s) | module |
|---|---|---|
| KL chain rule, per-round cost (Lemma B.1) | `klRounds`, `klRounds_le_cost` | `V6/InfoProcess`, `GeneralPrior/Membership` |
| Bretagnolle–Huber (Lemma B.2) | `bretagnolle_huber` | `GeneralPrior/Membership` |
| SPRT and the membership theorem (Lemma B.3, Thm B.4) | `membership_tight`, `membership_bh`, `membership_reach_needed`, `membership_reach_needed1`, `sprt_membership`, `sprt_typeI_avg`, `one_probe_decides` | `GeneralPrior/MembershipTight`, `Membership`, `MembershipRev`, `SPRT` |
| Non-visitors (Cor B.6) | `passive_population`, `passive_venue_gallery`, `passive_venue_arrivals_H0`, `iid_bridge` | `GeneralPrior/Passive`, `Attacks/PassiveGallery` |
| Ghost coupling and the contact bound (Lemma B.7, Thm B.8) | `val_coupling`, `ghost_bound_weighted`, `gallery_hitting`, `gallery_recovery`, `thm61_3`, `cor62_i` | `V6/Process`, `GeneralPrior/Coupling`, `GalleryBounds`, `Corollaries` |
| Information budget, superadditivity, Fano, information bound (Lemmas B.10–B.12, Thm B.13) | `info_le_global`, `info_le_cap`, `mutualInfo_superadditive_prior`, `small_ball_fano`, `recovery_count_budget`, `thm61_4` | `GeneralPrior/Budget`, `Information`, `RecoveryCount`, `Corollaries` |
| Net attack, pool case (Thm B.14(a)) | `pool_PN`, `pathProb_pool_full` | `Attacks/Pool` |
| Random search then bisection (Thm B.15) | `thm63_markov`, `thm63_chernoff`, `L2_correct` | `Attacks/RandomSearch`, `RandomSearchChernoff`, `Localise2` |
| Cap measure inequality (Lemma B.16) | `cap_measure_sharp_lt` | `GeneralPrior/CapMeasureSharp` |
| Per-person match cap (Thm B.22) | `info_le_concave`, `gallery_info_le_concave`, `match_cap_fano` | `GeneralPrior/MatchCap` |
| Refinement bits, projection step (Lemma B.23) | `proj_ball` | `GeneralPrior/Density` |

Theorem numbers refer to the document's current draft and may shift; the declaration names are
stable.

## What is not in Lean

Stated in the document and proved there on paper:

* the untruncated SPRT and the visitor variant of the membership count;
* the symmetry step for the context-free attacker (Mathlib does not yet expose the uniform measure
  on the sphere as the image of Haar measure on the orthogonal group); the cap inequality it rests
  on is in Lean;
* the net attack for a general net and its noisy version;
* random search for templates near a known subspace (only the full-space case is formalised);
* the labelled variant of the information bound;
* the refinement-bits lemma (its hypothesis is a model of face space, not a theorem).

Parameter values (false match rate, best-probe factor, list size, local dimension) are inputs, not
theorems; every figure in the document scales with them as stated there.

## Licence

Apache 2.0, see `LICENSE`.
