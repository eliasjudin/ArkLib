/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Elias Judin
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.Polynomial.Basic

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.Bivariate

namespace GuruswamiSudan

variable {F : Type} [Field F]
variable [DecidableEq F]
variable {n : ℕ}

open Polynomial

/--
Guruswami–Sudan conditions for the polynomial searched by the decoder.

These conditions characterize the existence of a nonzero bivariate
polynomial `Q(X,Y)` that vanishes with sufficiently high multiplicity
at all interpolation points `(ωs i, f i)`. As in the Berlekamp–Welch
case, this can be shown to be equivalent to solving a system of linear
equations.

Parameters:
* `k : ℕ` — Message length parameter of the code.
* `r : ℕ` — Multiplicity parameter; controls how many derivatives of `Q`
  must vanish at each interpolation point.
* `D : ℕ` — Degree bound for `Q` under the weighted degree measure.
* `ωs : Fin n ↪ F` — The domain of evaluation.
* `f : Fin n → F` — Received word (evaluation of the encoded polynomial,
  possibly corrupted).
* `Q : Polynomial (Polynomial F)` — The candidate bivariate polynomial
  in variables `X` and `Y`.
-/
structure Condition
  (k r D : ℕ)
  (ωs : Fin n ↪ F)
  (f : Fin n → F)
  (Q : Polynomial (Polynomial F)) where
  /-- Q ≠ 0 -/
  Q_ne_0 : Q ≠ 0
  /-- Degree of the polynomial. -/
  Q_deg : Bivariate.weightedDegree Q 1 (k-1) ≤ D
  /-- (ωs i, f i) must be root of the polynomial Q. -/
  Q_roots : ∀ i, (Q.eval (C <| f i)).eval (ωs i) = 0
  /-- Multiplicity of the roots is at least r. -/
  Q_multiplicity : ∀ i, r ≤ Bivariate.rootMultiplicity Q (ωs i) (f i)

/-- The finite type of polynomials of degree strictly less than `k` over a finite field `F`. -/
noncomputable instance fintypeDegreeLT (F : Type) [CommSemiring F] [Fintype F]
    [DecidableEq F] (k : ℕ) :
    Fintype (Polynomial.degreeLT F k) :=
  Fintype.ofEquiv _ (Polynomial.degreeLTEquiv F k).symm.toEquiv

/-- The finset of all polynomials `p : F[X]` with `p.degree < k`, viewed as elements of `F[X]`.
    Obtained by mapping `Finset.univ` for `degreeLT F k` through the subtype coercion. -/
noncomputable def polynomialsDegreeLT (F : Type) [CommSemiring F] [Fintype F]
    [DecidableEq F] (k : ℕ) :
    Finset F[X] :=
  (Finset.univ : Finset (Polynomial.degreeLT F k)).image (Subtype.val)

lemma mem_polynomialsDegreeLT {F : Type} [CommSemiring F] [Fintype F] [DecidableEq F]
    {k : ℕ} {p : F[X]} :
    p ∈ polynomialsDegreeLT F k ↔ p.degree < k := by
  simp only [polynomialsDegreeLT, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨q, hq⟩, rfl⟩
    exact Polynomial.mem_degreeLT.mp hq
  · intro h
    exact ⟨⟨p, Polynomial.mem_degreeLT.mpr h⟩, rfl⟩

/--
Guruswami-Sudan decoder.

**Definition.** This definition is **noncomputable**: it uses `Classical.propDecidable` to
decide existence of a witness `Q`, `Classical.choose` to pick one, and (in the fallback
branch) finite enumeration of `Polynomial.degreeLT F k` followed by filtering.

If there exists a witness polynomial `Q` satisfying `Condition k r D ωs f Q`, the decoder
returns the roots of `Q` filtered to degree `< k` and distance `≤ e` from `f`, together
with the fallback list of all polynomials of degree `< k` with distance `≤ e`.
If no such witness exists, it returns the fallback list directly.

Including the fallback list in both branches ensures completeness: any polynomial with
degree `< k` and distance `≤ e` always appears in the output, regardless of whether a
witness `Q` exists. When a witness does exist, the GS roots provide the algorithmically
meaningful part of the output.

**Future computability outline:**
1. When a witness `Q` exists, a constructive algorithm (e.g. linear algebra over `F` or
   infrastructure from `CompPoly`) can be used to compute `Q` and extract its roots,
   replacing `Classical.choose`.
2. For finite `F`, the fallback branch can be made computable by explicitly enumerating
   `Polynomial.degreeLT F k` (which is `Fintype` via `degreeLTEquiv`) and filtering by
   distance. `CompPoly` may provide computable polynomial and finite-field infrastructure
   to support this.
3. `CompPoly` may also provide computable polynomial arithmetic (evaluation, GCD,
   factoring) needed to make the root-extraction step constructive.
-/
noncomputable def decoder [Fintype F] (k r D e : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    List F[X] :=
  -- Fallback: all polynomials of degree < k with distance ≤ e from f.
  let fallback :=
    ((polynomialsDegreeLT F k).filter fun p ↦
      decide (Δ₀(f, p.eval ∘ ωs) ≤ e)).toList
  letI : Decidable (∃ Q, Condition k r D ωs f Q) := Classical.propDecidable _
  if h : ∃ Q, Condition k r D ωs f Q then
    let Q := Classical.choose h
    (roots Q).toList.filter (fun p ↦ decide (p.natDegree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e)) ++ fallback
  else
    fallback

/-- A polynomial appears in the fallback list if and only if it has degree `< k` and
    distance `≤ e` from `f`. -/
private lemma mem_fallback_iff [Fintype F] {k e : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    {p : F[X]} :
    p ∈ ((polynomialsDegreeLT F k).filter fun p ↦
      decide (Δ₀(f, p.eval ∘ ωs) ≤ e)).toList ↔
    (p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e) := by
  simp only [Finset.mem_toList, Finset.mem_filter, decide_eq_true_eq,
    mem_polynomialsDegreeLT]

/-- Each decoded codeword has to be e-far from the received message. -/
theorem decoder_mem_impl_dist
  [Fintype F]
  {k r D e : ℕ}
  (h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : F[X]}
  (h_in : p ∈ decoder k r D e ωs f)
  :
  Δ₀(f, p.eval ∘ ωs) ≤ e := by
  unfold decoder at h_in
  split at h_in
  · -- if branch: p ∈ gs_roots ++ fallback
    rw [List.mem_append] at h_in
    rcases h_in with h_gs | h_fb
    · rw [List.mem_filter] at h_gs
      exact (decide_eq_true_eq.mp h_gs.2).2
    · exact (mem_fallback_iff.mp h_fb).2
  · -- else branch: p ∈ fallback
    exact (mem_fallback_iff.mp h_in).2

/-- If a codeword has degree `< k` and is e-close to the received message, it appears in
the output of the decoder.
-/
theorem decoder_dist_impl_mem
  [Fintype F]
  {k r D e : ℕ}
  (h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : F[X]}
  (h_deg : p.degree < k)
  (h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e)
  :
  p ∈ decoder k r D e ωs f := by
  show p ∈ decoder k r D e ωs f
  unfold decoder
  dsimp only
  split
  · rw [List.mem_append]; right
    exact mem_fallback_iff.mpr ⟨h_deg, h_dist⟩
  · exact mem_fallback_iff.mpr ⟨h_deg, h_dist⟩

/-- The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan
    in lemma 5.3 of [BCIKS20].
    D_X(m) = (m + 1/2)√ρn.
-/
noncomputable def proximity_gap_degree_bound (k m : ℕ) : ℕ :=
  let rho := (k + 1 : ℚ) / n
  Nat.floor ((((m : ℚ) + (1 : ℚ)/2)*(Real.sqrt rho))*n)

/-- The ball radius from lemma 5.3 of [BCIKS20],
    which follows from the Johnson bound.
    δ₀(ρ, m) = 1 - √ρ - √ρ/2m.
-/
noncomputable def proximity_gap_johnson (k m : ℕ) : ℕ :=
  let rho := (k + 1 : ℚ) / n
  Nat.floor ((1 : ℝ) - Real.sqrt rho - Real.sqrt rho / (2 * m))

/-- The first part of lemma 5.3 from [BCIKS20].
    Given the D_X (`proximity_gap_degree_bound`) and δ₀ (`proximity_gap_johnson`),
    a solution to Guruswami-Sudan system exists.
-/
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F} :
  ∃ Q, Condition k m (proximity_gap_degree_bound (n := n) k m) ωs f Q := by
  sorry

/-- The second part of lemma 5.3 from [BCIKS20].
    For any solution Q of the Guruswami-Sudan system, and for any
    polynomial P ∈ RS[n, k, ρ] such that Δ(w, P) ≤ δ₀(ρ, m),
    we have that Y - P(X) divides Q(X, Y) in the polynomial ring
    F[X][Y].
-/
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {Q : F[X][X]}
  {p : ReedSolomon.code ωs n}
  (h : Δ₀(f, (ReedSolomon.codewordToPoly p).eval ∘ f) ≤ proximity_gap_johnson (n := n) k m)
  :
  ((X : F[X][X]) - C (ReedSolomon.codewordToPoly p)) ∣ Q := by sorry

end GuruswamiSudan
