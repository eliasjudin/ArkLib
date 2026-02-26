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
import ArkLib.Data.Polynomial.Interface

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

/-- Recover a polynomial from its first `k` coefficients when its degree is below `k`. -/
private lemma polynomialOfCoeffs_coeffsOfPolynomial_of_degree_lt
    {F : Type} [CommSemiring F] [DecidableEq F] {k : ℕ} {p : F[X]}
    (h : p.degree < (k : WithBot ℕ)) :
    polynomialOfCoeffs (coeffsOfPolynomial (deg := k) p) = p := by
  ext x
  simp only [coeff_polynomialOfCoeffs_eq_coeffs', coeffsOfPolynomial]
  split
  · rfl
  · symm
    exact Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le h (by exact_mod_cast Nat.le_of_not_lt ‹_›))

/-- The finset of all polynomials `p : F[X]` with `p.degree < k`, viewed as elements of `F[X]`.
    Constructed computably by enumerating coefficient vectors `Fin k → F`.
    Note that this always includes `0`, since `(0 : F[X]).degree = ⊥ < (k : WithBot ℕ)`. -/
def polynomialsDegreeLT (F : Type) [CommSemiring F] [Fintype F]
    [DecidableEq F] (k : ℕ) :
    Finset F[X] :=
  (Finset.univ : Finset (Fin k → F)).image polynomialOfCoeffs

lemma mem_polynomialsDegreeLT {F : Type} [CommSemiring F] [Fintype F] [DecidableEq F]
    {k : ℕ} {p : F[X]} :
    p ∈ polynomialsDegreeLT F k ↔ p.degree < k := by
  simp only [polynomialsDegreeLT, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨coeffs, rfl⟩
    exact degree_polynomialOfCoeffs_deg_lt_deg
  · intro h
    exact ⟨coeffsOfPolynomial p, polynomialOfCoeffs_coeffsOfPolynomial_of_degree_lt h⟩

/--
Guruswami–Sudan decoder.

**Definition.** The decoder enumerates all polynomials of degree `< k` over the
finite field `F` and returns the finset of those whose Hamming distance from the
received word `f` is at most `e`. The implementation is fully computable and
avoids `Classical.choose`, `Classical.propDecidable`, and `Polynomial.roots`.

The output is complete: a polynomial belongs to the returned `Finset` if and
only if it has degree `< k` and Hamming distance `≤ e` from `f`.

The parameters `r` and `D` are retained in the signature for compatibility with
the Guruswami–Sudan interpolation/root-extraction pipeline; they are not used by
the current brute-force implementation.

**Future computability outline:**
When a constructive algorithm for computing a Guruswami–Sudan witness `Q` and
extracting its roots is available (e.g. via `CompPoly`), the brute-force
enumeration can be replaced by root extraction from `Q`, preserving the same
interface.
-/
def decoder [Fintype F] (k r D e : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    Finset F[X] :=
  let _r := r; let _D := D  -- retained for GS pipeline compatibility
  (polynomialsDegreeLT F k).filter fun p ↦
    decide (Δ₀(f, p.eval ∘ ωs) ≤ e)

/-- Computable fallback candidates: degree `< k` and distance `≤ e` from `f`. -/
private def fallbackCandidates [Fintype F] (k e : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    Finset F[X] :=
  (polynomialsDegreeLT F k).filter fun p ↦ decide (Δ₀(f, p.eval ∘ ωs) ≤ e)

/-- Membership characterization for `fallbackCandidates`. -/
private lemma mem_fallbackCandidates_iff [Fintype F] {k e : ℕ} {ωs : Fin n ↪ F}
    {f : Fin n → F} {p : F[X]} :
    p ∈ fallbackCandidates k e ωs f ↔ (p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e) := by
  simp only [fallbackCandidates, Finset.mem_filter, decide_eq_true_eq,
    mem_polynomialsDegreeLT]

/-- Bounded root candidates from an explicit `Q`, restricted to degree `< k` and distance `≤ e`. -/
private noncomputable def boundedRootCandidates [Fintype F] (Q : F[X][X]) (k e : ℕ)
    (ωs : Fin n ↪ F) (f : Fin n → F) : Finset F[X] :=
  (polynomialsDegreeLT F k).filter fun p ↦
    decide (Q.eval p = 0 ∧ Δ₀(f, p.eval ∘ ωs) ≤ e)

/-- Membership characterization for `boundedRootCandidates`. -/
private lemma mem_boundedRootCandidates_iff [Fintype F] {Q : F[X][X]} {k e : ℕ}
    {ωs : Fin n ↪ F} {f : Fin n → F} {p : F[X]} :
    p ∈ boundedRootCandidates Q k e ωs f ↔
    (p.degree < k ∧ Q.eval p = 0 ∧ Δ₀(f, p.eval ∘ ωs) ≤ e) := by
  simp only [boundedRootCandidates, Finset.mem_filter, decide_eq_true_eq,
    mem_polynomialsDegreeLT]

/-- Every bounded-root candidate is a fallback candidate. -/
private lemma boundedRootCandidates_subset_fallbackCandidates [Fintype F]
    {Q : F[X][X]} {k e : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F} :
    boundedRootCandidates Q k e ωs f ⊆ fallbackCandidates k e ωs f := by
  intro p hp
  rw [mem_boundedRootCandidates_iff] at hp
  rw [mem_fallbackCandidates_iff]
  exact ⟨hp.1, hp.2.2⟩

/-- Membership characterization for the decoder: a polynomial belongs to the output
    if and only if it has degree `< k` and distance `≤ e` from `f`. -/
private lemma mem_decoder_iff [Fintype F] {k r D e : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    {p : F[X]} :
    p ∈ decoder k r D e ωs f ↔ (p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e) := by
  simp only [decoder, Finset.mem_filter, decide_eq_true_eq, mem_polynomialsDegreeLT]

/-- Each decoded codeword has to be e-far from the received message. -/
theorem decoder_mem_impl_dist
  [Fintype F]
  {k r D e : ℕ}
  (_h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : F[X]}
  (h_in : p ∈ decoder k r D e ωs f)
  :
  Δ₀(f, p.eval ∘ ωs) ≤ e := by
  exact (mem_decoder_iff.mp h_in).2

/-- If a codeword has degree `< k` and is e-close to the received message, it appears in
the output of the decoder.
-/
theorem decoder_dist_impl_mem
  [Fintype F]
  {k r D e : ℕ}
  (_h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : F[X]}
  (h_deg : p.degree < k)
  (h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e)
  :
  p ∈ decoder k r D e ωs f := by
  exact mem_decoder_iff.mpr ⟨h_deg, h_dist⟩

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
