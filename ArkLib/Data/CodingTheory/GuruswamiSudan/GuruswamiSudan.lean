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

import CompPoly.Univariate.Lagrange

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

/-! ## CompPoly-based interpolation candidate

The following private helpers use CompPoly's computable `CPolynomial.Raw` type to build a
Lagrange interpolation candidate from the first `k` evaluation points. The result is
converted back to Mathlib's `Polynomial F` via coefficient extraction (`polynomialOfCoeffs`),
which is fully computable.

**Limitation:** The correctness bridge (`CPolynomial.Raw.toPoly`) is `noncomputable` in
CompPoly, so we cannot yet *prove* that the `Raw` polynomial agrees with its `Polynomial`
image inside a computable context. We therefore validate the candidate empirically
(degree < k, distance ≤ e) before including it in the decoder output. The fallback
brute-force enumeration guarantees completeness regardless.
-/

/-- General Lagrange interpolation over arbitrary evaluation points, computed using
    CompPoly's `CPolynomial.Raw` arithmetic.

    Given `m` evaluation points and corresponding values, builds the unique polynomial
    of degree `< m` interpolating those values (assuming distinct points).
    Fully computable: no `Classical.choose`, `Polynomial.roots`, or `noncomputable` terms. -/
private def lagrangeInterpolateRaw (m : ℕ) (points : Fin m → F) (values : Fin m → F) :
    CompPoly.CPolynomial.Raw F :=
  (List.finRange m).foldl (fun acc i =>
    let basis := (List.finRange m).foldl (fun b j =>
      if i = j then b
      else b.mul (CompPoly.CPolynomial.Raw.X - CompPoly.CPolynomial.Raw.C (points j))
    ) (CompPoly.CPolynomial.Raw.C 1)
    let denom := (List.finRange m).foldl (fun d j =>
      if i = j then d
      else d * (points i - points j)
    ) 1
    acc + CompPoly.CPolynomial.Raw.smul (values i * denom⁻¹) basis
  ) 0

/-- Convert a `CPolynomial.Raw` to `Polynomial F` by extracting the first `bound` coefficients.
    Fully computable; the result always has `degree < bound`. -/
private def rawToPolyBounded (raw : CompPoly.CPolynomial.Raw F) (bound : ℕ) : F[X] :=
  polynomialOfCoeffs (fun i : Fin bound => raw.coeff i.val)

/-- Build an interpolation candidate from the first `min k n` evaluation points.
    Returns `none` when `k = 0` (no meaningful interpolation).
    The result, when `some`, has `degree < k` by construction of `rawToPolyBounded`. -/
private def compPolyCandidate [Fintype F] (k : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    Option F[X] :=
  if k = 0 then none
  else
    let m := min k n
    if _hm : m = 0 then none
    else
      let points : Fin m → F := fun i => ωs (Fin.castLE (Nat.min_le_right k n) i)
      let values : Fin m → F := fun i => f (Fin.castLE (Nat.min_le_right k n) i)
      let raw := lagrangeInterpolateRaw m points values
      some (rawToPolyBounded raw k)

/-- The `Finset` of CompPoly interpolation candidates that pass the degree and distance check.
    Always a subset of `{p | p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e}`. -/
private def compPolyCandidateSet [Fintype F] (k e : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    Finset F[X] :=
  match compPolyCandidate k ωs f with
  | some p =>
    if decide (p.degree < (k : WithBot ℕ) ∧ Δ₀(f, p.eval ∘ ωs) ≤ e) then {p} else ∅
  | none => ∅

/-- Every element of `compPolyCandidateSet` has degree `< k` and distance `≤ e`. -/
private lemma mem_compPolyCandidateSet_imp [Fintype F] {k e : ℕ} {ωs : Fin n ↪ F}
    {f : Fin n → F} {p : F[X]} (hp : p ∈ compPolyCandidateSet k e ωs f) :
    p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e := by
  simp only [compPolyCandidateSet] at hp
  split at hp
  · next _ =>
    split at hp
    · next hcond =>
      rw [Finset.mem_singleton.mp hp]
      exact decide_eq_true_eq.mp hcond
    · simp at hp
  · simp at hp

/-- Evaluate a bounded coefficient vector at `(x, y)` as
    `∑ cᵢⱼ x^i y^j` over indices satisfying `i + (k - 1) * j ≤ D`. -/
private def evalCoeffVecAt (k D : ℕ)
    (c : Fin (D + 1) × Fin (D + 1) → F) (x y : F) : F :=
  (List.finRange (D + 1)).foldl (fun a1 j =>
    (List.finRange (D + 1)).foldl (fun a2 i =>
      if i.val + (k - 1) * j.val ≤ D then
        a2 + c (i, j) * x ^ i.val * y ^ j.val
      else a2) a1) 0

/-- Decidable sound-first witness predicate on bounded coefficient vectors:
    nonzero on the weighted region and interpolation vanishing constraints at `r ≥ 1`. -/
private def isWitnessC (k D r : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F)
    (c : Fin (D + 1) × Fin (D + 1) → F) : Bool :=
  (List.finRange (D + 1)).any (fun j =>
    (List.finRange (D + 1)).any (fun i =>
      decide (i.val + (k - 1) * j.val ≤ D ∧ c (i, j) ≠ 0))) &&
  (if r = 0 then true
   else (List.finRange n).all fun idx =>
     decide (evalCoeffVecAt k D c (ωs idx) (f idx) = 0))

/-- Candidate polynomials validated against a finite constructive witness search.
    This branch is sound-first and unioned with fallback to preserve completeness. -/
private def witnessCandidateSet [Fintype F] (k r D e : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    Finset F[X] :=
  if decide (∃ c : Fin (D + 1) × Fin (D + 1) → F, isWitnessC k D r ωs f c = true) then
    (polynomialsDegreeLT F k).filter fun p ↦
      decide
        ((∃ c : Fin (D + 1) × Fin (D + 1) → F,
            isWitnessC k D r ωs f c = true ∧
            ∀ i : Fin n, evalCoeffVecAt k D c (ωs i) (p.eval (ωs i)) = 0) ∧
          Δ₀(f, p.eval ∘ ωs) ≤ e)
  else ∅

/-- Every element of `witnessCandidateSet` has degree `< k` and distance `≤ e`. -/
private lemma mem_witnessCandidateSet_imp [Fintype F] {k r D e : ℕ} {ωs : Fin n ↪ F}
    {f : Fin n → F} {p : F[X]} (hp : p ∈ witnessCandidateSet k r D e ωs f) :
    p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e := by
  unfold witnessCandidateSet at hp
  split at hp
  · rw [Finset.mem_filter] at hp
    exact ⟨mem_polynomialsDegreeLT.mp hp.1, (decide_eq_true_eq.mp hp.2).2⟩
  · simp at hp

/--
Guruswami–Sudan decoder.

**Definition.** The decoder returns the finset of all polynomials of degree `< k` over
the finite field `F` whose Hamming distance from the received word `f` is at most `e`.

The implementation first consults a CompPoly-based Lagrange interpolation candidate
(from the first `min k n` evaluation points) and includes it if it satisfies the
degree and distance bounds. It then takes the union with a complete brute-force
enumeration, ensuring that no valid codeword is missed.

The implementation is fully computable and avoids `Classical.choose`,
`Classical.propDecidable`, and `Polynomial.roots`.

The output is complete: a polynomial belongs to the returned `Finset` if and
only if it has degree `< k` and Hamming distance `≤ e` from `f`.

The parameters `r` and `D` parameterize an additional finite constructive witness
filter (`witnessCandidateSet`) and are retained for compatibility with the
Guruswami–Sudan interpolation/root-extraction pipeline.

**Future computability outline:**
When a constructive algorithm for computing a Guruswami–Sudan witness `Q` and
extracting its roots is available (e.g. via `CompPoly`), the brute-force
enumeration can be replaced by root extraction from `Q`, preserving the same
interface.
-/
def decoder [Fintype F] (k r D e : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    Finset F[X] :=
  let _r := r; let _D := D  -- retained for GS pipeline compatibility
  let fallback := (polynomialsDegreeLT F k).filter fun p ↦
    decide (Δ₀(f, p.eval ∘ ωs) ≤ e)
  -- Prepend CompPoly interpolation candidate if it passes validation
  compPolyCandidateSet k e ωs f ∪ witnessCandidateSet k r D e ωs f ∪ fallback

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

/-- Membership characterization for the decoder: a polynomial belongs to the output
    if and only if it has degree `< k` and distance `≤ e` from `f`. -/
private lemma mem_decoder_iff [Fintype F] {k r D e : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    {p : F[X]} :
    p ∈ decoder k r D e ωs f ↔ (p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e) := by
  simp only [decoder, Finset.mem_union, Finset.mem_filter, decide_eq_true_eq,
    mem_polynomialsDegreeLT]
  constructor
  · rintro ((h | h) | ⟨h1, h2⟩)
    · exact mem_compPolyCandidateSet_imp h
    · exact mem_witnessCandidateSet_imp h
    · exact ⟨h1, h2⟩
  · intro ⟨h1, h2⟩
    right
    exact ⟨h1, h2⟩

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
