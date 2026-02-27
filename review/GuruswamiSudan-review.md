# Code Review: Guruswami–Sudan Decoder Refactoring

**Branch:** `claude/review-lean4-changes-jlYAv`
**File:** `ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean`
**Commits reviewed:** 10 commits (`fa079fb`..`424bc72`)
**Lean version:** 4.28.0
**Review tooling:** lean4-skills (scripts), lean-lsp-mcp (registered), `lake env lean`

---

## Lean4 Review Report

**Scope:** `ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean` (file)

---

### Build Status

```
✔ [2481/2481] Built ArkLib.Data.CodingTheory.GuruswamiSudan.GuruswamiSudan (29s)
```

**Result: PASSING** — Zero errors. Only 2 expected `sorry` warnings (pre-existing, not introduced by these commits).

Direct `lake env lean` diagnostic output:
```
GuruswamiSudan.lean:324:6: warning: declaration uses `sorry`  ← guruswami_sudan_for_proximity_gap_existence
GuruswamiSudan.lean:334:6: warning: declaration uses `sorry`  ← guruswami_sudan_for_proximity_gap_property
```

No other warnings in the file itself.

---

### Axiom Status

All declarations use only standard Lean 4 axioms (`#print axioms` results):

| Declaration | Axioms |
|-------------|--------|
| `decoder` | `propext`, `Classical.choice`, `Quot.sound` |
| `decoder_mem_impl_dist` | `propext`, `Classical.choice`, `Quot.sound` |
| `decoder_dist_impl_mem` | `propext`, `Classical.choice`, `Quot.sound` |
| `polynomialsDegreeLT` | `propext`, `Classical.choice`, `Quot.sound` |
| `proximity_gap_degree_bound` | `propext`, `Classical.choice`, `Quot.sound` |
| `proximity_gap_johnson` | `propext`, `Classical.choice`, `Quot.sound` |

**Result: ✓ Standard axioms only.** The `Classical.choice` entry is inherited from Mathlib
infrastructure (e.g., `Finset`, `Polynomial` library), not from the decoder implementation
itself. Crucially, `decoder` is **not** marked `noncomputable` — Lean's kernel verified
computability at definition time.

---

### Summary of Changes (10 commits)

The refactoring replaces an `noncomputable opaque` classical decoder with a fully
computable `Finset`-based implementation. Change statistics:
`+226` insertions, `-17` deletions in a single file.

**Before (HEAD~10):**
```lean
noncomputable opaque decoder (k r D e : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) : List F[X] :=
  letI : Decidable (∃ Q, Condition k r D ωs f Q) := Classical.propDecidable _
  if h : ∃ Q, Condition k r D ωs f Q then
    let Q := Classical.choose h
    (roots Q).toList.filter fun p ↦ p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e
  else []
```
Both `decoder_mem_impl_dist` and `decoder_dist_impl_mem` were `sorry`.

**After (HEAD):**
```lean
def decoder [Fintype F] (k r D e : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    Finset F[X] :=
  compPolyCandidateSet k e ωs f ∪ witnessCandidateSet k r D e ωs f ∪ fallback
```
Both correctness theorems are now fully proven via `mem_decoder_iff`.

---

### Sorry Audit (2 remaining)

Both sorrys are **pre-existing** — they were present in the code before these 10 commits
and are not newly introduced.

| Line | Theorem | Status | Notes |
|------|---------|--------|-------|
| 326 | `guruswami_sudan_for_proximity_gap_existence` | Pre-existing `sorry` | Existence of GS polynomial Q for proximity-gap parameters. Requires: dimension-counting argument showing the linear system for Q has a non-trivial solution (Lemma 5.3 of [BCIKS20]). |
| 340 | `guruswami_sudan_for_proximity_gap_property` | Pre-existing `sorry` + **BUG** | See Issue #1 below. |

---

### Issues

#### Issue #1 — HIGH: Typo in `guruswami_sudan_for_proximity_gap_property` hypothesis (pre-existing)

**Location:** Lines 334–341
**Introduced by:** Pre-existing (before these 10 commits)
**Category:** Incorrect statement

The hypothesis reads:
```lean
(h : Δ₀(f, (ReedSolomon.codewordToPoly p).eval ∘ f) ≤ proximity_gap_johnson (n := n) k m)
```

Note `∘ f`: this computes `i ↦ poly.eval (f i)`, i.e., the codeword polynomial evaluated at
the *received word values* `f : Fin n → F`. This is not the intended meaning.

The correct statement should use `∘ ωs` (the evaluation domain), consistent with the
distance notation used throughout the file:
```lean
(h : Δ₀(f, (ReedSolomon.codewordToPoly p).eval ∘ ωs) ≤ proximity_gap_johnson (n := n) k m)
```

**Evidence:** `#check @GuruswamiSudan.guruswami_sudan_for_proximity_gap_property` shows:
```
Δ₀(f, (fun x => Polynomial.eval x (ReedSolomon.codewordToPoly p)) ∘ f) ≤ ...
```
Compare with `decoder_mem_impl_dist`: `Δ₀(f, (fun x => Polynomial.eval x p) ∘ ⇑ωs)`.

**Recommendation:** Fix `∘ f` → `∘ ωs` before attempting to close the sorry.

---

#### Issue #2 — MEDIUM: Unused hypothesis `_h_e` in both public theorems

**Location:** Lines 278, 294
**Category:** API design / misleading specification

Both `decoder_mem_impl_dist` and `decoder_dist_impl_mem` accept:
```lean
(_h_e : e ≤ n - Real.sqrt (k * n))
```
The `_` prefix confirms this hypothesis is **never used** in the proofs. The decoder is
correct for *any* `e`, not only `e ≤ n - √(kn)`.

The hypothesis is retained for compatibility with the original API, but it creates the
false impression that the correctness of the decoder depends on the Johnson-bound radius.
The current implementation is actually a correct-by-construction finite enumeration that
works regardless of `e`.

**Recommendation:** Either:
- Remove `_h_e` from both theorem signatures (breaking change), or
- Explicitly document in the docstring that the hypothesis is vacuously accepted and
  retained for forward-compatibility with the eventual GS algorithm instantiation, or
- Replace with a `(h_e : True)` or `(_h_e : _root_.True)` to make the intent obvious.

---

#### Issue #3 — MEDIUM: Breaking API change in `decoder_dist_impl_mem`

**Location:** Line 299
**Category:** Compatibility

The original `decoder_dist_impl_mem` only required:
```lean
(h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e)
```
The new version adds:
```lean
(h_deg : p.degree < k)
```

This is a **breaking change** for any callers. The original theorem was actually *incorrect*
(a polynomial not of degree < k could not possibly be in the decoder output, so the original
sorry implied something false). The new version is the correct statement.

**Recommendation:** Document this intentional breaking change in the commit message or
a CHANGELOG entry, and update any downstream callers.

---

#### Issue #4 — MEDIUM: `[Fintype F]` constraint added to `decoder`

**Location:** Line 239
**Category:** Compatibility / generality

The original `noncomputable opaque` decoder did not require `[Fintype F]`. The new
computable decoder does. This is a **necessary and expected** trade-off for computability,
but any downstream code instantiating the decoder over an infinite field (e.g., ℚ) will
now fail.

**Recommendation:** Document this constraint change. Consider a `noncomputable`
version without `[Fintype F]` for use in infinite-field contexts if needed.

---

#### Issue #5 — LOW: Dead `let _r` and `let _D` bindings in `decoder`

**Location:** Line 241
**Category:** Code cleanliness

```lean
let _r := r; let _D := D  -- retained for GS pipeline compatibility
```

The let-binding analysis (lean4-skills `analyze_let_usage.py`) confirms `_r` is
**UNUSED** — it is never referenced in the body. The parameters `r` and `D` are passed
directly to `witnessCandidateSet` on line 245. The `_r` and `_D` bindings serve no
purpose beyond signalling intent via a comment.

**Recommendation:** Remove the dead bindings and rely on the inline comment to explain why
`r` and `D` are retained as function parameters.

---

#### Issue #6 — LOW: `isWitnessC` does not check higher multiplicity (`r > 1`)

**Location:** Lines 180–187
**Category:** Incomplete witness check (sound but tight only for r=1)

The `Condition` structure requires `r ≤ Bivariate.rootMultiplicity Q (ωs i) (f i)`.
For `r = 1` this reduces to `Q(ωs_i, f_i) = 0`. For `r > 1` it requires partial
derivatives to vanish as well.

`isWitnessC` only checks the `r = 0` / `r ≥ 1` cases uniformly:
```lean
(if r = 0 then true
 else (List.finRange n).all fun idx =>
   decide (evalCoeffVecAt k D c (ωs idx) (f idx) = 0))
```

For `r > 1`, the check is **incomplete** (it only verifies `Q(ωs_i, f_i) = 0`, not
higher-order vanishing). This means `witnessCandidateSet` may include false positives for
`r > 1` calls — but soundness is still preserved by the `fallback` branch.

The current doc-string describes this as "sound-first" which is accurate. Consider adding
a note that the witness check is exact only for `r ≤ 1`.

---

### Golfing Opportunities

Identified by lean4-skills `find_golfable.py` (with false-positive filtering):

| Location | Pattern | Priority | Suggestion |
|----------|---------|----------|------------|
| Line 285 | `by exact ...` wrapper (2 lines) | MEDIUM | `(mem_decoder_iff.mp h_in).2` can be written in term mode: `exact (mem_decoder_iff.mp h_in).2` → `(mem_decoder_iff.mp h_in).2` |
| Line 301 | `by exact ...` wrapper (2 lines) | MEDIUM | Similarly, `mem_decoder_iff.mpr ⟨h_deg, h_dist⟩` |
| Lines 266–273 | Constructor branch (7 lines) | LOW | The `rintro ((h \| h) \| ⟨h1, h2⟩)` proof could use `simp [mem_compPolyCandidateSet_imp, mem_witnessCandidateSet_imp, mem_fallbackCandidates_iff]` or `aesop` |

**Note:** All golfing opportunities are minor style improvements. The current proofs are
clear and readable.

---

### Complexity Notes

The decoder implementation is correct for verification purposes but has high runtime
complexity unsuitable for production use:

| Branch | Complexity | Notes |
|--------|-----------|-------|
| `compPolyCandidateSet` | O(min(k,n)²) | Lagrange interpolation, fast in practice |
| `witnessCandidateSet` | O(\|F\|^((D+1)²)) | Exhaustive search over coefficient vectors |
| `fallbackCandidates` | O(\|F\|^k) | Enumeration of all degree-<k polynomials |

The union correctness is entirely determined by `fallbackCandidates` via `mem_decoder_iff`.
The first two branches are pre-filters that do not affect the proven output set.

---

### Positive Observations

1. **Computability achieved**: `decoder` is a `def` (not `noncomputable def`). Lean's
   kernel verified this at elaboration time. The implementation successfully avoids
   `Classical.propDecidable`, `Classical.choose`, and `Polynomial.roots` in the
   computation.

2. **`mem_decoder_iff` is the key insight**: The private lemma cleanly characterizes
   membership in a single biconditional, making both public theorems trivial one-liners.
   This is excellent proof architecture.

3. **`polynomialsDegreeLT` is reusable**: The computable finset of all degree-<k
   polynomials is a general utility that could be upstreamed. The
   `mem_polynomialsDegreeLT` characterization lemma is clean and correctly uses
   `polynomialOfCoeffs_coeffsOfPolynomial_of_degree_lt`.

4. **Three-branch design is clearly explained**: The `/-! ## CompPoly-based interpolation
   candidate -/` section marker and the inline comments in `decoder`'s docstring
   accurately describe the design limitations and future improvement path.

5. **Return type upgrade**: Changing `List F[X]` → `Finset F[X]` is mathematically
   correct (the decoder output is a set, not a list) and enables set-algebra lemmas.

6. **No new sorrys introduced**: All 2 sorrys in the file were pre-existing. The commits
   closed the two main correctness obligations (`decoder_mem_impl_dist` and
   `decoder_dist_impl_mem`).

---

### Recommendations

**Must fix before merge:**
1. Fix `∘ f` → `∘ ωs` typo in `guruswami_sudan_for_proximity_gap_property` (Issue #1)

**Should address:**
2. Document or remove `_h_e` unused hypothesis (Issue #2)
3. Add changelog / docstring note about `h_deg` addition in `decoder_dist_impl_mem` (Issue #3)
4. Document `[Fintype F]` constraint addition (Issue #4)

**Nice to have:**
5. Remove dead `let _r := r; let _D := D` bindings (Issue #5)
6. Add note to `isWitnessC` docstring about r > 1 incompleteness (Issue #6)
7. Apply minor golfing to theorem proofs at lines 285, 301

---

### Tooling Notes

- **lean4-skills** (`sorry_analyzer.py`, `find_golfable.py`, `analyze_let_usage.py`):
  installed from [cameronfreer/lean4-skills](https://github.com/cameronfreer/lean4-skills)
- **lean-lsp-mcp** registered as MCP server (available in subsequent sessions):
  `claude mcp add lean-lsp uvx lean-lsp-mcp -e LEAN_PROJECT_PATH=/home/user/ArkLib`
- **Lean 4.28.0** installed via elan from `lean-toolchain`
- **Build**: `lake exe cache get` (8010 pre-compiled Mathlib artifacts) + `lake build`
