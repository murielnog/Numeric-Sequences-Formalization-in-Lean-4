# Numeric Sequences — Formalization in Lean 4

Formalization of classical Real Analysis theorems on numeric sequences, written in [Lean 4](https://lean-lang.org/) with the support of the [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) library.

## Motivation

The proofs formalized here are based on those presented in:

- **Elon Lages Lima** — *Análise Real*, vol. 1, chapter on Sequences of Real Numbers.
- **Elon Lages Lima** — *Um Curso de Análise*, vol. 1, chapter on Numeric Sequences.

The goal is not merely to reproduce the results, but to **make explicit the steps the author omits** as self-evident for an advanced reader. In a Lean formalization, every intermediate step — modulus manipulation, application of the triangle inequality, choice of the correct index, positivity justifications — must be proved explicitly, making the Lean source a complementary, more detailed version of the book's proofs.

## Project Structure

```
NumericSequences/
├── Basic.lean                             -- Core definitions and auxiliary lemmas
├── Teorema_Unicidade_Limite.lean          -- Uniqueness of the limit of a sequence
├── Teorema_Convergente_Limitada.lean      -- Every convergent sequence is bounded
├── Teorema_limitezero_vezes_limitada.lean -- Zero-limit times bounded sequence
├── Teorema_monotona_limitada_convergente.lean -- Monotone bounded sequence converges
├── Lemmas_BW.lean                         -- Auxiliary lemmas for Bolzano-Weierstrass
└── Teorema_Bolzano_Weierstrass.lean       -- Bolzano-Weierstrass theorem
```

## Definitions (`Basic.lean`)

All definitions are built from primitives, without Mathlib shortcuts, in order to stay close to the language used in the books.

| Definition | Description |
|---|---|
| `Sequencia` | A function `ℕ → ℝ` |
| `limite_sequencia a L` | ε-N definition: `∀ ε > 0, ∃ N, ∀ n ≥ N, \|aₙ − L\| < ε` |
| `sequencia_limitada x` | `∃ K > 0, ∀ n, \|xₙ\| ≤ K` |
| `crescente x` | `∀ N ≤ n, xₙ ≥ xₙ` (non-decreasing) |
| `decrescente x` | `∀ n < m, xₘ ≤ xₙ` (non-increasing) |
| `e_supremo x s` | s is an upper bound approachable within any ε > 0 |
| `e_subsequencia y x` | `∃ f` strictly increasing, `y = x ∘ f` |
| `termo_destacado x m` | `∀ n > m, xₙ ≤ xₘ` (peak term) |

## Theorems

### Uniqueness of the Limit

> *If `aₙ → L` and `aₙ → M`, then `L = M`.*

The proof follows the classical argument by contradiction: assuming `L ≠ M`, one takes `ε = |L − M|` and applies the definition of the limit with tolerance `ε/2` for both `L` and `M` simultaneously. The step made explicit that the book omits is the application of the **triangle inequality in the form**
```
|L − M| = |(L − aₙ) + (aₙ − M)| ≤ |aₙ − L| + |aₙ − M|
```
along with the symmetry `|L − aₙ| = |aₙ − L|`, both stated as individual `have` goals before closing the contradiction with `linarith`.

### Every Convergent Sequence is Bounded

> *If `xₙ → L`, then `(xₙ)` is bounded.*

The proof uses `ε = 1` to obtain an index `N` beyond which `|xₙ| < |L| + 1`. For the first `N` terms, the lemma `minimo_maximo_finito` (proved by induction on `N`) guarantees the existence of a finite bound `max |c| |d|`. The global bound is then `K = max (max |c| |d|) (|L| + 1)`.

The step the book treats as obvious that was made explicit: the passage from `c ≤ xₙ ≤ d` to `|xₙ| ≤ max |c| |d|`, which in Lean requires decomposition via `abs_le` and separate handling of the lower and upper sides using `neg_abs_le` and `le_abs_self`.

### Zero-Limit Times Bounded Sequence

> *If `xₙ → 0` and `(yₙ)` is bounded in modulus by `C`, then `xₙ · yₙ → 0`.*

The tolerance passed to the limit definition of `(xₙ)` is `ε/C`, and the chain
```
|xₙ · yₙ| = |xₙ| · |yₙ| ≤ |xₙ| · C < (ε/C) · C = ε
```
is written as an explicit `calc` block, making visible each inequality that the books condense into a single line.

### Monotone Bounded Sequence Converges

> *Every non-decreasing sequence bounded above is convergent.*

The existence of the supremum is postulated via `axiom completude_reais`, representing the **Completeness Axiom of ℝ** (equivalent to the least upper bound property). The proof shows that the supremum `a` is the limit: given `ε > 0`, there exists `N` with `xₙ > a − ε`, and since the sequence is non-decreasing and `a` is an upper bound, `a − ε < xₙ ≤ a` for all `n ≥ N`, which gives `|xₙ − a| < ε`.

### Bolzano-Weierstrass Theorem (`Lemmas_BW.lean` + `Teorema_Bolzano_Weierstrass.lean`)

> *Every bounded sequence has a convergent subsequence.*

This is the most extensive proof. It relies on the notion of a **peak term**: `m` is a peak term of `(xₙ)` if `xₙ ≤ xₘ` for all `n > m`.

The dichotomy is:

**Case 1 — infinitely many peak terms:** the subsequence formed by the peak terms is non-increasing (since each peak term is greater than or equal to all subsequent terms). Since it is also bounded, it converges by the monotone convergence theorem.

**Case 2 — finitely many peak terms:** beyond some index `N₀`, no term is a peak. This means that for every `n > N₀` there exists `m > n` with `xₘ > xₙ`, allowing the construction of a **strictly increasing** subsequence of values. Since it is bounded, it converges.

Steps made explicit relative to the book:

- The **explicit construction of the index functions** `seq_destacada` and `seq_crescente` by structural recursion, with proofs that they are strictly increasing.
- The use of **subtypes `{ k : ℕ // k > N₀ }`** to automatically carry the evidence `k > N₀` through each recursive step in Case 2, avoiding repeated monotonicity proofs.
- The unfolding of the negation `¬ termo_destacado` into the existence of a larger index via `simp only [termo_destacado, not_forall, not_le]`, which the book justifies only verbally.
- The inheritance of boundedness from the original sequence by the subsequence, via decomposition of `e_subsequencia` and rewriting with `hf_eq`.

## Dependencies

- [Lean 4](https://lean-lang.org/) — `v4.29.1`
- [Mathlib4](https://github.com/leanprover-community/mathlib4) — `v4.29.1`

## Building

With [elan](https://github.com/leanprover/elan) and [lake](https://github.com/leanprover/lake) installed:

```bash
lake build
```

## References

- Lima, E. L. *Análise Real*, vol. 1. Rio de Janeiro: IMPA, multiple editions.
- Lima, E. L. *Um Curso de Análise*, vol. 1. Rio de Janeiro: IMPA, multiple editions.
