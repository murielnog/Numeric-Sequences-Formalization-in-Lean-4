import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

-- Definições Fundamentais de Sequências Numéricas

-- Uma sequência é uma função dos Naturais para os Reais
def Sequencia := ℕ → ℝ

-- Definição ε-N de limite de uma sequência
def limite_sequencia (a : Sequencia) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

def limitada_superiormente (x : Sequencia) : Prop :=
  ∃ M : ℝ, ∀ n : ℕ, x n ≤ M

def limitada_inferiormente (x : Sequencia) : Prop :=
  ∃ m : ℝ, ∀ n : ℕ, m ≤ x n

-- Sequência limitada: limitada superior e inferiormente (por cotas absolutas)
def sequencia_limitada (x : Sequencia) : Prop :=
  ∃ K > 0, ∀ n : ℕ, |x n| ≤ K

-- Versão alternativa (limitada superior e inferiormente separadamente)
def sequencia_limitada' (x : Sequencia) : Prop :=
  limitada_superiormente x ∧ limitada_inferiormente x

-- Limitação em módulo por uma constante positiva (usada no teorema do produto)
def limitada_em_modulo (a : Sequencia) : Prop :=
  ∃ C > 0, ∀ n : ℕ, |a n| ≤ C

-- Sequência crescente (não-decrescente): para todo N ≤ n, x_N ≤ x_n
def crescente (x : Sequencia) : Prop :=
  ∀ N n : ℕ, N ≤ n → x N ≤ x n

-- Sequência decrescente (não-crescente): para todo n < m, x_m ≤ x_n
def decrescente (x : Sequencia) : Prop :=
  ∀ n m : ℕ, n < m → x m ≤ x n

-- Definição de supremo de uma sequência:
-- s é supremo de {x_n} se:
--   (1) x_n ≤ s para todo n
--   (2) para todo ε > 0, existe N tal que s - ε < x_N
def e_supremo (x : Sequencia) (s : ℝ) : Prop :=
  (∀ n : ℕ, x n ≤ s) ∧
  (∀ ε > 0, ∃ N : ℕ, s - ε < x N)

-- Uma função de índices é estritamente crescente
def estritamente_crescente_indices (f : ℕ → ℕ) : Prop :=
  ∀ n m : ℕ, n < m → f n < f m

-- y é subsequência de x se existe f estritamente crescente com y = x ∘ f
def e_subsequencia (y x : Sequencia) : Prop :=
  ∃ f : ℕ → ℕ, estritamente_crescente_indices f ∧ y = x ∘ f

-- m é um índice de termo destacado (máximo da cauda a partir de m)
def termo_destacado (x : Sequencia) (m : ℕ) : Prop :=
  ∀ n > m, x n ≤ x m

-- Lemas Auxiliares

-- Lema: O conjunto finito dos primeiros N termos de x possui mínimo e máximo.
lemma minimo_maximo_finito (x : Sequencia) (N : ℕ) :
  ∃ c d : ℝ, ∀ n < N, c ≤ x n ∧ x n ≤ d := by
  induction N with
  | zero =>
    use 0, 0
    intro n hn
    contradiction
  | succ k ih =>
    rcases ih with ⟨c', d', h'⟩
    use min c' (x k), max d' (x k)
    intro n hn
    by_cases h : n < k
    · have h_n := h' n h
      exact ⟨le_trans (min_le_left _ _) h_n.1, le_trans h_n.2 (le_max_left _ _)⟩
    · have heq : n = k := by omega
      subst heq
      exact ⟨min_le_right _ _, le_max_right _ _⟩
