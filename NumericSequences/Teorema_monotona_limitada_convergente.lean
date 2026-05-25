import NumericSequences.Basic

-- Teorema de Monotonia e Limitação

-- Toda sequência crescente e limitada superiormente é convergente.

-- Postulado: Completude de ℝ — todo conjunto não vazio limitado superiormente possui supremo
axiom completude_reais (x : Sequencia) :
  limitada_superiormente x → ∃ a : ℝ, e_supremo x a

-- Demonstração do Teorema
theorem monotona_limitada_convergente {x : Sequencia}
  (h_cresc : crescente x) (h_lim : limitada_superiormente x) :
  ∃ a : ℝ, limite_sequencia x a := by
  -- Seja a = sup {x_n | n ∈ ℕ}
  rcases completude_reais x h_lim with ⟨a, h_a_sup⟩
  -- Mostraremos que a sequência converge para 'a'
  use a
  intro ε h_eps
  -- Dado ε > 0, o número a - ε não é uma cota superior da sequência.
  -- Logo, existe N ∈ ℕ tal que x_N > a - ε
  have h_sup_prop2 := h_a_sup.right ε h_eps
  rcases h_sup_prop2 with ⟨N, hN⟩
  use N
  intro n hn
  -- Como a sequência é crescente, para todo n ≥ N temos x_N ≤ x_n
  have h_cresc_n : x N ≤ x n := h_cresc N n hn
  -- 'a' é cota superior, pois é o supremo
  have h_cota_n : x n ≤ a := h_a_sup.left n
  -- Portanto: a - ε < x_N ≤ x_n ≤ a < a + ε
  have h_esq : a - ε < x n := by linarith
  have h_dir : x n < a + ε := by linarith
  -- o que mostra que |x_n - a| < ε, i.e., lim x_n = a
  exact abs_lt.mpr ⟨by linarith, by linarith⟩
