import NumericSequences.Basic

-- Teorema: Limite Zero Vezes Sequência Limitada

-- Se x_n → 0 e (y_n) é limitada em módulo, então x_n * y_n → 0.

theorem limite_zero_vezes_limitada {x y : Sequencia}
  (hx : limite_sequencia x 0) (hy : limitada_em_modulo y) :
  limite_sequencia (fun n => x n * y n) 0 := by
  -- Como (y_n) é limitada, existe C > 0 tal que |y_n| ≤ C para todo n
  rcases hy with ⟨C, hC_pos, hC⟩
  -- Seja ε > 0
  intro ε h_eps
  -- Para aplicar a definição de limite de x_n, ajustamos a tolerância para ε / C
  have h_eps_div_C : ε / C > 0 := div_pos h_eps hC_pos
  -- Como x_n → 0, existe N ∈ ℕ tal que n ≥ N ⇒ |x_n| < ε / C
  rcases hx (ε / C) h_eps_div_C with ⟨N, hN⟩
  -- Usamos este mesmo N para a demonstração final
  use N
  intro n hn
  -- Extraindo e isolando a desigualdade |x_n| < ε / C
  have h_x_dist := hN n hn
  have h_x_abs : |x n| < ε / C := by
    calc
      |x n| = |x n - 0| := congrArg abs (by ring)
      _ < ε / C := h_x_dist
  -- Logo, para todo n ≥ N, temos |x_n||y_n| < (ε/C) * C = ε
  -- Encadeamento das manipulações algébricas:
  calc
    |x n * y n - 0| = |x n * y n| := congrArg abs (by ring)
    _ = |x n| * |y n| := abs_mul (x n) (y n)
    _ ≤ |x n| * C := mul_le_mul_of_nonneg_left (hC n) (abs_nonneg (x n))
    _ < (ε / C) * C := mul_lt_mul_of_pos_right h_x_abs hC_pos
    _ = ε := div_mul_cancel₀ ε (ne_of_gt hC_pos)
