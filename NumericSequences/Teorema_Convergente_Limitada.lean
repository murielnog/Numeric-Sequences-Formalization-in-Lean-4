import NumericSequences.Basic

-- Teorema: Toda Sequência Convergente é Limitada

-- Se x_n → L, então (x_n) é limitada em módulo.

theorem convergente_limitada {x : Sequencia} {L : ℝ}
  (h_conv : limite_sequencia x L) : sequencia_limitada x := by
  -- Tomemos ε = 1
  have h_eps : (1 : ℝ) > 0 := by norm_num
  -- Pela definição de limite, existe N ∈ ℕ tal que n ≥ N ⇒ |x_n - L| < 1
  rcases h_conv 1 h_eps with ⟨N, hN⟩
  -- n ≥ N implica L - 1 < x_n < L + 1, portanto |x_n| < |L| + 1
  have h_cauda : ∀ n ≥ N, |x n| < |L| + 1 := by
    intro n hn
    have h_dist := hN n hn
    have h_abs := abs_lt.mp h_dist
    rw [abs_lt]
    constructor
    · linarith [neg_abs_le L]
    · linarith [le_abs_self L]
  -- Os primeiros N termos possuem mínimo c e máximo d
  rcases minimo_maximo_finito x N with ⟨c, d, h_finito⟩
  -- Para os termos iniciais: |x_n| ≤ max |c| |d|
  -- Usamos abs_le para decompor e by_cases no sinal de x_n
  have h_ini : ∀ n < N, |x n| ≤ max |c| |d| := by
    intro n hn
    have hc := (h_finito n hn).left
    have hd := (h_finito n hn).right
    -- |x_n| ≤ max |c| |d| segue de c ≤ x_n ≤ d
    rw [abs_le]
    constructor
    · -- -max|c||d| ≤ x_n: basta mostrar -|c| ≤ x_n
      have h1 : -|c| ≤ c := neg_abs_le c
      have h2 : -(max |c| |d|) ≤ -|c| := by
        linarith [le_max_left |c| |d|]
      linarith
    · -- x_n ≤ max|c||d|: basta mostrar x_n ≤ d ≤ |d|
      have h1 : d ≤ |d| := le_abs_self d
      have h2 : |d| ≤ max |c| |d| := le_max_right _ _
      linarith
  -- Definimos K = max (max |c| |d|) (|L| + 1) como cota global
  use max (max |c| |d|) (|L| + 1)
  constructor
  · -- K > 0
    have : |L| + 1 > 0 := by linarith [abs_nonneg L]
    linarith [le_max_right (max |c| |d|) (|L| + 1)]
  · intro n
    by_cases h : n < N
    · -- Caso n < N: |x_n| ≤ max |c| |d| ≤ K
      exact le_trans (h_ini n h) (le_max_left _ _)
    · -- Caso n ≥ N: |x_n| < |L| + 1 ≤ K
      have h_ge : n ≥ N := by omega
      exact le_trans (le_of_lt (h_cauda n h_ge)) (le_max_right _ _)
