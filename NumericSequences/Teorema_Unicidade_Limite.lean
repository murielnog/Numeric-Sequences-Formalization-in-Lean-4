import NumericSequences.Basic

-- Teorema da Unicidade do Limite

-- Se uma sequência (a_n) converge para L e para M, então L = M.

theorem unicidade_limite {a : Sequencia} {L M : ℝ}
  (hL : limite_sequencia a L) (hM : limite_sequencia a M) : L = M := by
  -- Procedemos por contradição. Suponha L ≠ M
  by_contra h
  -- A distância |L - M| deve ser estritamente maior que 0
  have h_pos : |L - M| > 0 := abs_pos.mpr (sub_ne_zero.mpr h)
  -- Definimos ε como a distância |L - M|
  set ε := |L - M|
  -- Como ε > 0, ε/2 também é > 0
  have h_eps_meio_pos : ε / 2 > 0 := half_pos h_pos
  -- Aplicamos a definição de limite para L e M com tolerância ε/2
  rcases hL (ε / 2) h_eps_meio_pos with ⟨N1, hN1⟩
  rcases hM (ε / 2) h_eps_meio_pos with ⟨N2, hN2⟩
  -- Escolhemos o maior índice para que ambas as condições sejam válidas simultaneamente
  let N := max N1 N2
  have hN_ge_N1 : N ≥ N1 := le_max_left N1 N2
  have hN_ge_N2 : N ≥ N2 := le_max_right N1 N2
  -- Instanciamos as desigualdades para o índice N
  have h_dist_L := hN1 N hN_ge_N1
  have h_dist_M := hN2 N hN_ge_N2
  -- Usamos o "zero esperto" e a desigualdade triangular: |L - M| = |(L - a N) + (a N - M)|
  have h_triangular : |L - M| ≤ |L - a N| + |a N - M| := by
    calc
      |L - M| = |(L - a N) + (a N - M)| := congrArg abs (by ring)
      _ ≤ |L - a N| + |a N - M| := abs_add_le (L - a N) (a N - M)
  -- Convertendo |L - a N| para |a N - L| (propriedade do módulo)
  have h_mod_simetria : |L - a N| = |a N - L| := abs_sub_comm L (a N)
  rw [h_mod_simetria] at h_triangular
  -- Concluímos a contradição: ε ≤ ε/2 + ε/2 = ε, logo ε < ε, o que é falso
  have h_contradicao : |L - M| < ε := by linarith
  -- falsidade logicamente impossível (|L - M| < |L - M|)
  exact lt_irrefl ε h_contradicao
