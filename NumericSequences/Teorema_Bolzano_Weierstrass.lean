import NumericSequences.Basic
import NumericSequences.Lemmas_BW

-- Teorema de Bolzano-Weierstrass

-- Toda sequência limitada possui uma subsequência convergente.

-- Assumimos os teoremas já provados: sequência monótona limitada converge
axiom monotona_limitada_convergente_cresc (x : Sequencia) :
  crescente x → sequencia_limitada x → ∃ L, limite_sequencia x L

axiom monotona_limitada_convergente_decr (x : Sequencia) :
  decrescente x → sequencia_limitada x → ∃ L, limite_sequencia x L

-- Os lemas auxiliares estão provados em NumericSequences.Lemmas_BW:
--   caso_infinitos_destacados : infinitos termos destacados → subsequência decrescente
--   caso_finitos_destacados   : finitos termos destacados  → subsequência crescente

-- TEOREMA DE BOLZANO-WEIERSTRASS
theorem bolzano_weierstrass (x : Sequencia) (h_lim : sequencia_limitada x) :
  ∃ y : Sequencia, e_subsequencia y x ∧ ∃ L : ℝ, limite_sequencia y L := by
  -- A partir da definição de termos destacados podem ocorrer dois casos
  by_cases h_casos : ∀ N : ℕ, ∃ m > N, termo_destacado x m
  · -- Primeiro caso: Existem infinitos termos destacados
    rcases caso_infinitos_destacados x h_casos with ⟨y, h_subseq, h_decr⟩
    -- Como a sequência original é limitada, a subsequência 'y' também herda essa limitação
    have h_y_lim : sequencia_limitada y := by
      rcases h_lim with ⟨K, hKpos, hK⟩
      rcases h_subseq with ⟨f, _, hf_eq⟩
      use K, hKpos
      intro n
      rw [hf_eq]
      exact hK (f n)
    -- Pelo teorema das sequências monótonas limitadas, concluímos que ela converge
    have h_conv := monotona_limitada_convergente_decr y h_decr h_y_lim
    exact ⟨y, h_subseq, h_conv⟩
  · -- Segundo caso: Existem apenas finitos termos destacados
    -- Logicamente, negar "para todo N existe m > N destacado" significa
    -- "existe N onde nenhum m > N é destacado"
    have h_finitos : ∃ N : ℕ, ∀ m > N, ¬ termo_destacado x m := by
      push Not at h_casos
      exact h_casos
    rcases caso_finitos_destacados x h_finitos with ⟨y, h_subseq, h_cresc⟩
    -- A subsequência 'y' herda a limitação da sequência original
    have h_y_lim : sequencia_limitada y := by
      rcases h_lim with ⟨K, hKpos, hK⟩
      rcases h_subseq with ⟨f, _, hf_eq⟩
      use K, hKpos
      intro n
      rw [hf_eq]
      exact hK (f n)
    -- Pelo teorema das sequências monótonas limitadas, ela converge
    have h_conv := monotona_limitada_convergente_cresc y h_cresc h_y_lim
    exact ⟨y, h_subseq, h_conv⟩
