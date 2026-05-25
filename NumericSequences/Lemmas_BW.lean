import NumericSequences.Basic

-- Lemas Auxiliares para o Teorema de Bolzano-Weierstrass

-- Uma função de índices estritamente crescente cresce além de qualquer limite
lemma estritamente_crescente_ge (f : ℕ → ℕ)
    (hf : estritamente_crescente_indices f) (n : ℕ) : f n ≥ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have := hf k (k + 1) (Nat.lt_succ_self k)
    omega

-- Caso 1: Infinitos termos destacados → subsequência decrescente

-- Construção da sequência de índices de termos destacados por recursão.
-- g n = (n+1)-ésimo índice de termo destacado, garantindo g n > g (n-1).
noncomputable def seq_destacada (x : Sequencia)
    (h : ∀ N : ℕ, ∃ m > N, termo_destacado x m) : ℕ → ℕ
  | 0     => (h 0).choose
  | n + 1 => (h (seq_destacada x h n)).choose

-- O índice atual é maior que o anterior
lemma seq_destacada_lt (x : Sequencia) (h : ∀ N : ℕ, ∃ m > N, termo_destacado x m) (n : ℕ) :
    seq_destacada x h n < seq_destacada x h (n + 1) := by
  simp only [seq_destacada]
  exact (h (seq_destacada x h n)).choose_spec.1

-- O índice atual corresponde a um termo destacado
lemma seq_destacada_e_destacado (x : Sequencia) (h : ∀ N : ℕ, ∃ m > N, termo_destacado x m)
    (n : ℕ) : termo_destacado x (seq_destacada x h n) := by
  cases n with
  | zero =>
    simp only [seq_destacada]
    exact (h 0).choose_spec.2
  | succ k =>
    simp only [seq_destacada]
    exact (h (seq_destacada x h k)).choose_spec.2

-- A função de índices é estritamente crescente
lemma seq_destacada_estritamente_crescente (x : Sequencia)
    (h : ∀ N : ℕ, ∃ m > N, termo_destacado x m) :
    estritamente_crescente_indices (seq_destacada x h) := by
  intro a b hab
  induction hab with
  | refl => exact seq_destacada_lt x h a
  | step _ ih => exact Nat.lt_trans ih (seq_destacada_lt x h _)

-- Lema principal do Caso 1
lemma caso_infinitos_destacados (x : Sequencia)
    (h_inf : ∀ N : ℕ, ∃ m > N, termo_destacado x m) :
    ∃ y : Sequencia, e_subsequencia y x ∧ decrescente y := by
  let f := seq_destacada x h_inf
  refine ⟨x ∘ f, ⟨f, seq_destacada_estritamente_crescente x h_inf, rfl⟩, ?_⟩
  intro n m hnm
  simp only [Function.comp]
  have hd : termo_destacado x (f n) := seq_destacada_e_destacado x h_inf n
  have hfnm : f n < f m :=
    seq_destacada_estritamente_crescente x h_inf n m hnm
  exact hd (f m) hfnm

-- Caso 2: Finitos termos destacados → subsequência crescente

-- A partir de N₀ (onde não há mais termos destacados),
-- para todo índice n > N₀ existe m > n com x n < x m.
lemma nao_destacado_tem_maior (x : Sequencia) (N₀ : ℕ)
    (h_fin : ∀ m > N₀, ¬ termo_destacado x m) {n : ℕ} (hn : n > N₀) :
    ∃ m > n, x n < x m := by
  have hnd := h_fin n hn
  simp only [termo_destacado, not_forall, not_le] at hnd
  obtain ⟨k, hkn, hkx⟩ := hnd
  exact ⟨k, hkn, hkx⟩

-- Construção recursiva dos índices da subsequência crescente.
-- O subtipo { k : ℕ // k > N₀ } carrega automaticamente a evidência necessária em cada passo.
noncomputable def seq_crescente_aux (x : Sequencia) (N₀ : ℕ)
    (h_fin : ∀ m > N₀, ¬ termo_destacado x m) : ℕ → { k : ℕ // k > N₀ }
  | 0 =>
      ⟨(nao_destacado_tem_maior x N₀ h_fin (Nat.lt_succ_self N₀)).choose,
       Nat.lt_trans (Nat.lt_succ_self N₀)
         (nao_destacado_tem_maior x N₀ h_fin (Nat.lt_succ_self N₀)).choose_spec.1⟩
  | n + 1 =>
      let prev := seq_crescente_aux x N₀ h_fin n
      ⟨(nao_destacado_tem_maior x N₀ h_fin prev.2).choose,
       Nat.lt_trans prev.2
         (nao_destacado_tem_maior x N₀ h_fin prev.2).choose_spec.1⟩

-- Extrai o índice (sem o subtipo)
noncomputable def seq_crescente (x : Sequencia) (N₀ : ℕ)
    (h_fin : ∀ m > N₀, ¬ termo_destacado x m) (n : ℕ) : ℕ :=
  (seq_crescente_aux x N₀ h_fin n).val

-- O índice sempre é > N₀
lemma seq_crescente_gt_N₀ (x : Sequencia) (N₀ : ℕ)
    (h_fin : ∀ m > N₀, ¬ termo_destacado x m) (n : ℕ) :
    seq_crescente x N₀ h_fin n > N₀ :=
  (seq_crescente_aux x N₀ h_fin n).2

-- O índice atual é estritamente menor que o próximo
lemma seq_crescente_lt (x : Sequencia) (N₀ : ℕ)
    (h_fin : ∀ m > N₀, ¬ termo_destacado x m) (n : ℕ) :
    seq_crescente x N₀ h_fin n < seq_crescente x N₀ h_fin (n + 1) := by
  simp only [seq_crescente, seq_crescente_aux]
  exact (nao_destacado_tem_maior x N₀ h_fin (seq_crescente_aux x N₀ h_fin n).2).choose_spec.1

-- O valor de x é estritamente crescente ao longo dos índices consecutivos
lemma seq_crescente_valor_lt (x : Sequencia) (N₀ : ℕ)
    (h_fin : ∀ m > N₀, ¬ termo_destacado x m) (n : ℕ) :
    x (seq_crescente x N₀ h_fin n) < x (seq_crescente x N₀ h_fin (n + 1)) := by
  simp only [seq_crescente, seq_crescente_aux]
  exact (nao_destacado_tem_maior x N₀ h_fin (seq_crescente_aux x N₀ h_fin n).2).choose_spec.2

-- A função de índices é estritamente crescente
lemma seq_crescente_estritamente_crescente (x : Sequencia) (N₀ : ℕ)
    (h_fin : ∀ m > N₀, ¬ termo_destacado x m) :
    estritamente_crescente_indices (seq_crescente x N₀ h_fin) := by
  intro a b hab
  induction hab with
  | refl => exact seq_crescente_lt x N₀ h_fin a
  | step _ ih => exact Nat.lt_trans ih (seq_crescente_lt x N₀ h_fin _)

-- A subsequência extraída é crescente (não-decrescente)
lemma seq_crescente_subseq_cresc (x : Sequencia) (N₀ : ℕ)
    (h_fin : ∀ m > N₀, ¬ termo_destacado x m) :
    crescente (x ∘ seq_crescente x N₀ h_fin) := by
  intro N n hNn
  simp only [Function.comp]
  induction hNn with
  | refl => exact le_refl _
  | @step m _ ih =>
    exact le_trans ih (le_of_lt (seq_crescente_valor_lt x N₀ h_fin m))

-- Lema principal do Caso 2
lemma caso_finitos_destacados (x : Sequencia)
    (h_fin : ∃ N : ℕ, ∀ m > N, ¬ termo_destacado x m) :
    ∃ y : Sequencia, e_subsequencia y x ∧ crescente y := by
  obtain ⟨N₀, hN₀⟩ := h_fin
  let f := seq_crescente x N₀ hN₀
  exact ⟨x ∘ f,
    ⟨f, seq_crescente_estritamente_crescente x N₀ hN₀, rfl⟩,
    seq_crescente_subseq_cresc x N₀ hN₀⟩
