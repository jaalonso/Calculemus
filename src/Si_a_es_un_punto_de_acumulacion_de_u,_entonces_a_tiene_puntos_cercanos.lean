-- Si_a_es_un_punto_de_acumulacion_de_u,_entonces_a_tiene_puntos_cercanos.lean
-- Si a es un punto de acumulación de u, entonces ∀ε>0, ∀ N, ∃k≥N, |u(k)−a| < ε
-- José A. Alonso Jiménez
-- Sevilla, 31 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Para extraer una subsucesión se aplica una función de extracción que
-- conserva el orden; por ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción φ tal que φ(n) = 2*n.
--
-- En Lean, se puede definir que φ es una función de extracción por
--    def extraccion (φ : ℕ → ℕ) :=
--      ∀ n m, n < m → φ n < φ m
-- También se puede definir que a es un límite de u por
--    def limite (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε
--
-- Los puntos de acumulación de una sucesión son los límites de sus
-- subsucesiones. En Lean se puede definir por
--    def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
--      ∃ φ, extraccion φ ∧ limite (u ∘ φ) a
--
-- Demostrar que si a es un punto de acumulación de u, entonces
--    ∀ ε > 0, ∀ N, ∃ k ≥ N, |u k - a| < ε
-- ---------------------------------------------------------------------

import data.real.basic
open nat

variable  {u : ℕ → ℝ}
variables {a : ℝ}
variable  {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ):=
  ∀ n m, n < m → φ n < φ m

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

-- En la demostración se usarán los siguientes lemas.

lemma aux1
  (h : extraccion φ)
  : ∀ n, n ≤ φ n :=
begin
  intro n,
  induction n with m HI,
  { exact nat.zero_le (φ 0), },
  { apply nat.succ_le_of_lt,
    calc m ≤ φ m        : HI
       ... < φ (succ m) : h m (m+1) (lt_add_one m), },
end

lemma aux2
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
λ N N', ⟨max N N', ⟨le_max_right N N',
                    le_trans (le_max_left N N')
                             (aux1 h (max N N'))⟩⟩

-- 1ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ k ≥ N, |u k - a| < ε :=
begin
  intros ε hε N,
  unfold punto_acumulacion at h,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  unfold limite at hφ2,
  cases hφ2 ε hε with N' hN',
  rcases aux2 hφ1 N N' with ⟨m, hm, hm'⟩,
  clear hφ1 hφ2,
  use φ m,
  split,
  { exact hm', },
  { exact hN' m hm, },
end

-- 2ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
begin
  intros ε hε N,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  cases hφ2 ε hε with N' hN',
  rcases aux2 hφ1 N N' with ⟨m, hm, hm'⟩,
  use φ m,
  exact ⟨hm', hN' m hm⟩,
end

-- 3ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
begin
  intros ε hε N,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  cases hφ2 ε hε with N' hN',
  rcases aux2 hφ1 N N' with ⟨m, hm, hm'⟩,
  exact ⟨φ m, hm', hN' _ hm⟩,
end

-- 4ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
begin
  intros ε hε N,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  cases hφ2 ε hε with N' hN',
  rcases aux2 hφ1 N N' with ⟨m, hm, hm'⟩,
  use φ m ; finish,
end

-- 5ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| < ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from aux2 hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              ( assume hm1 : m ≥ N',
                assume hm2 : φ m ≥ N,
                have h2 : |u (φ m) - a| < ε,
                  from hN' m hm1,
                show ∃ n ≥ N, |u n - a| < ε,
                  from exists.intro (φ m) (exists.intro hm2 h2)))))

-- 6ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| < ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from aux2 hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              ( assume hm1 : m ≥ N',
                assume hm2 : φ m ≥ N,
                have h2 : |u (φ m) - a| < ε,
                  from hN' m hm1,
                show ∃ n ≥ N, |u n - a| < ε,
                  from ⟨φ m, hm2, h2⟩))))

-- 7ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| < ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from aux2 hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              ( assume hm1 : m ≥ N',
                assume hm2 : φ m ≥ N,
                have h2 : |u (φ m) - a| < ε,
                  from hN' m hm1,
                ⟨φ m, hm2, h2⟩))))

-- 8ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| < ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from aux2 hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              ( assume hm1 : m ≥ N',
                assume hm2 : φ m ≥ N,
                ⟨φ m, hm2, hN' m hm1⟩))))

-- 9ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| < ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from aux2 hφ.1 N N',
        exists.elim h1
          ( assume m,
            assume hm : ∃ (H : m ≥ N'), φ m ≥ N,
            exists.elim hm
              (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 10ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| < ε,
        have h1 : ∃ n ≥ N', φ n ≥ N,
          from aux2 hφ.1 N N',
        exists.elim h1
          (λ m hm, exists.elim hm (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 11ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      ( assume N',
        assume hN' : ∀ (n : ℕ), n ≥ N' → |(u ∘ φ) n - a| < ε,
        exists.elim (aux2 hφ.1 N N')
          (λ m hm, exists.elim hm (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 12ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  ( assume φ,
    assume hφ : extraccion φ ∧ limite (u ∘ φ) a,
    exists.elim (hφ.2 ε hε)
      (λ N' hN', exists.elim (aux2 hφ.1 N N')
        (λ m hm, exists.elim hm
          (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 13ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
assume ε,
assume hε : ε > 0,
assume N,
exists.elim h
  (λ φ hφ, exists.elim (hφ.2 ε hε)
    (λ N' hN', exists.elim (aux2 hφ.1 N N')
      (λ m hm, exists.elim hm
        (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))

-- 14ª demostración
example
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
λ ε hε N, exists.elim h
  (λ φ hφ, exists.elim (hφ.2 ε hε)
    (λ N' hN', exists.elim (aux2 hφ.1 N N')
      (λ m hm, exists.elim hm
        (λ hm1 hm2, ⟨φ m, hm2, hN' m hm1⟩))))
