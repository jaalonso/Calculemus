-- Las_funciones_de_extraccion_no_estan_acotadas.lean
-- Las funciones de extracción no están acotadas
-- José A. Alonso Jiménez
-- Sevilla, 30 de agosto de 2021
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
--
-- Demostrar que las funciones de extracción no está acotadas; es decir,
-- que si φ es una función de extracción, entonces
--     ∀ N N', ∃ n ≥ N', φ n ≥ N
-- ---------------------------------------------------------------------

import tactic
open nat

variable {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ) :=
  ∀ n m, n < m → φ n < φ m

lemma aux
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

-- 1ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros N N',
  let n := max N N',
  use n,
  split,
  { exact le_max_right N N', },
  { calc N ≤ n   : le_max_left N N'
       ... ≤ φ n : aux h n, },
end

-- 2ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros N N',
  let n := max N N',
  use n,
  split,
  { exact le_max_right N N', },
  { exact le_trans (le_max_left N N')
                   (aux h n), },
end

-- 3ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros N N',
  use max N N',
  split,
  { exact le_max_right N N', },
  { exact le_trans (le_max_left N N')
                   (aux h (max N N')), },
end

-- 4ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros N N',
  use max N N',
  exact ⟨le_max_right N N',
         le_trans (le_max_left N N')
                  (aux h (max N N'))⟩,
end

-- 5ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
λ N N',
  ⟨max N N', ⟨le_max_right N N',
              le_trans (le_max_left N N')
                       (aux h (max N N'))⟩⟩

-- 6ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
let n := max N N' in
have h1 : n ≥ N',
  from le_max_right N N',
show ∃ n ≥ N', φ n ≥ N, from
exists.intro n
  (exists.intro h1
    (show φ n ≥ N, from
       calc N ≤ n   : le_max_left N N'
          ... ≤ φ n : aux h n))

-- 7ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
let n := max N N' in
have h1 : n ≥ N',
  from le_max_right N N',
show ∃ n ≥ N', φ n ≥ N, from
⟨n, h1, calc N ≤ n   : le_max_left N N'
          ...  ≤ φ n : aux h n⟩

-- 8ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
let n := max N N' in
have h1 : n ≥ N',
  from le_max_right N N',
show ∃ n ≥ N', φ n ≥ N, from
⟨n, h1, le_trans (le_max_left N N')
                 (aux h (max N N'))⟩

-- 9ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
let n := max N N' in
have h1 : n ≥ N',
  from le_max_right N N',
⟨n, h1, le_trans (le_max_left N N')
                 (aux h n)⟩

-- 10ª demostración
example
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
assume N N',
⟨max N N', le_max_right N N',
           le_trans (le_max_left N N')
                    (aux h (max N N'))⟩

-- 11ª demostración
lemma extraccion_mye
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
λ N N',
  ⟨max N N', le_max_right N N',
             le_trans (le_max_left N N')
             (aux h (max N N'))⟩
