-- Relacion_entre_los_indices_de_las_subsucesiones_y_de_la_sucesion.lean
-- Relación entre los índices de las subsucesiones y los de la sucesión
-- José A. Alonso Jiménez
-- Sevilla, 29 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Para extraer una subsucesión se aplica una función de extracción que
-- conserva el orden; por ejemplo, la subsucesión
--    uₒ, u₂, u₄, u₆, ...
-- se ha obtenido con la función de extracción φ tal que φ(n) = 2*n.
--
-- En Lean, se puede definir que φ es una función de extracción por
--    def extraccion (φ : ℕ → ℕ) :=
--      ∀ {n m}, n < m → φ n < φ m
--
-- Demostrar que si φ es una función de extracción, entonces
--    ∀ n, n ≤ φ n
-- ---------------------------------------------------------------------

import tactic
open nat

variable {φ : ℕ → ℕ}

set_option pp.structure_projections false

def extraccion (φ : ℕ → ℕ) :=
  ∀ {n m}, n < m → φ n < φ m

-- 1ª demostración
example :
  extraccion φ → ∀ n, n ≤ φ n :=
begin
  intros h n,
  induction n with m HI,
  { exact nat.zero_le (φ 0), },
  { apply nat.succ_le_of_lt,
    have h1 : m < succ m := lt_add_one m,
    calc m ≤ φ m        : HI
       ... < φ (succ m) : h h1, },
end

-- 2ª demostración
example :
  extraccion φ → ∀ n, n ≤ φ n :=
begin
  intros h n,
  induction n with m HI,
  { exact nat.zero_le (φ 0), },
  { apply nat.succ_le_of_lt,
    calc m ≤ φ m        : HI
       ... < φ (succ m) : h (lt_add_one m), },
end

-- 3ª demostración
example :
  extraccion φ → ∀ n, n ≤ φ n :=
assume h : extraccion φ,
assume n,
nat.rec_on n
  ( show 0 ≤ φ 0,
      from nat.zero_le (φ 0) )
  ( assume m,
    assume HI : m ≤ φ m,
    have h1 : m < succ m,
      from lt_add_one m,
    have h2 : m < φ (succ m), from
      calc m ≤ φ m        : HI
         ... < φ (succ m) : h h1,
    show succ m ≤ φ (succ m),
      from nat.succ_le_of_lt h2)
