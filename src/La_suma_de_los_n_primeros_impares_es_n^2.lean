-- La_suma_de_los_n_primeros_impares_es_n^2.lean
-- La suma de los n primeros impares es n^2.
-- José A. Alonso Jiménez
-- Sevilla, 3 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, se puede definir el n-ésimo número primo por
--    def impar (n : ℕ) := 2 * n + 1
-- Además, en la librería finset están definidas las funciones
--    range :: ℕ → finset ℕ
--    sum :: finset α → (α → β) → β
-- tales que
-- + (range n) es el conjunto de los n primeros números naturales. Por
--   ejemplo, el valor de (range 3) es {0, 1, 2}.
-- + (sum A f) es la suma del conjunto obtenido aplicando la función f a
--   los elementos del conjunto finito A. Por ejemplo, el valor de
--   (sum (range 3) impar) es 9.
--
-- Demostrar que la suma de los n primeros números impares es n².
-- ---------------------------------------------------------------------

import data.finset
import tactic.ring
open nat

set_option pp.structure_projections false

variable (n : ℕ)

def impar (n : ℕ) := 2 * n + 1

-- 1ª demostración
example :
  finset.sum (finset.range n) impar = n ^ 2 :=
begin
  induction n with m HI,
  { calc finset.sum (finset.range 0) impar
          = 0
            : by simp
     ...  = 0 ^ 2
            : rfl, },
  { calc finset.sum (finset.range (succ m)) impar
         = finset.sum (finset.range m) impar + impar m
           : finset.sum_range_succ impar m
     ... = m ^ 2 + impar m
           : congr_arg2 (+) HI rfl
     ... = m ^ 2 + 2 * m + 1
           : rfl
     ... = (m + 1) ^ 2
           : by ring_nf
     ... = succ m ^ 2
           : rfl },
end

-- 2ª demostración
example :
  finset.sum (finset.range n) impar = n ^ 2 :=
begin
  induction n with d hd,
  { refl, },
  { rw finset.sum_range_succ,
    rw hd,
    change d ^ 2 + (2 * d + 1) = (d + 1) ^ 2,
    ring_nf, },
end
