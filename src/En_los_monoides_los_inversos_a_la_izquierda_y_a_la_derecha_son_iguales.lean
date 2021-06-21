-- En_los_monoides_los_inversos_a_la_izquierda_y_a_la_derecha_son_iguales.lean
-- En los monoides, los inversos a la izquierda y a la derecha son iguales.
-- José A. Alonso Jiménez
-- Sevilla, 29 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Un [monoide](https://en.wikipedia.org/wiki/Monoid) es un conjunto
-- junto con una operación binaria que es asociativa y tiene elemento
-- neutro.
--
-- En Lean, está definida la clase de los monoides (como `monoid`) y sus
-- propiedades características son
--    mul_assoc : (a * b) * c = a * (b * c)
--    one_mul :   1 * a = a
--    mul_one :   a * 1 = a
--
-- Demostrar que si M es un monide, a ∈ M, b es un inverso de a por la
-- izquierda y c es un inverso de a por la derecha, entonce b = c.
-- ---------------------------------------------------------------------

import algebra.group.defs

variables {M : Type} [monoid M]
variables {a b c : M}

-- 1ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
begin
 rw ←one_mul c,
 rw ←hba,
 rw mul_assoc,
 rw hac,
 rw mul_one b,
end

-- 2ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
by rw [←one_mul c, ←hba, mul_assoc, hac, mul_one b]

-- 3ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
calc b   = b * 1       : (mul_one b).symm
     ... = b * (a * c) : congr_arg (λ x, b * x) hac.symm
     ... = (b * a) * c : (mul_assoc b a c).symm
     ... = 1 * c       : congr_arg (λ x, x * c) hba
     ... = c           : one_mul c

-- 4ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
calc b   = b * 1       : by finish
     ... = b * (a * c) : by finish
     ... = (b * a) * c : (mul_assoc b a c).symm
     ... = 1 * c       : by finish
     ... = c           : by finish

-- 5ª demostración
-- ===============

example
  (hba : b * a = 1)
  (hac : a * c = 1)
  : b = c :=
left_inv_eq_right_inv hba hac
