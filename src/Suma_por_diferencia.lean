-- Suma_por_diferencia.lean
-- Suma por diferencia.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-agosto-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a y b son números reales, entonces
--    (a + b) * (a - b) = a^2 - b^2
-- ---------------------------------------------------------------------

import data.real.basic

variables a b c d : ℝ

-- 1ª demostración
example : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
      = a * (a - b) + b * (a - b)         : by rw add_mul
  ... = (a * a - a * b) + b * (a - b)     : by rw mul_sub
  ... = (a^2 - a * b) + b * (a - b)       : by rw ← pow_two
  ... = (a^2 - a * b) + (b * a - b * b)   : by rw mul_sub
  ... = (a^2 - a * b) + (b * a - b^2)     : by rw ← pow_two
  ... = (a^2 + -(a * b)) + (b * a - b^2)  : by ring
  ... = a^2 + (-(a * b) + (b * a - b^2))  : by rw add_assoc
  ... = a^2 + (-(a * b) + (b * a + -b^2)) : by ring
  ... = a^2 + ((-(a * b) + b * a) + -b^2) : by rw ← add_assoc
                                               (-(a * b)) (b * a) (-b^2)
  ... = a^2 + ((-(a * b) + a * b) + -b^2) : by rw mul_comm
  ... = a^2 + (0 + -b^2)                  : by rw neg_add_self (a * b)
  ... = (a^2 + 0) + -b^2                  : by rw ← add_assoc
  ... = a^2 + -b^2                        : by rw add_zero
  ... = a^2 - b^2                         : by linarith


-- 2ª demostración
example : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
      = a * (a - b) + b * (a - b)         : by ring
  ... = (a * a - a * b) + b * (a - b)     : by ring
  ... = (a^2 - a * b) + b * (a - b)       : by ring
  ... = (a^2 - a * b) + (b * a - b * b)   : by ring
  ... = (a^2 - a * b) + (b * a - b^2)     : by ring
  ... = (a^2 + -(a * b)) + (b * a - b^2)  : by ring
  ... = a^2 + (-(a * b) + (b * a - b^2))  : by ring
  ... = a^2 + (-(a * b) + (b * a + -b^2)) : by ring
  ... = a^2 + ((-(a * b) + b * a) + -b^2) : by ring
  ... = a^2 + ((-(a * b) + a * b) + -b^2) : by ring
  ... = a^2 + (0 + -b^2)                  : by ring
  ... = (a^2 + 0) + -b^2                  : by ring
  ... = a^2 + -b^2                        : by ring
  ... = a^2 - b^2                         : by ring

-- 3ª demostración
example : (a + b) * (a - b) = a^2 - b^2 :=
by ring
