-- Dos_por_a_igual_a_mas_a.lean
-- Si R es un anillo y a ∈ R, entonces 2 * a = a + a.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo y a ∈ R, entonces
--    2 * a = a + a
-- ----------------------------------------------------------------------

import algebra.ring

variables {R : Type*} [ring R]
variables a : R

-- 1ª demostración
-- ===============

example : 2 * a = a + a :=
calc
  2 * a = (1 + 1) * a   : congr_fun (congr_arg has_mul.mul one_add_one_eq_two.symm) a
  ...   = 1 * a + 1 * a : add_mul 1 1 a
  ...   = a + 1 * a     : congr_arg (λ x, x + 1 * a) (one_mul a)
  ...   = a + a         : congr_arg (λ x, a + x) (one_mul a)

-- 2ª demostración
-- ===============

example : 2 * a = a + a :=
calc
  2 * a = (1 + 1) * a   : by rw one_add_one_eq_two
  ...   = 1 * a + 1 * a : by rw add_mul
  ...   = a + a         : by rw one_mul

-- 3ª demostración
-- ===============

example : 2 * a = a + a :=
by rw [one_add_one_eq_two.symm, add_mul, one_mul]

-- 4ª demostración
-- ===============

example : 2 * a = a + a :=
calc
  2 * a = (1 + 1)  * a  : rfl
  ...   = 1 * a + 1 * a : by simp [add_mul]
  ...   = a + a         : by simp

-- 5ª demostración
-- ===============

example : 2 * a = a + a :=
-- by library_search
two_mul a
