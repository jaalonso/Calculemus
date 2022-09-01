-- Neutro_derecha.lean
-- Si G es un grupo y a ∈ G, entonces a * 1 = a
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si G es un grupo y a ∈ G, entonces
--    a * 1 = a
-- ----------------------------------------------------------------------

import algebra.group
variables {G : Type*} [group G]
variables a : G

-- 1ª demostración
-- ===============

example : a * 1 = a :=
calc
  a * 1 = a * (a⁻¹ * a) : congr_arg (λ x, a * x) (mul_left_inv a).symm
    ... = (a * a⁻¹) * a : (mul_assoc a a⁻¹ a).symm
    ... = 1 * a         : congr_arg (λ x, x* a) (mul_right_inv a)
    ... = a             : one_mul a

-- 2ª demostración
-- ===============

example : a * 1 = a :=
calc
  a * 1 = a * (a⁻¹ * a) : by rw mul_left_inv
    ... = (a * a⁻¹) * a : by rw mul_assoc
    ... = 1 * a         : by rw mul_right_inv
    ... = a             : by rw one_mul

-- 3ª demostración
-- ===============

example : a * 1 = a :=
calc
  a * 1 = a * (a⁻¹ * a) : by simp
    ... = (a * a⁻¹) * a : by simp
    ... = 1 * a         : by simp
    ... = a             : by simp

-- 3ª demostración
-- ===============

example : a * 1 = a :=
by simp

-- 4ª demostración
-- ===============

example : a * 1 = a :=
-- by library_search
mul_one a
