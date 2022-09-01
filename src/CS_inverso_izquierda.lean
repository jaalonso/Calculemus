-- CS_inverso_izquierda.lean
-- Si G es un grupo y a, b ∈ G tales que b * a = 1, entonces a⁻¹ = b
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que siG es un grupo y a, b ∈ G tales que
--    b * a = 1
-- entonces
--    a⁻¹ = b
-- ----------------------------------------------------------------------

import algebra.group
variables {G : Type*} [group G]
variables a b : G

-- 1ª demostración
-- ===============

example
  (h : b * a = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ =  1 * a⁻¹       : (one_mul a⁻¹).symm
  ... =  (b * a) * a⁻¹ : congr_arg (λ x, x * a⁻¹) h.symm
  ... =  b * (a * a⁻¹) : mul_assoc b a a⁻¹
  ... =  b * 1         : congr_arg (λ x, b * x) (mul_right_inv a)
  ... =  b             : mul_one b

-- 2ª demostración
-- ===============

example
  (h : b * a = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ =  1 * a⁻¹       : by rw one_mul
  ... =  (b * a) * a⁻¹ : by rw h
  ... =  b * (a * a⁻¹) : by rw mul_assoc
  ... =  b * 1         : by rw mul_right_inv
  ... =  b             : by rw mul_one

-- 3ª demostración
-- ===============

example
  (h : b * a = 1)
  : a⁻¹ = b :=
calc
  a⁻¹ =  1 * a⁻¹       : by simp
  ... =  (b * a) * a⁻¹ : by simp [h]
  ... =  b * (a * a⁻¹) : by simp
  ... =  b * 1         : by simp
  ... =  b             : by simp

-- 4ª demostración
-- ===============

example
  (h : b * a = 1)
  : a⁻¹ = b :=
-- by library_search
inv_eq_of_mul_eq_one_left h
