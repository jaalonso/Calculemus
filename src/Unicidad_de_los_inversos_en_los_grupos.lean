-- Unicidad_de_los_inversos_en_los_grupos.lean
-- Unicidad de los inversos en los grupos
-- José A. Alonso Jiménez
-- Sevilla, 5 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a es un elemento de un grupo G, entonces a tiene un
-- único inverso; es decir, si b es un elemento de G tal que a * b = 1,
-- entonces a⁻¹ = b.
-- ---------------------------------------------------------------------

import algebra.group.basic

universe  u
variables {G : Type u} [group G]
variables {a b : G}

-- 1ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * 1       : (mul_one a⁻¹).symm
     ... = a⁻¹ * (a * b) : congr_arg ((*) a⁻¹) h.symm
     ... = (a⁻¹ * a) * b : (mul_assoc a⁻¹ a b).symm
     ... = 1 * b         : congr_arg (* b) (inv_mul_self a)
     ... = b             : one_mul b

-- 2ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * 1       : by simp only [mul_one]
     ... = a⁻¹ * (a * b) : by simp only [h]
     ... = (a⁻¹ * a) * b : by simp only [mul_assoc]
     ... = 1 * b         : by simp only [inv_mul_self]
     ... = b             : by simp only [one_mul]

-- 3ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * 1       : by simp
     ... = a⁻¹ * (a * b) : by simp [h]
     ... = (a⁻¹ * a) * b : by simp
     ... = 1 * b         : by simp
     ... = b             : by simp

-- 4ª demostración
-- ===============

example
  (h : a * b = 1)
  : a⁻¹ = b :=
calc a⁻¹ = a⁻¹ * (a * b) : by simp [h]
     ... = b             : by simp

-- 5ª demostración
-- ===============

example
  (h : b * a = 1)
  : b = a⁻¹ :=
-- by library_search
eq_inv_iff_mul_eq_one.mpr h

-- Referencia
-- ==========

-- Propiedad 3.18 del libro "Abstract algebra: Theory and applications"
-- de Thomas W. Judson.
-- http://abstract.ups.edu/download/aata-20200730.pdf#page=49
