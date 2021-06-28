-- Inverso_del_inverso_en_grupos.lean
-- Inverso del inverso en grupos
-- José A. Alonso Jiménez
-- Sevilla, 7 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea G un grupo y a ∈ G. Demostrar que
--    (a⁻¹)⁻¹ = a
-- ---------------------------------------------------------------------

import algebra.group.basic

universe  u
variables {G : Type u} [group G]
variables {a b : G}

-- ?ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
calc (a⁻¹)⁻¹
     = (a⁻¹)⁻¹ * 1         : (mul_one (a⁻¹)⁻¹).symm
 ... = (a⁻¹)⁻¹ * (a⁻¹ * a) : congr_arg ((*) (a⁻¹)⁻¹) (inv_mul_self a).symm
 ... = ((a⁻¹)⁻¹ * a⁻¹) * a : (mul_assoc _ _ _).symm
 ... = 1 * a               : congr_arg (* a) (inv_mul_self a⁻¹)
 ... = a                   : one_mul a

-- ?ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
calc (a⁻¹)⁻¹
     = (a⁻¹)⁻¹ * 1         : by simp only [mul_one]
 ... = (a⁻¹)⁻¹ * (a⁻¹ * a) : by simp only [inv_mul_self]
 ... = ((a⁻¹)⁻¹ * a⁻¹) * a : by simp only [mul_assoc]
 ... = 1 * a               : by simp only [inv_mul_self]
 ... = a                   : by simp only [one_mul]

-- ?ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
calc (a⁻¹)⁻¹
     = (a⁻¹)⁻¹ * 1         : by simp
 ... = (a⁻¹)⁻¹ * (a⁻¹ * a) : by simp
 ... = ((a⁻¹)⁻¹ * a⁻¹) * a : by simp
 ... = 1 * a               : by simp
 ... = a                   : by simp

-- ?ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
begin
  apply inv_eq_of_mul_eq_one,
  exact mul_left_inv a,
end

-- ?ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a :=
inv_eq_of_mul_eq_one (mul_left_inv a)

-- ?ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a:=
inv_inv a

-- ?ª demostración
-- ===============

example : (a⁻¹)⁻¹ = a:=
by simp


-- Referencia
-- ==========

-- Propiedad 3.20 del libro "Abstract algebra: Theory and applications"
-- de Thomas W. Judson.
-- http://abstract.ups.edu/download/aata-20200730.pdf#page=49
