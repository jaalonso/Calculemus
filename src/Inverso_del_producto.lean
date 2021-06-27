-- Inverso_del_producto.lean
-- Inverso del producto
-- José A. Alonso Jiménez
-- Sevilla, 6 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea G un grupo y a, b ∈ G. Entonces,
--    (a * b)⁻¹ = b⁻¹ * a⁻¹
-- ---------------------------------------------------------------------

import algebra.group.basic

universe  u
variables {G : Type u} [group G]
variables {a b : G}

-- 1ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply inv_eq_of_mul_eq_one,
  calc a * b * (b⁻¹ * a⁻¹)
       = ((a * b) * b⁻¹) * a⁻¹ : (mul_assoc _ _ _).symm
   ... = (a * (b * b⁻¹)) * a⁻¹ : congr_arg (* a⁻¹) (mul_assoc a _ _)
   ... = (a * 1) * a⁻¹         : congr_arg2 _ (congr_arg _ (mul_inv_self b)) rfl
   ... = a * a⁻¹               : congr_arg (* a⁻¹) (mul_one a)
   ... = 1                     : mul_inv_self a
end

-- 2ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply inv_eq_of_mul_eq_one,
  calc a * b * (b⁻¹ * a⁻¹)
       = ((a * b) * b⁻¹) * a⁻¹ : by simp only [mul_assoc]
   ... = (a * (b * b⁻¹)) * a⁻¹ : by simp only [mul_assoc]
   ... = (a * 1) * a⁻¹         : by simp only [mul_inv_self]
   ... = a * a⁻¹               : by simp only [mul_one]
   ... = 1                     : by simp only [mul_inv_self]
end

-- 3ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply inv_eq_of_mul_eq_one,
  calc a * b * (b⁻¹ * a⁻¹)
       = ((a * b) * b⁻¹) * a⁻¹ : by simp [mul_assoc]
   ... = (a * (b * b⁻¹)) * a⁻¹ : by simp
   ... = (a * 1) * a⁻¹         : by simp
   ... = a * a⁻¹               : by simp
   ... = 1                     : by simp,
end

-- 4ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
mul_inv_rev a b

-- 5ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by simp

-- Referencia
-- ==========

-- Propiedad 3.19 del libro "Abstract algebra: Theory and applications"
-- de Thomas W. Judson.
-- http://abstract.ups.edu/download/aata-20200730.pdf#page=49
