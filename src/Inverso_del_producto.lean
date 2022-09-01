-- Inverso_del_producto.lean
-- Si G es un grupo y a, b ∈ G entonces (a * b)⁻¹ = b⁻¹ * a⁻¹
-- José A. Alonso Jiménez
-- Sevilla, 19-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si G un grupo y a, b ∈ G, entonces
--    (a * b)⁻¹ = b⁻¹ * a⁻¹
-- ---------------------------------------------------------------------

import algebra.group
variables {G : Type*} [group G]
variables a b : G

-- 1ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_eq_one_iff_inv_eq.mp,
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
  apply mul_eq_one_iff_inv_eq.mp,
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
  apply mul_eq_one_iff_inv_eq.mp,
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
-- by library_search
mul_inv_rev a b

-- 5ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by simp
