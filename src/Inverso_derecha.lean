-- Inverso_derecha.lean
-- Si G es un grupo y a ∈ G, entonces a * a⁻¹ = 1
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 14-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, se declara que G es un grupo mediante la expresión
--    variables {G : Type*} [group G]
-- y, como consecuencia, se tiene los siguientes axiomas
--    mul_assoc    : ∀ a b c : G, a * b * c = a * (b * c)
--    one_mul      : ∀ a : G,     1 * a = a
--    mul_left_inv : ∀ a : G,     a⁻¹ * a = 1
--
-- Demostrar que si G es un grupo y a ∈ G, entonces
--    a * a⁻¹ = 1
-- ---------------------------------------------------------------------

import algebra.group
variables {G : Type*} [group G]
variables (a b : G)

-- 1ª demostración
-- ===============

example : a * a⁻¹ = 1 :=
calc a * a⁻¹
     = 1 * (a * a⁻¹)
       : (one_mul (a * a⁻¹)).symm
 ... = (1 * a) * a⁻¹
       : (mul_assoc 1 a  a⁻¹).symm
 ... = (((a⁻¹)⁻¹ * a⁻¹)  * a) * a⁻¹
       : congr_arg (λ x, (x * a) * a⁻¹) (mul_left_inv a⁻¹).symm
 ... = ((a⁻¹)⁻¹ * (a⁻¹  * a)) * a⁻¹
       : congr_fun (congr_arg has_mul.mul (mul_assoc a⁻¹⁻¹ a⁻¹ a)) a⁻¹
 ... = ((a⁻¹)⁻¹ * 1) * a⁻¹
       : congr_arg (λ x, (a⁻¹⁻¹ * x) * a⁻¹) (mul_left_inv a)
 ... = (a⁻¹)⁻¹ * (1 * a⁻¹)
       : mul_assoc (a⁻¹)⁻¹ 1 a⁻¹
 ... = (a⁻¹)⁻¹ * a⁻¹
       : congr_arg (λ x, (a⁻¹)⁻¹ * x) (one_mul a⁻¹)
 ... = 1
       : mul_left_inv a⁻¹

-- 2ª demostración
-- ===============

example : a * a⁻¹ = 1 :=
calc
  a * a⁻¹ = 1 * (a * a⁻¹)                : by rw one_mul
      ... = (1 * a) * a⁻¹                : by rw mul_assoc
      ... = (((a⁻¹)⁻¹ * a⁻¹)  * a) * a⁻¹ : by rw mul_left_inv
      ... = ((a⁻¹)⁻¹ * (a⁻¹  * a)) * a⁻¹ : by rw ← mul_assoc
      ... = ((a⁻¹)⁻¹ * 1) * a⁻¹          : by rw mul_left_inv
      ... = (a⁻¹)⁻¹ * (1 * a⁻¹)          : by rw mul_assoc
      ... = (a⁻¹)⁻¹ * a⁻¹                : by rw one_mul
      ... = 1                            : by rw mul_left_inv

-- 3ª demostración
-- ===============

example : a * a⁻¹ = 1 :=
calc
  a * a⁻¹ = 1 * (a * a⁻¹)                : by simp
      ... = (1 * a) * a⁻¹                : by simp
      ... = (((a⁻¹)⁻¹ * a⁻¹)  * a) * a⁻¹ : by simp
      ... = ((a⁻¹)⁻¹ * (a⁻¹  * a)) * a⁻¹ : by simp
      ... = ((a⁻¹)⁻¹ * 1) * a⁻¹          : by simp
      ... = (a⁻¹)⁻¹ * (1 * a⁻¹)          : by simp
      ... = (a⁻¹)⁻¹ * a⁻¹                : by simp
      ... = 1                            : by simp

-- 4ª demostración
-- ===============

example : a * a⁻¹ = 1 :=
by simp

-- 5ª demostración
-- ===============

example : a * a⁻¹ = 1 :=
-- by library_search
mul_inv_self a
