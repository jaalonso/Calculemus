-- Unicidad_de_inversos_en_monoides.lean
-- Unicidad de inversos en monoides
-- José A. Alonso Jiménez
-- Sevilla, 2 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que en los monoides conmutativos, si un elemento tiene un
-- inverso por la derecha, dicho inverso es único.
-- ---------------------------------------------------------------------

import algebra.group.basic

variables {M : Type} [comm_monoid M]
variables {x y z : M}

-- 1ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
calc y = 1 * y       : (one_mul y).symm
   ... = (x * z) * y : congr_arg (* y) hz.symm
   ... = (z * x) * y : congr_arg (* y) (mul_comm x z)
   ... = z * (x * y) : mul_assoc z x y
   ... = z * 1       : congr_arg ((*) z) hy
   ... = z           : mul_one z

-- 2ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
calc y = 1 * y       : by simp only [one_mul]
   ... = (x * z) * y : by simp only [hz]
   ... = (z * x) * y : by simp only [mul_comm]
   ... = z * (x * y) : by simp only [mul_assoc]
   ... = z * 1       : by simp only [hy]
   ... = z           : by simp only [mul_one]

-- 3ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
calc y = 1 * y       : by simp
   ... = (x * z) * y : by simp [hz]
   ... = (z * x) * y : by simp [mul_comm]
   ... = z * (x * y) : by simp [mul_assoc]
   ... = z * 1       : by simp [hy]
   ... = z           : by simp

-- 4ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
begin
  apply left_inv_eq_right_inv _ hz,
  rw mul_comm,
  exact hy,
end

-- 5ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
left_inv_eq_right_inv (trans (mul_comm _ _) hy) hz

-- 6ª demostración
-- ===============

example
  (hy : x * y = 1)
  (hz : x * z = 1)
  : y = z :=
inv_unique hy hz
