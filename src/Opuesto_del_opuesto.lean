-- Opuesto_del_opuesto.lean
-- Si R es un anillo y a ∈ R, entonces -(-a) = a.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 9-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo y a ∈ R, entonces
--    -(-a) = a
-- ----------------------------------------------------------------------

import algebra.ring

variables {R : Type*} [ring R]
variable a : R

-- 1ª demostración
-- ===============

example : -(-a) = a :=
begin
  calc -(-a)
       = -(0 - a) : congr_arg (λ x, -x) (zero_sub a).symm
   ... = a - 0    : neg_sub (0 : R) a
   ... = a        : sub_zero a
end

-- 2ª demostración
-- ===============

example : -(-a) = a :=
begin
  calc -(-a)
       = -(0 - a) : by { congr; rw zero_sub}
   ... = a - 0    : by rw neg_sub
   ... = a        : by rw sub_zero
end

-- 3ª demostración
-- ===============

example : -(-a) = a :=
by simpa only [zero_sub, sub_zero] using (neg_sub (0 : R) a)

-- 4ª demostración
-- ===============

example : -(-a) = a :=
neg_neg a

-- 5ª demostración
-- ===============

example : -(-a) = a :=
by simp

-- 6ª demostración
-- ===============

example : -(-a) = a :=
begin
  apply neg_eq_of_add_eq_zero_right,
  rw neg_add_self a,
end

-- 7ª demostración
-- ===============

example : -(-a) = a :=
neg_eq_of_add_eq_zero_right (neg_add_self a)
