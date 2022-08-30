-- Opuesto_de_cero.lean
-- Si R es un anillo, entonces -0 = 0.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-agosto-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo, entonces
--    -0 = 0
-- ----------------------------------------------------------------------

import algebra.ring

variables {R : Type*} [ring R]

-- 1ª demostración
-- ===============

example : (-0 : R) = 0 :=
begin
  have h : 0 - 0 = (-0 : R) := zero_sub 0,
  calc (-0 : R)
       = 0 - 0    : h.symm
   ... = -(0 - 0) : (neg_sub (0 : R) 0).symm
   ... = -(-0)    : congr_arg (λ x, -x) h
   ... = 0        : neg_neg 0
end

-- 2ª demostración
-- ===============

example : (-0 : R) = 0 :=
begin
  have h : 0 - 0 = (-0 : R) := by rw zero_sub,
  calc (-0 : R)
       = 0 - 0    : by rw h
   ... = -(0 - 0) : by rw neg_sub
   ... = -(-0)    : by {congr; rw h}
   ... = 0        : by rw neg_neg
end

-- 3ª demostración
-- ===============

example : (-0 : R) = 0 :=
by simpa only [zero_sub, neg_neg] using (neg_sub (0 : R) 0).symm

-- 4ª demostración
-- ===============

example : (-0 : R) = 0 :=
neg_zero

-- 5ª demostración
-- ===============

example : (-0 : R) = 0 :=
by simp

-- 6ª demostración
-- ===============

example : (-0 : R) = 0 :=
begin
  apply neg_eq_of_add_eq_zero_right,
  rw add_zero,
end

-- 7ª demostración
-- ===============

example : (-0 : R) = 0 :=
neg_eq_of_add_eq_zero_right (add_zero 0)
