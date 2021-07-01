-- Potencias_de_potencias_en_monoides.lean
-- Potencias de potencias en monoides
-- José A. Alonso Jiménez
-- Sevilla, 9 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En los [monoides](https://en.wikipedia.org/wiki/Monoid) se define la
-- potencia con exponentes naturales. En Lean la potencia x^n se
-- se caracteriza por los siguientes lemas:
--    pow_zero : x^0 = 1
--    pow_succ' : x^(succ n) = x * x^n
--
-- Demostrar que si M, a ∈ M y m, n ∈ ℕ, entonces
--    a^(m * n) = (a^m)^n
--
-- Indicación: Se puede usar el lema
--    pow_add : a^(m + n) = a^m * a^n
-- ---------------------------------------------------------------------

import algebra.group_power.basic
open monoid nat

variables {M : Type} [monoid M]
variable  a : M
variables (m n : ℕ)

-- Para que no use la notación con puntos
set_option pp.structure_projections false

-- 1ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
begin
  induction n with n HI,
  { calc a^(m * 0)
         = a^0             : congr_arg ((^) a) (nat.mul_zero m)
     ... = 1               : pow_zero a
     ... = (a^m)^0         : (pow_zero (a^m)).symm },
  { calc a^(m * succ n)
         = a^(m * n + m)   : congr_arg ((^) a) (nat.mul_succ m n)
     ... = a^(m * n) * a^m : pow_add a (m * n) m
     ... = (a^m)^n * a^m   : congr_arg (* a^m) HI
     ... = (a^m)^(succ n)  : (pow_succ' (a^m) n).symm },
end

-- 2ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
begin
  induction n with n HI,
  { calc a^(m * 0)
         = a^0             : by simp only [nat.mul_zero]
     ... = 1               : by simp only [pow_zero]
     ... = (a^m)^0         : by simp only [pow_zero] },
  { calc a^(m * succ n)
         = a^(m * n + m)   : by simp only [nat.mul_succ]
     ... = a^(m * n) * a^m : by simp only [pow_add]
     ... = (a^m)^n * a^m   : by simp only [HI]
     ... = (a^m)^succ n    : by simp only [pow_succ'] },
end

-- 3ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
begin
  induction n with n HI,
  { calc a^(m * 0)
         = a^0             : by simp [nat.mul_zero]
     ... = 1               : by simp
     ... = (a^m)^0         : by simp },
  { calc a^(m * succ n)
         = a^(m * n + m)   : by simp [nat.mul_succ]
     ... = a^(m * n) * a^m : by simp [pow_add]
     ... = (a^m)^n * a^m   : by simp [HI]
     ... = (a^m)^succ n    : by simp [pow_succ'] },
end

-- 4ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
begin
  induction n with n HI,
  { by simp [nat.mul_zero] },
  { by simp [nat.mul_succ,
             pow_add,
             HI,
             pow_succ'] },
end

-- 5ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
begin
  induction n with n HI,
  { rw nat.mul_zero,
    rw pow_zero,
    rw pow_zero, },
  { rw nat.mul_succ,
    rw pow_add,
    rw HI,
    rw pow_succ', }
end

-- 6ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
begin
  induction n with n HI,
  { rw [nat.mul_zero, pow_zero, pow_zero] },
  { rw [nat.mul_succ, pow_add, HI, pow_succ'] }
end

-- 7ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
pow_mul a m n
