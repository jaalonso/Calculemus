-- Producto_de_potencias_de_la_misma_base_en_monoides.lean
-- Producto_de_potencias_de_la_misma_base_en_monoides
-- José A. Alonso Jiménez
-- Sevilla, 30 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En los [monoides](https://en.wikipedia.org/wiki/Monoid) se define la
-- potencia con exponentes naturales. En Lean la potencia x^n se
-- se caracteriza por los siguientes lemas:
--    pow_zero : x^0 = 1
--    pow_succ : x^(succ n) = x * x^n
--
-- Demostrar que
--    x^(m + n) = x^m * x^n
-- ---------------------------------------------------------------------

import algebra.group_power.basic
open monoid nat

variables {M : Type} [monoid M]
variable  x : M
variables (m n : ℕ)

-- Para que no use la notación con puntos
set_option pp.structure_projections false

-- 1ª demostración
-- ===============

example :
  x^(m + n) = x^m * x^n :=
begin
  induction m with m HI,
  { calc x^(0 + n)
         = x^n             : congr_arg ((^) x) (nat.zero_add n)
     ... = 1 * x^n         : (monoid.one_mul (x^n)).symm
     ... = x^0 * x^n       : congr_arg (* (x^n)) (pow_zero x).symm, },
  { calc x^(succ m + n)
         = x^succ (m + n)  : congr_arg ((^) x) (succ_add m n)
     ... = x * x^(m + n)   : pow_succ x (m + n)
     ... = x * (x^m * x^n) : congr_arg ((*) x) HI
     ... = (x * x^m) * x^n : (monoid.mul_assoc x (x^m) (x^n)).symm
     ... = x^succ m * x^n  : congr_arg (* x^n) (pow_succ x m).symm, },
end

-- 2ª demostración
-- ===============

example :
  x^(m + n) = x^m * x^n :=
begin
  induction m with m HI,
  { calc x^(0 + n)
         = x^n             : by simp only [nat.zero_add]
     ... = 1 * x^n         : by simp only [monoid.one_mul]
     ... = x^0 * x^n       : by simp [pow_zero] },
  { calc x^(succ m + n)
         = x^succ (m + n)  : by simp only [succ_add]
     ... = x * x^(m + n)   : by simp only [pow_succ]
     ... = x * (x^m * x^n) : by simp only [HI]
     ... = (x * x^m) * x^n : (monoid.mul_assoc x (x^m) (x^n)).symm
     ... = x^succ m * x^n  : by simp only [pow_succ], },
end

-- 3ª demostración
-- ===============

example :
  x^(m + n) = x^m * x^n :=
begin
  induction m with m HI,
  { calc x^(0 + n)
         = x^n             : by simp [nat.zero_add]
     ... = 1 * x^n         : by simp
     ... = x^0 * x^n       : by simp, },
  { calc x^(succ m + n)
         = x^succ (m + n)  : by simp [succ_add]
     ... = x * x^(m + n)   : by simp [pow_succ]
     ... = x * (x^m * x^n) : by simp [HI]
     ... = (x * x^m) * x^n : (monoid.mul_assoc x (x^m) (x^n)).symm
     ... = x^succ m * x^n  : by simp [pow_succ], },
end

-- 4ª demostración
-- ===============

example :
  x^(m + n) = x^m * x^n :=
begin
  induction m with m HI,
  { show x^(0 + n) = x^0 * x^n,
      by simp [nat.zero_add] },
  { show x^(succ m + n) = x^succ m * x^n,
      by finish [succ_add,
                 HI,
                 monoid.mul_assoc,
                 pow_succ], },
end

-- 5ª demostración
-- ===============

example :
  x^(m + n) = x^m * x^n :=
pow_add x m n
