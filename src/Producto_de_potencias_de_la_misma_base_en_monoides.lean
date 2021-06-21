-- Producto_de_potencias_de_la_misma_base_en_monoides.lean
-- Producto_de_potencias_de_la_misma_base_en_monoides
-- José A. Alonso Jiménez
-- Sevilla, 30 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En los [monoides](https://en.wikipedia.org/wiki/Monoid) se define la
-- potencia con exponentes naturales. En Lean la potencia x^n se
-- representa por (npow n x) y se caracteriza por los siguientes lemas:
--    npow_zero' : npow 0 x = 1
--    npow_succ' : npow (succ n) x = x * npow n x
--
-- Demostrar que
--    npow (m + n) x = npow m x * npow n x :=
-- ---------------------------------------------------------------------

import algebra.group.defs

variables {M : Type} [monoid M]
variable  x : M
variables (m n : ℕ)

-- Para que no use la notación con puntos
set_option pp.structure_projections false

-- 1ª demostración
-- ===============

example :
  npow (m + n) x = npow m x * npow n x :=
begin
  induction m with m HI,
  { rw nat.zero_add,
    rw monoid.npow_zero',
    rw monoid.one_mul, },
  { rw nat.succ_add,
    rw monoid.npow_succ',
    rw monoid.npow_succ',
    rw HI,
    rw ← mul_assoc, },
end

-- 2ª demostración
-- ===============

example :
  npow (m + n) x = npow m x * npow n x :=
begin
  induction m with m HI,
  { rw [nat.zero_add, monoid.npow_zero', monoid.one_mul], },
  { rw [nat.succ_add, monoid.npow_succ', monoid.npow_succ', HI, ← mul_assoc] }
end
