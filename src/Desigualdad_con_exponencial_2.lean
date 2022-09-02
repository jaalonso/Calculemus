-- Desigualdad_con_exponencial_2.lean
-- Si a, b, c, d ∈ ℝ tales que a ≤ b y c < d, entonces a + eᶜ + f < b + eᵈ + f
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 22-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si
--    a ≤ b
--    c < d
-- entonces
--    a + exp c + f < b + exp d + f
-- ----------------------------------------------------------------------

import analysis.special_functions.log.basic
open real
variables a b c d f : ℝ

-- 1ª demostración
-- ===============

example
  (hab : a ≤ b)
  (hcd : c < d)
  : a + exp c + f < b + exp d + f :=
begin
  apply add_lt_add_of_lt_of_le,
  { apply add_lt_add_of_le_of_lt,
    { exact hab, },
    { apply exp_lt_exp.mpr,
      exact hcd, }},
  { apply le_refl, },
end

-- 3ª demostración
-- ===============

example
  (hab : a ≤ b)
  (hcd : c < d)
  : a + exp c + f < b + exp d + f :=
begin
  apply add_lt_add_of_lt_of_le,
  { apply add_lt_add_of_le_of_lt hab (exp_lt_exp.mpr hcd), },
  { refl, },
end

-- 4ª demostración
-- ===============

example
  (hab : a ≤ b)
  (hcd : c < d)
  : a + exp c + f < b + exp d + f :=
add_lt_add_of_lt_of_le
  (add_lt_add_of_le_of_lt hab (exp_lt_exp.mpr hcd))
  (le_refl f)

-- 5ª demostración
-- ===============

example
  (hab : a ≤ b)
  (hcd : c < d)
  : a + exp c + f < b + exp d + f :=
by linarith [exp_lt_exp.mpr hcd]
