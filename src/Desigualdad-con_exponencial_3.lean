-- Desigualdad-con_exponencial_3.lean
-- Si a, b, c ∈ ℝ tales que a ≤ b, entonces c - eᵇ ≤ c - eᵃ
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a, b, c ∈ ℝ tales que a ≤ b, entonces
--    c - eᵇ ≤ c - eᵃ
-- ----------------------------------------------------------------------

import analysis.special_functions.log.basic
import tactic

open real

variables a b c : ℝ

-- 1ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
begin
   apply sub_le_sub_left _ c,
   exact exp_le_exp.mpr h,
end

-- 2ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
sub_le_sub_left (exp_le_exp.mpr h) c

-- 3ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - b ≤ c - a :=
-- by library_search
sub_le_sub_left h c

-- 4ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
by linarith [exp_le_exp.mpr h]

-- 5ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
-- by hint
by finish
