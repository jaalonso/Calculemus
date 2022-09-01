-- Desigualdad_con_exponencial.lean
-- Si a, b, d ∈ ℝ tales que 1 ≤ a y b ≤ d, entonces 2 + a + eᵇ ≤ 3a + eᵈ
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-septiembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Si a, b, d ∈ ℝ tales que
--    1 ≤ a
--    b ≤ d
-- entonces
--    2 + a + exp b ≤ 3 * a + exp d
--
-- Nota: Se pueden usar los lemas
--    add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d
--    exp_le_exp : exp a ≤ exp b ↔ a ≤ b
-- ----------------------------------------------------------------------

import analysis.special_functions.log.basic
open real
variables a b d : ℝ

-- 1ª demostración
-- ===============

example
  (h  : 1 ≤ a)
  (h' : b ≤ d)
  : 2 + a + exp b ≤ 3 * a + exp d :=
begin
  apply add_le_add,
  { calc 2 + a
         = (1 + 1) + a : by refl
     ... ≤ (1 + a) + a : by simp [h]
     ... ≤ (a + a) + a : by simp [h]
     ... = 3 * a       : by ring },
  { exact exp_le_exp.mpr h', },
end

-- 2ª demostración
-- ===============

example
  (h  : 1 ≤ a)
  (h' : b ≤ d)
  : 2 + a + exp b ≤ 3 * a + exp d :=
by linarith [exp_le_exp.mpr h']
