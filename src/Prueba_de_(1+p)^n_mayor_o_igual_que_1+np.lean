-- Prueba_de_(1+p)^n_mayor_o_igual_que_1+np.lean
-- Prueba de (1+p)ⁿ ≥ 1+np
-- José A. Alonso Jiménez
-- Sevilla, 23 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean p ∈ ℝ y n ∈ ℕ tales que p > -1. Demostrar que
--    (1 + p)^n ≥ 1 + n*p
-- ---------------------------------------------------------------------

import data.real.basic
open nat

variable (p : ℝ)
variable (n : ℕ)

set_option pp.structure_projections false

example
  (h : p > -1)
  : (1 + p)^n ≥ 1 + n*p :=
begin
  induction n with n HI,
  { simp, },
  { have h1 : 1 + p > 0 := iff.mp neg_lt_iff_pos_add' h,
    have h2 : p*p ≥ 0 := mul_self_nonneg p,
    replace h2 : ↑n*(p*p) ≥ 0 := mul_nonneg (cast_nonneg n) h2,
    calc (1 + p)^succ n
         = (1 + p)^n * (1 + p)
             : pow_succ' (1 + p) n
     ... ≥ (1 + n * p) * (1 + p)
             : (mul_le_mul_right h1).mpr HI
     ... = (1 + p + n*p) + n*(p*p)
             : by ring !
     ... ≥ 1 + p + n*p
             : le_add_of_nonneg_right h2
     ... = 1 + (n + 1) * p
             : by ring !
     ... = 1 + ↑(succ n) * p
             : by norm_num },
end
