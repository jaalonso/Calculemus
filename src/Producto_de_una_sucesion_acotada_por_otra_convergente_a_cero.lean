-- Producto_de_una_sucesion_acotada_por_otra_convergente_a_cero.lean
-- Producto de una sucesión acotada por otra convergente a cero.
-- José A. Alonso Jiménez
-- Sevilla, 31 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que el producto de una sucesión acotada por una convergente
-- a 0 también converge a 0.
-- ---------------------------------------------------------------------

import data.real.basic
import tactic

variables (u v : ℕ → ℝ)
variable  (a : ℝ)

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (c : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

def acotada (a : ℕ → ℝ) :=
∃ B, ∀ n, |a n| ≤ B

-- 1ª demostración
example
  (hU : acotada u)
  (hV : limite v 0)
  : limite (u*v) 0 :=
begin
  cases hU with B hB,
  have hBnoneg : 0 ≤ B,
    calc 0 ≤ |u 0| : abs_nonneg (u 0)
       ... ≤ B     : hB 0,
  by_cases hB0 : B = 0,
  { subst hB0,
    intros ε hε,
    use 0,
    intros n hn,
    simp_rw [sub_zero] at *,
    calc |(u * v) n|
         = |u n * v n|   : congr_arg abs (pi.mul_apply u v n)
     ... = |u n| * |v n| : abs_mul (u n) (v n)
     ... ≤ 0 * |v n|     : mul_le_mul_of_nonneg_right (hB n) (abs_nonneg (v n))
     ... = 0             : zero_mul (|v n|)
     ... < ε             : hε, },
  { change B ≠ 0 at hB0,
    have hBpos : 0 < B := (ne.le_iff_lt hB0.symm).mp hBnoneg,
    intros ε hε,
    cases hV (ε/B) (div_pos hε hBpos) with N hN,
    use N,
    intros n hn,
    simp_rw [sub_zero] at *,
    calc |(u * v) n|
         = |u n * v n|    : congr_arg abs (pi.mul_apply u v n)
     ... = |u n| * |v n|  : abs_mul (u n) (v n)
     ... ≤ B * |v n|      : mul_le_mul_of_nonneg_right (hB n) (abs_nonneg _)
     ... < B * (ε/B)      : mul_lt_mul_of_pos_left (hN n hn) hBpos
     ... = ε              : mul_div_cancel' ε hB0 },
end

-- 2ª demostración
example
  (hU : acotada u)
  (hV : limite v 0)
  : limite (u*v) 0 :=
begin
  cases hU with B hB,
  have hBnoneg : 0 ≤ B,
    calc 0 ≤ |u 0| : abs_nonneg (u 0)
       ... ≤ B     : hB 0,
  by_cases hB0 : B = 0,
  { subst hB0,
    intros ε hε,
    use 0,
    intros n hn,
    simp_rw [sub_zero] at *,
    calc |(u * v) n|
         = |u n| * |v n| : by finish [abs_mul]
     ... ≤ 0 * |v n|     : mul_le_mul_of_nonneg_right (hB n) (abs_nonneg (v n))
     ... = 0             : by ring
     ... < ε             : hε, },
  { change B ≠ 0 at hB0,
    have hBpos : 0 < B := (ne.le_iff_lt hB0.symm).mp hBnoneg,
    intros ε hε,
    cases hV (ε/B) (div_pos hε hBpos) with N hN,
    use N,
    intros n hn,
    simp_rw [sub_zero] at *,
    calc |(u * v) n|
         = |u n| * |v n|  : by finish [abs_mul]
     ... ≤ B * |v n|      : mul_le_mul_of_nonneg_right (hB n) (abs_nonneg _)
     ... < B * (ε/B)      : by finish
     ... = ε              : mul_div_cancel' ε hB0 },
end
