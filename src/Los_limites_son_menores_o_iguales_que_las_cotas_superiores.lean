-- Los_limites_son_menores_o_iguales_que_las_cotas_superiores.lean
-- Los límites son menores o iguales que las cotas superiores
-- José A. Alonso Jiménez
-- Sevilla, 16 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, se puede definir que a es el límite de la sucesión u por
--    def limite (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε
-- y que a es una cota superior de  u por
--    def cota_superior (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ n, u n ≤ a
--
-- Demostrar que si x es el límite de la sucesión u e y es una cota
-- superior de u, entonces x ≤ y.
-- ---------------------------------------------------------------------

import data.real.basic

variable  (u : ℕ → ℝ)
variables (x y : ℝ)

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε

def cota_superior (u : ℕ → ℝ) (a : ℝ) :=
  ∀ n, u n ≤ a

lemma aux :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
begin
  contrapose!,
  intro h,
  use (y-x)/2,
  split ; linarith,
end

-- 1º demostración
example
  (hx : limite u x)
  (hy : cota_superior u y)
  : x ≤ y :=
begin
  apply aux,
  intros ε hε,
  cases hx ε hε with k hk,
  specialize hk k rfl.ge,
  replace hk : -ε < u k - x := neg_lt_of_abs_lt hk,
  replace hk : x < u k + ε := neg_lt_sub_iff_lt_add'.mp hk,
  apply le_of_lt,
  exact lt_add_of_lt_add_right hk (hy k),
end

-- 2º demostración
example
  (hx : limite u x)
  (hy : cota_superior u y)
  : x ≤ y :=
begin
  apply aux,
  intros ε hε,
  cases hx ε hε with k hk,
  specialize hk k rfl.ge,
  apply le_of_lt,
  calc x < u k + ε : neg_lt_sub_iff_lt_add'.mp (neg_lt_of_abs_lt hk)
     ... ≤ y + ε   : add_le_add_right (hy k) ε,
end

-- 3º demostración
example
  (hx : limite u x)
  (hy : cota_superior u y)
  : x ≤ y :=
begin
  apply aux,
  intros ε hε,
  cases hx ε hε with k hk,
  specialize hk k (by linarith),
  rw abs_lt at hk,
  linarith [hy k],
end
