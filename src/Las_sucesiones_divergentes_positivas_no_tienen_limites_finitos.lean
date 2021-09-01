-- Las_sucesiones_divergentes_positivas_no_tienen_limites_finitos.lean
-- Las sucesiones divergentes positivas no_tienen límites finitos
-- José A. Alonso Jiménez
-- Sevilla, 5 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    def limite (u: ℕ → ℝ) (a: ℝ) :=
--      ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
-- donde se usa la notación |x| para el valor absoluto de x
--    notation `|`x`|` := abs x
--
-- La sucesión u diverge positivamente cuando, para cada número real A,
-- se puede encontrar un número natural m tal que, para n > m , se tenga
-- u(n) > A. En Lean se puede definir por
--    def diverge_positivamente (u : ℕ → ℝ) :=
--      ∀ A, ∃ m, ∀ n ≥ m, u n > A
--
-- Demostrar que si u diverge positivamente, entonces ningún número real
-- es límite de u.
-- ---------------------------------------------------------------------

import data.real.basic
import tactic

variable  {u : ℕ → ℝ}

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - a| < ε

def diverge_positivamente (u : ℕ → ℝ) :=
  ∀ A, ∃ m, ∀ n ≥ m, u n > A

-- 1ª demostración
example
  (h : diverge_positivamente u)
  : ¬(∃ a, limite u a) :=
begin
  push_neg,
  intros a ha,
  cases ha 1 zero_lt_one with m1 hm1,
  cases h (a+1) with m2 hm2,
  let m := max m1 m2,
  specialize hm1 m (le_max_left _ _),
  specialize hm2 m (le_max_right _ _),
  replace hm1 : u m - a < 1 := lt_of_abs_lt hm1,
  replace hm2 : 1 < u m - a := lt_sub_iff_add_lt'.mpr hm2,
  apply lt_irrefl (u m),
  calc u m < a + 1 : sub_lt_iff_lt_add'.mp hm1
       ... < u m   : lt_sub_iff_add_lt'.mp hm2,
end

-- 2ª demostración
example
  (h : diverge_positivamente u)
  : ¬(∃ a, limite u a) :=
begin
  push_neg,
  intros a ha,
  cases ha 1 (by linarith) with m1 hm1,
  cases h (a+1) with m2 hm2,
  let m := max m1 m2,
  replace hm1 : |u m - a| < 1 := by finish,
  replace hm1 : u m - a < 1   := lt_of_abs_lt hm1,
  replace hm2 : u m > a + 1   := by finish,
  replace hm2 : 1 < u m - a   := lt_sub_iff_add_lt'.mpr hm2,
  apply lt_irrefl (u m),
  calc u m < a + 1 : by linarith
       ... < u m   : by linarith
end

-- 3ª demostración
example
  (h : diverge_positivamente u)
  : ¬(∃ a, limite u a) :=
begin
  push_neg,
  intros a ha,
  cases ha 1 (by linarith) with m1 hm1,
  cases h (a+1) with m2 hm2,
  let m := max m1 m2,
  specialize hm1 m (le_max_left _ _),
  specialize hm2 m (le_max_right _ _),
  rw abs_lt at hm1,
  linarith,
end
