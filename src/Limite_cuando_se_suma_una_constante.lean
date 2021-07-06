-- Limite_cuando_se_suma_una_constante.lean
-- Límite con suma de constante
-- José A. Alonso Jiménez
-- Sevilla, 13 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- Se define que a es el límite de la sucesión u, por
--    def limite : (ℕ → ℝ) → ℝ → Prop :=
--    λ u a, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
-- donde se usa la notación |x| para el valor absoluto de x
--    notation `|`x`|` := abs x
--
-- Demostrar que si el límite de la sucesión u(i) es a y c ∈ ℝ, entonces
-- el límite de u(i)+c es a+c.
-- ---------------------------------------------------------------------

import data.real.basic
import tactic

variables {u : ℕ → ℝ}
variables {a c : ℝ}

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (h : limite u a)
  : limite (λ i, u i + c) (a + c) :=
begin
  intros ε hε,
  dsimp,
  cases h ε hε with k hk,
  use k,
  intros n hn,
  calc |u n + c - (a + c)|
       = |u n - a|         : by norm_num
   ... < ε                 : hk n hn,
end

-- 2ª demostración
-- ===============

example
  (h : limite u a)
  : limite (λ i, u i + c) (a + c) :=
begin
  intros ε hε,
  dsimp,
  cases h ε hε with k hk,
  use k,
  intros n hn,
  convert hk n hn using 2,
  ring,
end

-- 3ª demostración
-- ===============

example
  (h : limite u a)
  : limite (λ i, u i + c) (a + c) :=
begin
  intros ε hε,
  convert h ε hε,
  by norm_num,
end

-- 4ª demostración
-- ===============

example
  (h : limite u a)
  : limite (λ i, u i + c) (a + c) :=
λ ε hε, (by convert h ε hε; norm_num)
