-- Limite_de_sucesiones_no_decrecientes.lean
-- Límite de sucesiones no decrecientes
-- José A. Alonso Jiménez
-- Sevilla, 6 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante
-- una función (u : ℕ → ℝ) de forma que u(n) es uₙ.
--
-- En Lean, se define que a es el límite de la sucesión u, por
--    def limite (u: ℕ → ℝ) (a: ℝ) :=
--      ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
-- donde se usa la notación |x| para el valor absoluto de x
--    notation `|`x`|` := abs x
-- y que la sucesión u es no decreciente por
--    def no_decreciente (u : ℕ → ℝ) :=
--      ∀ n m, n ≤ m → u n ≤ u m
--
-- Demostrar que si u es una sucesión no decreciente y su límite es a,
-- entonces u(n) ≤ a para todo n.
-- ---------------------------------------------------------------------

import data.real.basic
import tactic

variable {u : ℕ → ℝ}
variable (a : ℝ)

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - a| < ε

def no_decreciente (u : ℕ → ℝ) :=
  ∀ n m, n ≤ m → u n ≤ u m

-- 1ª demostración
example
  (h : limite u a)
  (h' : no_decreciente u)
  : ∀ n, u n ≤ a :=
begin
  intro n,
  by_contradiction H,
  push_neg at H,
  replace H : u n - a > 0 := sub_pos.mpr H,
  cases h (u n - a) H with m hm,
  let k := max n m,
  specialize hm k (le_max_right _ _),
  specialize h' n k (le_max_left _ _),
  replace hm : |u k - a| < u k - a, by
    calc |u k - a| < u n - a : hm
               ... ≤ u k - a : sub_le_sub_right h' a,
  rw ← not_le at hm,
  apply hm,
  exact le_abs_self (u k - a),
end

-- 2ª demostración
example
  (h : limite u a)
  (h' : no_decreciente u)
  : ∀ n, u n ≤ a :=
begin
  intro n,
  by_contradiction H,
  push_neg at H,
  cases h (u n - a) (by linarith) with m hm,
  specialize hm (max n m) (le_max_right _ _),
  specialize h' n (max n m) (le_max_left _ _),
  rw abs_lt at hm,
  linarith,
end
