-- Acotacion_de_convergentes.lean
-- Acotación de sucesiones convergentes
-- José A. Alonso Jiménez
-- Sevilla, 25 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar u es una sucesión convergente, entonces está acotada; es
-- decir
--     ∃ k b. ∀n≥k. ¦u n¦ ≤ b
-- ----------------------------------------------------------------------

import data.real.basic

variable {u : ℕ → ℝ}
variable {a : ℝ}

notation `|`x`|` := abs x

-- (limite u c) expresa que el límite de u es c.
def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| ≤ ε

-- (convergente u) expresa que u es convergente.
def convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

-- 1ª demostración
example
  (h : convergente u)
  : ∃ k b, ∀ n, n ≥ k → |u n| ≤ b :=
begin
  cases h with a ua,
  cases ua 1 zero_lt_one with k h,
  use [k, 1 + |a|],
  intros n hn,
  specialize h n hn,
  calc |u n|
       = |u n - a + a|   : congr_arg abs (eq_add_of_sub_eq rfl)
   ... ≤ |u n - a| + |a| : abs_add (u n - a) a
   ... ≤ 1 + |a|         : add_le_add_right h _
end

-- 2ª demostración
example
  (h : convergente u)
  : ∃ k b, ∀ n, n ≥ k → |u n| ≤ b :=
begin
  cases h with a ua,
  cases ua 1 zero_lt_one with k h,
  use [k, 1 + |a|],
  intros n hn,
  specialize h n hn,
  calc |u n|
       = |u n - a + a|   : by ring_nf
   ... ≤ |u n - a| + |a| : abs_add (u n - a) a
   ... ≤ 1 + |a|         : by linarith,
end
