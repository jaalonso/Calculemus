-- Las_sucesiones_acotadas_por_cero_son_nulas.lean
-- Las sucesiones acotadas por cero son nulas
-- José A. Alonso Jiménez
-- Sevilla, 31 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que las sucesiones acotadas por cero son nulas.
-- ---------------------------------------------------------------------

import data.real.basic
import tactic

variable (u : ℕ → ℝ)

notation `|`x`|` := abs x

-- 1ª demostración
example
  (h : ∀ n, |u n| ≤ 0)
  : ∀ n, u n = 0 :=
begin
  intro n,
  rw ← abs_eq_zero,
  specialize h n,
  apply le_antisymm,
  { exact h, },
  { exact abs_nonneg (u n), },
end

-- 2ª demostración
example
  (h : ∀ n, |u n| ≤ 0)
  : ∀ n, u n = 0 :=
begin
  intro n,
  rw ← abs_eq_zero,
  specialize h n,
  exact le_antisymm h (abs_nonneg (u n)),
end

-- 3ª demostración
example
  (h : ∀ n, |u n| ≤ 0)
  : ∀ n, u n = 0 :=
begin
  intro n,
  rw ← abs_eq_zero,
  exact le_antisymm (h n) (abs_nonneg (u n)),
end

-- 4ª demostración
example
  (h : ∀ n, |u n| ≤ 0)
  : ∀ n, u n = 0 :=
begin
  intro n,
  exact abs_eq_zero.mp (le_antisymm (h n) (abs_nonneg (u n))),
end

-- 5ª demostración
example
  (h : ∀ n, |u n| ≤ 0)
  : ∀ n, u n = 0 :=
λ n, abs_eq_zero.mp (le_antisymm (h n) (abs_nonneg (u n)))

-- 6ª demostración
example
  (h : ∀ n, |u n| ≤ 0)
  : ∀ n, u n = 0 :=
by finish
