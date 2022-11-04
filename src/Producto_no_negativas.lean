-- Producto_no_negativas.lean
-- El producto de dos funciones no negativas es no negativa.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 4-noviembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que el producto de dos funciones no negativas es no
-- negativa.
-- ----------------------------------------------------------------------

import data.real.basic
variables (f g : ℝ → ℝ)

def no_negativa (f : ℝ → ℝ) : Prop := ∀ x, 0 ≤ f x

-- 1ª demostración
-- ===============

example
  (nnf : no_negativa f)
  (nng : no_negativa g)
  : no_negativa (f * g) :=
begin
  have h1 : ∀x, 0 ≤ f x * g x,
  { intro x,
    have h2: 0 ≤ f x := nnf x,
    have h3: 0 ≤ g x := nng x,
    show 0 ≤ f x * g x,
      by exact mul_nonneg (nnf x) (nng x), },
  show no_negativa (f * g),
    by exact h1,
end

-- 2ª demostración
-- ===============

example
  (nnf : no_negativa f)
  (nng : no_negativa g)
  : no_negativa (f * g) :=
begin
  intro x,
  change 0 ≤ f x * g x,
  apply mul_nonneg,
  apply nnf,
  apply nng
end

-- 3ª demostración
-- ===============

example
  (nnf : no_negativa f)
  (nng : no_negativa g)
  : no_negativa (f * g) :=
λ x, mul_nonneg (nnf x) (nng x)
