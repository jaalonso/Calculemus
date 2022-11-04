-- Suma_de_cotas_inferiores.lean
-- La suma de una cota inferior de f y una cota inferior de g es una cota inferior de f+g
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 2-noviembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la suma de una cota inferior de f y una cota inferior
-- de g es una cota inferior de f + g.
-- ----------------------------------------------------------------------

import data.real.basic

-- (cota_inferior f a) se verifica si a es una cota inferior de f.
def cota_inferior (f : ℝ → ℝ) (a : ℝ) : Prop :=
∀ x, a ≤ f x

variables (f g : ℝ → ℝ)
variables (a b : ℝ)

-- 1ª demostración
-- ===============

example
  (hfa : cota_inferior f a)
  (hgb : cota_inferior g b)
  : cota_inferior (λ x, f x + g x) (a + b) :=
begin
  have h1 : ∀ x, a + b ≤ f x + g x,
  { intro x,
    have h1a : a ≤ f x := hfa x,
    have h1b : b ≤ g x := hgb x,
    show a + b ≤ f x + g x,
      by exact add_le_add (hfa x) (hgb x), },
  show cota_inferior (λ x, f x + g x) (a + b),
    by exact h1,
end

-- 2ª demostración
-- ===============

example
  (hfa : cota_inferior f a)
  (hgb : cota_inferior g b)
  : cota_inferior (λ x, f x + g x) (a + b) :=
begin
  intro x,
  dsimp,
  change a + b ≤ f x + g x,
  apply add_le_add,
  apply hfa,
  apply hgb
end

-- 3ª demostración
-- ===============

example
  (hfa : cota_inferior f a)
  (hgb : cota_inferior g b)
  : cota_inferior (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)
