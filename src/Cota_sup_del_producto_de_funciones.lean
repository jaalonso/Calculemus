-- Cota_sup_del_producto_de_funciones.lean
-- Si a es una cota superior no negativa de f y b es es una cota
--   superior de la función no negativa g, entonces a*b es una cota
--   superior de f*g
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 7-noviembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a es una cota superior no negativa de f y b es es
-- una cota superior de la función no negativa g, entonces a*b es una
-- cota superior de f*g.
-- ----------------------------------------------------------------------

import data.real.basic

def cota_superior (f : ℝ → ℝ) (a : ℝ) : Prop :=
∀ x, f x ≤ a

def no_negativa (f : ℝ → ℝ) : Prop :=
∀ x, 0 ≤ f x

variables (f g : ℝ → ℝ)
variables (a b : ℝ)

-- 1ª demostración
-- ===============

example
  (hfa : cota_superior f a)
  (hgb : cota_superior g b)
  (nng : no_negativa g)
  (nna : 0 ≤ a)
  : cota_superior (f * g) (a * b) :=
begin
  have h1 : ∀ x, f x * g x ≤ a * b,
    { intro x,
      have h2 : f x ≤ a := hfa x,
      have h3 : g x ≤ b := hgb x,
      have h4 : 0 ≤ g x := nng x,
      show f x * g x ≤ a * b,
        by exact mul_le_mul h2 h3 h4 nna, },
  show cota_superior (f * g) (a * b),
    by exact h1,
end

-- 2ª demostración
-- ===============

example
  (hfa : cota_superior f a)
  (hgb : cota_superior g b)
  (nng : no_negativa g)
  (nna : 0 ≤ a)
  : cota_superior (f * g) (a * b) :=
begin
  intro x,
  change f x * g x ≤ a * b,
  apply mul_le_mul,
  apply hfa,
  apply hgb,
  apply nng,
  apply nna
end

-- 3ª demostración
-- ===============

example
  (hfa : cota_superior f a)
  (hgb : cota_superior g b)
  (nng : no_negativa g)
  (nna : 0 ≤ a)
  : cota_superior (f * g) (a * b) :=
begin
  dunfold cota_superior no_negativa at *,
  intro x,
  have h1:= hfa x,
  have h2:= hgb x,
  have h3:= nng x,
  exact mul_le_mul h1 h2 h3 nna,
end

-- 4ª demostración
-- ===============

example
  (hfa : cota_superior f a)
  (hgb : cota_superior g b)
  (nng : no_negativa g)
  (nna : 0 ≤ a)
  : cota_superior (f * g) (a * b) :=
begin
  dunfold cota_superior no_negativa at *,
  intro x,
  specialize hfa x,
  specialize hgb x,
  specialize nng x,
  exact mul_le_mul hfa hgb nng nna,
end

-- 5ª demostración
-- ===============

example
  (hfa : cota_superior f a)
  (hgb : cota_superior g b)
  (nng : no_negativa g)
  (nna : 0 ≤ a)
  : cota_superior (f * g) (a * b) :=
λ x, mul_le_mul (hfa x) (hgb x) (nng x) nna
