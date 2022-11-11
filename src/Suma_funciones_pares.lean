-- Suma_funciones_pares.lean
-- La suma de dos funciones pares es par.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 11-noviembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- La función f de ℝ en ℝ es par si, para todo x, f(-x) = f(x).
--
-- Demostrar que la suma de dos funciones pares es par.
-- ---------------------------------------------------------------------

import data.real.basic
variables (f g : ℝ → ℝ)

def par (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)

-- 1ª demostración
-- ===============

example
  (hf : par f)
  (hg : par g)
  : par (f + g) :=
begin
  intro x,
  have h1 : f x = f (-x) := hf x,
  have h2 : g x = g (-x) := hg x,
  calc (f + g) x
       = f x + g x       : rfl
   ... = f (-x) + g x    : congr_arg (+ g x) h1
   ... = f (-x) + g (-x) : congr_arg ((+) (f (-x))) h2
   ... = (f + g) (-x)    : rfl
end

-- 2ª demostración
-- ===============

example
  (hf : par f)
  (hg : par g)
  : par (f + g) :=
begin
  intro x,
  calc (f + g) x
       = f x + g x       : rfl
   ... = f (-x) + g (-x) : by rw [hf, hg]
   ... = (f + g) (-x)    : rfl
end
