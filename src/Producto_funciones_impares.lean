-- Producto_funciones_impares.lean
-- El producto de dos funciones impares es par.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 14-noviembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- La función f de ℝ en ℝ es par si, para todo x, f(-x) = f(x) y es
-- impar si, para todo x, f(-x) -f(x).
--
-- Demostrar que el producto de dos funciones impares es par.
-- ---------------------------------------------------------------------

import data.real.basic
variables (f g : ℝ → ℝ)

def par (f : ℝ → ℝ) : Prop    := ∀ x, f x = f (-x)
def impar  (f : ℝ → ℝ) : Prop := ∀ x, f x = -f (-x)

-- 1ª demostración
-- ===============

example
  (hf : impar f)
  (hg : impar g)
  : par (f * g) :=
begin
  intro x,
  have h1 : f x = -f (-x) := hf x,
  have h2 : g x = -g (-x) := hg x,
  calc (f * g) x
       = f x * g x             : rfl
   ... = (-f (-x)) * g x       : congr_arg (* g x) h1
   ... = (-f (-x)) * (-g (-x)) : congr_arg ((*) (-f (-x))) h2
   ... = f (-x) * g (-x)       : neg_mul_neg (f (-x)) (g (-x))
   ... = (f * g) (-x)          : rfl,
end

-- 2ª demostración
-- ===============

example
  (hf : impar f)
  (hg : impar g)
  : par (f * g) :=
begin
  intro x,
  calc (f * g) x
       = f x * g x         : rfl
   ... = -f (-x) * -g (-x) : by rw [hf, hg]
   ... = f (-x) * g (-x)   : by rw neg_mul_neg
   ... = (f * g) (-x)      : rfl
end

-- 3ª demostración
-- ===============

example
  (hf : impar f)
  (hg : impar g)
  : par (f * g) :=
begin
  intro x,
  calc (f * g) x
       = f x * g x         : rfl
   ... = f (-x) * g (-x)   : by rw [hf, hg, neg_mul_neg]
   ... = (f * g) (-x)      : rfl
end
