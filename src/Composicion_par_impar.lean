-- Composicion_par_impar.lean
-- Si f es par y g es impar, entonces f ∘ g es par.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 17-noviembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- La función f de ℝ en ℝ es par si, para todo x, f(-x) = f(x) y es
-- impar si, para todo x, f(-x) -f(x).
--
-- Demostrar que si f es par y g es impar, entonces f ∘ g es par.
-- ----------------------------------------------------------------------

import data.real.basic
variables (f g : ℝ → ℝ)

def par (f : ℝ → ℝ) : Prop    := ∀ x, f x = f (-x)
def impar  (f : ℝ → ℝ) : Prop := ∀ x, f x = -f (-x)

-- 1ª demostración
-- ===============

example
  (hf : par f)
  (hg : impar g)
  : par (f ∘ g) :=
begin
  intro x,
  have h1 : f x = f (-x) := hf x,
  have h2 : g x = -g (-x) := hg x,
  calc (f ∘ g) x
       = f (g x)      : rfl
   ... = f (-g (-x))  : congr_arg f (hg x)
   ... = f (g (-x))   : eq.symm (hf (g (-x)))
   ... = (f ∘ g) (-x) : rfl
end

-- 2ª demostración
-- ===============

example
  (hf : par f)
  (hg : impar g)
  : par (f ∘ g) :=
begin
  intro x,
  calc (f ∘ g) x
       = f (g x)      : rfl
   ... = f (-g (-x))  : by rw hg
   ... = f (g (-x))   : by rw ←hf
   ... = (f ∘ g) (-x) : rfl
end
