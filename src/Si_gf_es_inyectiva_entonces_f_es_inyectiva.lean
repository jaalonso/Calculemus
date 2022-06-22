-- Si_gf_es_inyectiva_entonces_f_es_inyectiva.lean
-- Si g·f es inyectiva, entonces f es inyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 22-junio-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si g·f es inyectiva, entonces f es inyectiva.
-- ---------------------------------------------------------------------

import tactic
open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

-- 1ª demostración
example
  (Hgf : injective (g ∘ f))
  : injective f :=
begin
  intros x x' f_xx',
  apply Hgf,
  calc (g ∘ f) x = g (f x)    : rfl
             ... = g (f x')   : congr_arg g f_xx'
             ... = (g ∘ f) x' : rfl
end

-- 2ª demostración
example
  (Hgf : injective (g ∘ f))
  : injective f :=
begin
  intros x x' f_xx',
  apply Hgf,
  simp [f_xx'],
end

-- 3ª demostración
example
  (Hgf : injective (g ∘ f))
  : injective f :=
begin
  intros x x' f_xx',
  apply Hgf,
  finish,
end

-- 4ª demostración
example
  (Hgf : injective (g ∘ f))
  : injective f :=
begin
  assume x  : X, 
  assume x' : X, 
  assume f_xx' : f x = f x',
  have gf_xx' : (g ∘ f) x = (g ∘ f) x', from 
    calc (g ∘ f) x = g (f x)    : rfl
               ... = g (f x')   : congr_arg g f_xx'
               ... = (g ∘ f) x' : rfl,
  show x = x', 
    { exact Hgf gf_xx' },
end
