-- Si_gf_es_suprayectiva_entonces_g_es_suprayectiva.lean
-- Si gf es suprayectiva, entonces g es suprayectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-junio-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si g·f es suprayectiva, entonces g es suprayectiva
-- ---------------------------------------------------------------------

import tactic
open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

-- 1ª demostración
-- ===============

example
  (Hgf : surjective (g ∘ f))
  : surjective g :=
begin
  intros z,
  rcases Hgf z with ⟨x, hx⟩,
  use f x,
  calc g (f x) = (g ∘ f) x : rfl
           ... = z         : hx,
end

-- 2ª demostración
-- ===============

example
  (Hgf : surjective (g ∘ f))
  : surjective g  := 
begin
  assume z : Z,
  rcases Hgf z with ⟨x : X, hx : (g ∘ f) x = z⟩,
  let y : Y := f x,
  use y,
  show g y = z, from
    calc g y = g (f x)   : rfl
         ... = (g ∘ f) x : rfl
         ... = z         : hx,
end  
