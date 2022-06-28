-- Si_ff_es_biyectiva_entonces_f_es_biyectiva.lean
-- Si f·f es biyectiva entonces f es biyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-junio-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si f·f es biyectiva, entonces f es biyectiva.
-- ---------------------------------------------------------------------

import tactic
open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z}

-- 1ª demostración
-- ===============

lemma iny_comp_iny_primera
  (Hgf : injective (g ∘ f))
  : injective f :=
begin
  intros x x' f_xx',
  apply Hgf,
  finish,
end

lemma supr_comp_supr_segunda
  (Hgf : surjective (g ∘ f))
  : surjective g :=
begin
  intros z,
  rcases Hgf z with ⟨x, hx⟩,
  use f x,
  calc g (f x) = (g ∘ f) x : rfl
           ... = z         : hx,
end

example
  (f : X → X)
  (Hff : bijective (f ∘ f))
  : bijective f :=
begin
  split,
  { have h1 : injective (f ∘ f) := bijective.injective Hff,
    exact iny_comp_iny_primera h1, },
  { have h2 : surjective (f ∘ f) := bijective.surjective Hff,
    exact supr_comp_supr_segunda h2, },
end
