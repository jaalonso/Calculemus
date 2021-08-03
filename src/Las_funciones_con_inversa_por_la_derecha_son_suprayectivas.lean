-- Las_funciones_con_inversa_por_la_derecha_son_suprayectivas.lean
-- Las funciones con inversa por la derecha son suprayectivas.
-- José A. Alonso Jiménez
-- Sevilla, 5 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, que g es una inversa por la izquierda de f está definido por
--    left_inverse (g : β → α) (f : α → β) : Prop :=
--       ∀ x, g (f x) = x
-- que g es una inversa por la derecha de f está definido por
--    right_inverse (g : β → α) (f : α → β) : Prop :=
--       left_inverse f g
-- y que f tenga inversa por la derecha está definido por
--    has_right_inverse (f : α → β) : Prop :=
--       ∃ g : β → α, right_inverse g f
-- Finalmente, que f es suprayectiva está definido por
--    def surjective (f : α → β) : Prop :=
--       ∀ b, ∃ a, f a = b
--
-- Demostrar que si la función f tiene inversa por la derecha, entonces
-- f es suprayectiva.
-- ---------------------------------------------------------------------

import tactic
open function

variables {α β: Type*}
variable  {f : α → β}

-- 1ª demostración
example
  (hf : has_right_inverse f)
  : surjective f :=
begin
  unfold surjective,
  unfold has_right_inverse at hf,
  cases hf with g hg,
  intro b,
  use g b,
  exact hg b,
end

-- 2ª demostración
example
  (hf : has_right_inverse f)
  : surjective f :=
begin
  intro b,
  cases hf with g hg,
  use g b,
  exact hg b,
end

-- 3ª demostración
example
  (hf : has_right_inverse f)
  : surjective f :=
begin
  intro b,
  cases hf with g hg,
  use [g b, hg b],
end

-- 4ª demostración
example
  (hf : has_right_inverse f)
  : surjective f :=
has_right_inverse.surjective hf
