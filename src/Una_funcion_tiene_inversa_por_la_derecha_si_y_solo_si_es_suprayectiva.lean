-- Una_funcion_tiene_inversa_por_la_derecha_si_y_solo_si_es_suprayectiva.lean
-- Una función tiene inversa por la derecha si y solo si es suprayectiva
-- José A. Alonso Jiménez
-- Sevilla, 7 de agosto de 2021
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
-- Demostrar que la función f tiene inversa por la derecha si y solo si
-- es suprayectiva.
-- ---------------------------------------------------------------------

import tactic
open function classical

variables {α β: Type*}
variable  {f : α → β}

-- 1ª demostración
example : has_right_inverse f ↔ surjective f :=
begin
  split,
  { intros hf b,
    cases hf with g hg,
    use g b,
    exact hg b, },
  { intro hf,
    let g := λ y, some (hf y),
    use g,
    intro b,
    apply some_spec (hf b), },
end

-- 2ª demostración
example : has_right_inverse f ↔ surjective f :=
surjective_iff_has_right_inverse.symm
