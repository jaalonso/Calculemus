-- Las_funciones_suprayectivas_tienen_inversa_por_la_derecha.lean
-- Las funciones suprayectivas tienen inversa por la derecha
-- José A. Alonso Jiménez
-- Sevilla, 6 de agosto de 2021
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
-- Demostrar que si f es una función suprayectiva, entonces f tiene
-- inversa por la derecha.
-- ---------------------------------------------------------------------

import tactic
open function classical

variables {α β: Type*}
variable  {f : α → β}

-- 1ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
begin
  unfold has_right_inverse,
  let g := λ y, some (hf y),
  use g,
  unfold function.right_inverse,
  unfold function.left_inverse,
  intro b,
  apply some_spec (hf b),
end

-- 2ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
begin
  let g := λ y, some (hf y),
  use g,
  intro b,
  apply some_spec (hf b),
end

-- 3ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
begin
  use surj_inv hf,
  intro b,
  exact surj_inv_eq hf b,
end

-- 4ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
begin
  use surj_inv hf,
  exact surj_inv_eq hf,
end

-- 5ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
begin
  use [surj_inv hf, surj_inv_eq hf],
end

-- 6ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
⟨surj_inv hf, surj_inv_eq hf⟩

-- 7ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
⟨_, surj_inv_eq hf⟩

-- 8ª demostración
example
  (hf : surjective f)
  : has_right_inverse f :=
surjective.has_right_inverse hf
