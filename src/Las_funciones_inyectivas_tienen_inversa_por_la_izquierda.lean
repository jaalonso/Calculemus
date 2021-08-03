-- Las_funciones_inyectivas_tienen_inversa_por_la_izquierda.lean
-- Las funciones inyectivas tienen inversa por la izquierda
-- José A. Alonso Jiménez
-- Sevilla, 3 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, que g es una inversa por la izquierda de f está definido por
--    left_inverse (g : β → α) (f : α → β) : Prop :=
--       ∀ x, g (f x) = x
-- y que f tenga inversa por la izquierda está definido por
--    has_left_inverse (f : α → β) : Prop :=
--       ∃ finv : β → α, left_inverse finv f
-- Finalmente, que f es inyectiva está definido por
--    injective (f : α → β) : Prop :=
--       ∀ ⦃x y⦄, f x = f y → x = y
--
-- Demostrar que si f es una función inyectiva con dominio no vacío,
-- entonces f tiene inversa por la izquierda.
-- ---------------------------------------------------------------------

import tactic
open function classical

variables {α β: Type*}
variable  {f : α → β}

-- 1ª demostración
example
  [hα : nonempty α]
  (hf : injective f)
  : has_left_inverse f :=
begin
  classical,
  unfold has_left_inverse,
  let g := λ y, if h : ∃ x, f x = y then some h else choice hα,
  use g,
  unfold left_inverse,
  intro a,
  have h1 : ∃ x : α, f x = f a := Exists.intro a rfl,
  dsimp at *,
  dsimp [g],
  rw dif_pos h1,
  apply hf,
  exact some_spec h1,
end

-- 2ª demostración
example
  [hα : nonempty α]
  (hf : injective f)
  : has_left_inverse f :=
begin
  classical,
  let g := λ y, if h : ∃ x, f x = y then some h else choice hα,
  use g,
  intro a,
  have h1 : ∃ x : α, f x = f a := Exists.intro a rfl,
  dsimp [g],
  rw dif_pos h1,
  exact hf (some_spec h1),
end

-- 3ª demostración
example
  [hα : nonempty α]
  (hf : injective f)
  : has_left_inverse f :=
begin
  unfold has_left_inverse,
  use inv_fun f,
  unfold left_inverse,
  intro x,
  apply hf,
  apply inv_fun_eq,
  use x,
end

-- 4ª demostración
example
  [hα : nonempty α]
  (hf : injective f)
  : has_left_inverse f :=
begin
  use inv_fun f,
  intro x,
  apply hf,
  apply inv_fun_eq,
  use x,
end

-- 5ª demostración
example
  [hα : nonempty α]
  (hf : injective f)
  : has_left_inverse f :=
⟨inv_fun f, left_inverse_inv_fun hf⟩

-- 6ª demostración
example
  [hα : nonempty α]
  (hf : injective f)
  : has_left_inverse f :=
injective.has_left_inverse hf
