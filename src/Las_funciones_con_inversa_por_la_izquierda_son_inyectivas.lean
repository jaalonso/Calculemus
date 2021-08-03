-- Las_funciones_con_inversa_por_la_izquierda_son_inyectivas.lean
-- Las funciones con inversa por la izquierda son inyectivas
-- José A. Alonso Jiménez
-- Sevilla, 2 de agosto de 2021
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
-- Demostrar que si f tiene inversa por la izquierda, entonces f es
-- inyectiva.
-- ---------------------------------------------------------------------

import tactic
open function

universes u v
variables {α : Type u}
variable  {β : Type v}
variable  {f : α → β}

-- 1ª demostración
example
  (hf : has_left_inverse f)
  : injective f :=
begin
  intros x y hxy,
  unfold has_left_inverse at hf,
  unfold left_inverse at hf,
  cases hf with g hg,
  calc x = g (f x) : (hg x).symm
     ... = g (f y) : congr_arg g hxy
     ... = y       : hg y
end

-- 2ª demostración
example
  (hf : has_left_inverse f)
  : injective f :=
begin
  intros x y hxy,
  cases hf with g hg,
  calc x = g (f x) : (hg x).symm
     ... = g (f y) : congr_arg g hxy
     ... = y       : hg y
end

-- 3ª demostración
example
  (hf : has_left_inverse f)
  : injective f :=
exists.elim hf (λ finv inv, inv.injective)

-- 4ª demostración
example
  (hf : has_left_inverse f)
  : injective f :=
has_left_inverse.injective hf
