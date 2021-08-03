-- Una_funcion_tiene_inversa_por_la_izquierda_si_y_solo_si_es_inyectiva.lean
-- Una función tiene inversa por la izquierda si y solo si es inyectiva
-- José A. Alonso Jiménez
-- Sevilla, 4 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean, que g es una inversa por la izquierda de f que está definido
-- en Lean por
--    left_inverse (g : β → α) (f : α → β) : Prop :=
--       ∀ x, g (f x) = x
-- y que f tenga inversa por la izquierda está definido por
--    has_left_inverse (f : α → β) : Prop :=
--       ∃ finv : β → α, left_inverse finv f
-- Finalmente, que f es inyectiva está definido por
--    injective (f : α → β) : Prop :=
--       ∀ ⦃x y⦄, f x = f y → x = y
--
-- Demostrar que una función f, con dominio no vacío, tiene inversa por
-- la izquierda si y solo si es inyectiva.
-- ---------------------------------------------------------------------

import tactic
open function classical

variables {α : Type*} [nonempty α]
variable  {β : Type*}
variable  {f : α → β}

-- 1ª demostración
example
  : has_left_inverse f ↔ injective f :=
begin
  split,
  { intro hf,
    intros x y hxy,
    cases hf with g hg,
    calc x = g (f x) : (hg x).symm
       ... = g (f y) : congr_arg g hxy
       ... = y       : hg y, },
  { intro hf,
    use inv_fun f,
    intro x,
    apply hf,
    apply inv_fun_eq,
    use x, },
end

-- 2ª demostración
example
  : has_left_inverse f ↔ injective f :=
begin
  split,
  { intro hf,
    exact has_left_inverse.injective hf },
  { intro hf,
    exact injective.has_left_inverse hf },
end

-- 3ª demostración
example
  : has_left_inverse f ↔ injective f :=
⟨has_left_inverse.injective, injective.has_left_inverse⟩

-- 4ª demostración
example
  : has_left_inverse f ↔ injective f :=
injective_iff_has_left_inverse.symm
