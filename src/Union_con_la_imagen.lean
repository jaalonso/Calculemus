-- Union_con_la_imagen.lean
-- Unión con la imagen
-- José A. Alonso Jiménez
-- Sevilla, 20 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v
-- ----------------------------------------------------------------------

import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α
variable  v : set β

-- 1ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
begin
  intros y hy,
  cases hy with x hx,
  cases hx with hx1 fxy,
  cases hx1 with xs xv,
  { left,
    use x,
    split,
    { exact xs, },
    { exact fxy, }},
  { right,
    rw ← fxy,
    exact xv, },
end

-- 2ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
begin
  rintros y ⟨x, xs | xv, fxy⟩,
  { left,
    use [x, xs, fxy], },
  { right,
    rw ← fxy,
    exact xv, },
end

-- 3ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
begin
  rintros y ⟨x, xs | xv, fxy⟩;
  finish,
end
