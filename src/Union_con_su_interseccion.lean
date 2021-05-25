-- Union_con_su_interseccion.lean
-- Unión con su intersección
-- José A. Alonso Jiménez
-- Sevilla, 26 de mayo de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∪ (s ∩ t) = s
-- ----------------------------------------------------------------------

import data.set.basic
open set

variable {α : Type}
variables s t : set α

-- 1ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
begin
  ext x,
  split,
  { intro hx,
    cases hx with xs xst,
    { exact xs, },
    { exact xst.1, }},
  { intro xs,
    left,
    exact xs, },
end

-- 2ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
begin
  ext x,
  exact ⟨λ hx, or.dcases_on hx id and.left,
         λ xs, or.inl xs⟩,
end

-- 3ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
begin
  ext x,
  split,
  { rintros (xs | ⟨xs, xt⟩);
    exact xs },
  { intro xs,
    left,
    exact xs },
end

-- 4ª demostración
-- ===============

example : s ∪ (s ∩ t) = s :=
sup_inf_self
