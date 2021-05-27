-- Diferencia_de_union_e_interseccion.lean
-- Diferencia de unión e interseccion
-- José A. Alonso Jiménez
-- Sevilla, 28 de mayo de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t)
-- ----------------------------------------------------------------------

import data.set.basic
open set

variable {α : Type}
variables s t : set α

-- 1ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext x,
  split,
  { rintros (⟨xs, xnt⟩ | ⟨xt, xns⟩),
    { split,
      { left,
        exact xs },
      { rintros ⟨_, xt⟩,
        contradiction }},
    { split ,
      { right,
        exact xt },
      { rintros ⟨xs, _⟩,
        contradiction }}},
  { rintros ⟨xs | xt, nxst⟩,
    { left,
      use xs,
      intro xt,
      apply nxst,
      split; assumption },
    { right,
      use xt,
      intro xs,
      apply nxst,
      split; assumption }},
end

-- 2ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext x,
  split,
  { rintros (⟨xs, xnt⟩ | ⟨xt, xns⟩),
    { finish, },
    { finish, }},
  { rintros ⟨xs | xt, nxst⟩,
    { finish, },
    { finish, }},
end

-- 3ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext x,
  split,
  { rintros (⟨xs, xnt⟩ | ⟨xt, xns⟩) ; finish, },
  { rintros ⟨xs | xt, nxst⟩ ; finish, },
end

-- 4ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext,
  split,
  { finish, },
  { finish, },
end

-- 5ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  rw ext_iff,
  intro,
  rw iff_def,
  finish,
end

-- 6ª demostración
-- ===============

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by finish [ext_iff, iff_def]
