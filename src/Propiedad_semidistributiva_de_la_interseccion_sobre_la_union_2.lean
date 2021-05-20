-- Propiedad_semidistributiva_de_la_interseccion_sobre_la_union_2.lean
-- 2ª propiedad semidistributiva de la intersección sobre la unión
-- José A. Alonso Jiménez
-- Sevilla, 20 de mayo de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)
-- ----------------------------------------------------------------------

import data.set.basic
open set

variable {α : Type}
variables s t u : set α

-- 1ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
begin
  intros x hx,
  cases hx with xst xsu,
  { split,
    { exact xst.1 },
    { left,
      exact xst.2 }},
  { split,
    { exact xsu.1 },
    { right,
      exact xsu.2 }},
end

-- 2ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
begin
  rintros x (⟨xs, xt⟩ | ⟨xs, xu⟩),
  { use xs,
    left,
    exact xt },
  { use xs,
    right,
    exact xu },
end

-- 3ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
by rw inter_distrib_left s t u

-- 4ª demostración
-- ===============

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
begin
  intros x hx,
  finish
end
