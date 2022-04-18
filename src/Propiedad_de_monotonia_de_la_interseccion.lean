-- Propiedad_de_monotonia_de_la_interseccion.lean
-- Propiedad de monotonía de la intersección.
-- José A. Alonso Jiménez
-- Sevilla, 17 de mayo de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si
--    s ⊆ t
-- entonces
--    s ∩ u ⊆ t ∩ u
-- ----------------------------------------------------------------------

import data.set.basic
import tactic
open set

variable {α : Type}
variables s t u : set α

-- 1ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  rw subset_def,
  rw inter_def,
  rw inter_def,
  dsimp,
  intros x h,
  cases h with xs xu,
  split,
  { rw subset_def at h,
    apply h,
    assumption },
  { assumption },
end

-- 2ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  rw [subset_def, inter_def, inter_def],
  dsimp,
  rintros x ⟨xs, xu⟩,
  rw subset_def at h,
  exact ⟨h _ xs, xu⟩,
end

-- 3ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  simp only [subset_def, mem_inter_eq] at *,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

-- 4ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  intros x xsu,
  exact ⟨h xsu.1, xsu.2⟩,
end

-- 5ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
-- by library_search
inter_subset_inter_left u h

-- 6ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
by tidy
