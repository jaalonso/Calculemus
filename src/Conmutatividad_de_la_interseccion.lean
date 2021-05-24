-- Conmutatividad_de_la_interseccion.lean
-- Conmutatividad de la intersección.
-- José A. Alonso Jiménez
-- Sevilla, 24 de mayo de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∩ t = t ∩ s
-- ----------------------------------------------------------------------

import data.set.basic
open set

variable {α : Type}
variables s t u : set α

-- 1ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext x,
  simp only [mem_inter_eq],
  split,
  { intro h,
    split,
    { exact h.2, },
    { exact h.1, }},
  { intro h,
    split,
    { exact h.2, },
    { exact h.1, }},
end

-- 2ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext,
  simp only [mem_inter_eq],
  exact ⟨λ h, ⟨h.2, h.1⟩,
         λ h, ⟨h.2, h.1⟩⟩,
end

-- 3ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext,
  exact ⟨λ h, ⟨h.2, h.1⟩,
         λ h, ⟨h.2, h.1⟩⟩,
end

-- 4ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext x,
  simp only [mem_inter_eq],
  split,
  { rintros ⟨xs, xt⟩,
    exact ⟨xt, xs⟩ },
  { rintros ⟨xt, xs⟩,
    exact ⟨xs, xt⟩ },
end

-- 5ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext x,
  exact and.comm,
end

-- 6ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
ext (λ x, and.comm)

-- 7ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by ext x; simp [and.comm]

-- 8ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
inter_comm s t

-- 9ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by finish
