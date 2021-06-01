-- Distributiva_de_la_interseccion_respecto_de_la_union_general.lean
-- Distributiva de la intersección respecto de la unión general
-- José A. Alonso Jiménez
-- Sevilla, 2 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que
--    s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s)
-- ----------------------------------------------------------------------

import data.set.basic
import data.set.lattice
import tactic

open set

variable {α : Type}
variable s : set α
variable A : ℕ → set α

-- 1ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  split,
  { intro h,
    rw mem_Union,
    cases h with xs xUAi,
    rw mem_Union at xUAi,
    cases xUAi with i xAi,
    use i,
    split,
    { exact xAi, },
    { exact xs, }},
  { intro h,
    rw mem_Union at h,
    cases h with i hi,
    cases hi with xAi xs,
    split,
    { exact xs, },
    { rw mem_Union,
      use i,
      exact xAi, }},
end

-- 2ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Union],
  split,
  { rintros ⟨xs, ⟨i, xAi⟩⟩,
    exact ⟨i, xAi, xs⟩, },
  { rintros ⟨i, xAi, xs⟩,
    exact ⟨xs, ⟨i, xAi⟩⟩ },
end

-- 3ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  finish [mem_inter_eq, mem_Union],
end

-- 4ª demostración
-- ===============

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
by finish [mem_inter_eq, mem_Union, ext_iff]
