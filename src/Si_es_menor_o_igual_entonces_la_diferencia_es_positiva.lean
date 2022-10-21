-- Si_es_menor_o_igual_entonces_la_diferencia_es_positiva.lean
-- Si R es un anillo ordenado, entonces ∀ a b ∈ R, a ≤ b → 0 ≤ b - a
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-octubre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo ordenado y a, b ∈ R, entonces
--    a ≤ b → 0 ≤ b - a
-- ----------------------------------------------------------------------

import algebra.order.ring
variables {R : Type*} [ordered_ring R]
variables a b : R

-- 1ª demostración
-- ===============

example : a ≤ b → 0 ≤ b - a :=
begin
  intro h,
  calc
    0   = a - a : (sub_self a).symm
    ... ≤ b - a : sub_le_sub_right h a
end

-- 2ª demostración
-- ===============

example : a ≤ b → 0 ≤ b - a :=
-- by library_search
sub_nonneg.mpr

-- 3ª demostración
-- ===============

example : a ≤ b → 0 ≤ b - a :=
-- by hint
by simp
