-- CN_de_diferencia_no_negativa.lean
-- Si R es un anillo ordenado y a b ∈ R, entonces 0 ≤ b - a → a ≤ b
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-octubre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un anillo ordenado y a b ∈ R, entonces
--    0 ≤ b - a → a ≤ b
-- ---------------------------------------------------------------------

import algebra.order.ring
variables {R : Type*} [ordered_ring R]
variables a b : R

-- 1ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
begin
  intro h,
  calc
    a   = 0 + a       : (zero_add a).symm
    ... ≤ (b - a) + a : add_le_add_right h a
    ... = b           : sub_add_cancel b a
end

-- 2ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
-- by library_search
sub_nonneg.mp

-- 3ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
-- by hint
by simp
