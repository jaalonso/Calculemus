-- Union_de_pares_e_impares.lean
-- Unión de pares e impares
-- José A. Alonso Jiménez
-- Sevilla, 31 de mayo de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Los conjuntos de los números naturales, de los pares y de los impares
-- se definen por
--    def naturales : set ℕ := {n | true}
--    def pares     : set ℕ := {n | even n}
--    def impares   : set ℕ := {n | ¬ even n}
--
-- Demostrar que
--    pares ∪ impares = naturales
-- ----------------------------------------------------------------------

import data.nat.parity
import data.set.basic
import tactic

open set

def naturales : set ℕ := {n | true}
def pares     : set ℕ := {n | even n}
def impares   : set ℕ := {n | ¬ even n}

-- 1ª demostración
-- ===============

example : pares ∪ impares = naturales :=
begin
  unfold pares impares naturales,
  ext n,
  simp,
  apply classical.em,
end

-- 2ª demostración
-- ===============

example : pares ∪ impares = naturales :=
begin
  unfold pares impares naturales,
  ext n,
  finish,
end

-- 3ª demostración
-- ===============

example : pares ∪ impares = naturales :=
by finish [pares, impares, naturales, ext_iff]
