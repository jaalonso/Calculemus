-- Interseccion_de_los_primos_y_los_mayores_que_dos.lean
-- Intersección de los primos y los mayores que dos
-- José A. Alonso Jiménez
-- Sevilla, 1 de junio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Los números primos, los mayores que 2 y los impares se definen por
--    def primos      : set ℕ := {n | prime n}
--    def mayoresQue2 : set ℕ := {n | n > 2}
--    def impares     : set ℕ := {n | ¬ even n}
--
-- Demostrar que
--    primos ∩ mayoresQue2 ⊆ impares
-- ----------------------------------------------------------------------

import data.nat.parity
import data.nat.prime
import tactic

open nat

def primos      : set ℕ := {n | prime n}
def mayoresQue2 : set ℕ := {n | n > 2}
def impares     : set ℕ := {n | ¬ even n}

example : primos ∩ mayoresQue2 ⊆ impares :=
begin
  unfold primos mayoresQue2 impares,
  intro n,
  simp,
  intro hn,
  cases prime.eq_two_or_odd hn with h h,
  { rw h,
    intro,
    linarith, },
  { rw even_iff,
    rw h,
    norm_num },
end
