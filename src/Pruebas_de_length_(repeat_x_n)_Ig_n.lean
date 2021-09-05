-- Pruebas_de_length_(repeat_x_n)_Ig_n.lean
-- Pruebas de length (repeat x n) = n
-- José A. Alonso Jiménez
-- Sevilla, 7 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En Lean están definidas las funciones length y repeat tales que
-- + (length xs) es la longitud de la lista xs. Por ejemplo,
--      length [1,2,5,2] = 4
-- + (repeat x n) es la lista que tiene el elemento x n veces. Por
--   ejemplo,
--      repeat 7 3 = [7, 7, 7]
--
-- Demostrar que
--    length (repeat x n) = n
-- ---------------------------------------------------------------------

import data.list.basic
open nat
open list

set_option pp.structure_projections false

variable {α : Type}
variable (x : α)
variable (n : ℕ)

-- 1ª demostración
example :
  length (repeat x n) = n :=
begin
  induction n with n HI,
  { calc length (repeat x 0)
          = length []                : rfl
      ... = 0                        : rfl },
  { calc length (repeat x (succ n))
         = length (x :: repeat x n)  : rfl
     ... = length (repeat x n) + 1   : rfl
     ... = n + 1                     : by rw HI
     ... = succ n                    : rfl, },
end

-- 2ª demostración
example : length (repeat x n) = n :=
begin
  induction n with n HI,
  { refl, },
  { dsimp,
    rw HI, },
end

-- 3ª demostración
example : length (repeat x n) = n :=
begin
  induction n with n HI,
  { simp, },
  { simp [HI], },
end

-- 4ª demostración
example : length (repeat x n) = n :=
by induction n ; simp [*]

-- 5ª demostración
example : length (repeat x n) = n :=
nat.rec_on n
  ( show length (repeat x 0) = 0, from
      calc length (repeat x 0)
           = length []                : rfl
       ... = 0                        : rfl )
  ( assume n,
    assume HI : length (repeat x n) = n,
    show length (repeat x (succ n)) = succ n, from
      calc length (repeat x (succ n))
           = length (x :: repeat x n) : rfl
       ... = length (repeat x n) + 1  : rfl
       ... = n + 1                    : by rw HI
       ... = succ n                   : rfl )

-- 6ª demostración
example : length (repeat x n) = n :=
nat.rec_on n
  ( by simp )
  ( λ n HI, by simp [HI])

-- 7ª demostración
example : length (repeat x n) = n :=
length_repeat x n

-- 8ª demostración
example : length (repeat x n) = n :=
by simp

-- 9ª demostración
lemma length_repeat_1 :
  ∀ n, length (repeat x n) = n
| 0 := by calc length (repeat x 0)
               = length ([] : list α)         : rfl
           ... = 0                            : rfl
| (n+1) := by calc length (repeat x (n + 1))
                   = length (x :: repeat x n) : rfl
               ... = length (repeat x n) + 1  : rfl
               ... = n + 1                    : by rw length_repeat_1

-- 10ª demostración
lemma length_repeat_2 :
  ∀ n, length (repeat x n) = n
| 0     := by simp
| (n+1) := by simp [*]
