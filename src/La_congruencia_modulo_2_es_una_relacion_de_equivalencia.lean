-- La_congruencia_modulo_2_es_una_relacion_de_equivalencia.lean
-- La congruencia módulo 2 es una relación de equivalencia
-- José A. Alonso Jiménez
-- Sevilla, 1 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Se define la relación R entre los números enteros de forma que x está
-- relacionado con y si x-y es divisible por 2. Demostrar que R es una
-- relación de equivalencia.
-- ---------------------------------------------------------------------

import data.int.basic
import tactic

def R (m n : ℤ) := 2 ∣ (m - n)

-- 1ª demostración
example : equivalence R :=
begin
  repeat {split},
  { intro x,
    unfold R,
    rw sub_self,
    exact dvd_zero 2, },
  { intros x y hxy,
    unfold R,
    cases hxy with a ha,
    use -a,
    calc y - x
         = -(x - y) : (neg_sub x y).symm
     ... = -(2 * a) : by rw ha
     ... = 2 * -a   : neg_mul_eq_mul_neg 2 a, },
  { intros x y z hxy hyz,
    cases hxy with a ha,
    cases hyz with b hb,
    use a + b,
    calc x - z
         = (x - y) + (y - z) : (sub_add_sub_cancel x y z).symm
     ... = 2 * a + 2 * b     : congr_arg2 ((+)) ha hb
     ... = 2 * (a + b)       : (mul_add 2 a b).symm , },
end

-- 2ª demostración
example : equivalence R :=
begin
  repeat {split},
  { intro x,
    simp [R], },
  { rintros x y ⟨a, ha⟩,
    use -a,
    linarith, },
  { rintros x y z ⟨a, ha⟩ ⟨b, hb⟩,
    use a + b,
    linarith, },
end
