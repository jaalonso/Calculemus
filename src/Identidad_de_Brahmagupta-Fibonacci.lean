-- Identidad_de_Brahmagupta-Fibonacci.lean
-- Identidad de Brahmagupta-Fibonacci
-- José A. Alonso Jiménez
-- Sevilla, 26 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar la identidad de Brahmagupta-Fibonacci https://bit.ly/3ucEc80
--    (a² + b²) * (c² + d²) = (ac - bd)² + (ad + bc)²
-- ---------------------------------------------------------------------

import data.real.basic

variables (a b c d : ℝ)

-- 1ª demostración
example : (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2 :=
calc (a^2 + b^2) * (c^2 + d^2)
     = a^2 * (c^2 + d^2) + b^2 * (c^2 + d^2)
         : right_distrib (a^2) (b^2) (c^2 + d^2)
 ... = (a^2*c^2 + a^2*d^2) + b^2 * (c^2 + d^2)
         : congr_arg2 (+) (left_distrib (a^2) (c^2) (d^2)) rfl
 ... = (a^2*c^2 + a^2*d^2) + (b^2*c^2 + b^2*d^2)
         : congr_arg2 (+) rfl (left_distrib (b^2) (c^2) (d^2))
 ... = ((a*c)^2 + (b*d)^2) + ((a*d)^2 + (b*c)^2)
         : by ring
 ... = ((a*c)^2 - 2*a*c*b*d + (b*d)^2) + ((a*d)^2 + 2*a*d*b*c + (b*c)^2)
         : by ring
 ... = (a*c - b*d)^2 + (a*d + b*c)^2
         : by ring

-- 2ª demostración
example : (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2 :=
by ring
