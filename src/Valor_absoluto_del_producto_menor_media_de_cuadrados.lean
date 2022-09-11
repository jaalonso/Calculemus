-- Valor_absoluto_del_producto_menor_media_de_cuadrados.lean
-- Si a, b ∈ ℝ, entonces |ab| ≤ (a^2 + b^2)/2
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-septiembre-2022
-- ---------------------------------------------------------------------

import data.real.basic
import tactic

variables a b : ℝ

-- 1ª demostración
example : abs (a*b) ≤ (a^2 + b^2) / 2 :=
begin
  apply abs_le.mpr,
  split,
  { have h1 : 0 ≤ a^2 + 2*a*b + b^2,
      calc 0 ≤ (a+b)^2                : by exact pow_two_nonneg (a + b)
         ... = a^2+2*a*b+b^2          : by ring,
    have h2 : -2*(a*b) ≤ a^2 + b^2,
      calc -2*(a*b)
           ≤ -2*(a*b)+(a^2+2*a*b+b^2) : by exact le_add_of_nonneg_right h1
       ... = a^2 + b^2                : by ring,
    show -((a^2 + b^2) / 2) ≤ a*b,      by linarith [h2] },
  { have h3 : 0 ≤ a^2 - 2*a*b + b^2,
      calc 0 ≤ (a-b)^2                : by exact pow_two_nonneg (a - b)
         ... = a^2-2*a*b+b^2          : by ring,
    have h4 : 2*(a*b) ≤ a^2 + b^2,
      calc 2*(a*b)
           ≤ 2*(a*b)+(a^2-2*a*b+b^2)  : by exact le_add_of_nonneg_right h3
       ... = a^2 + b^2                : by ring,
    show a * b ≤ (a^2 + b^2)/2,         by linarith [h4] },
end

-- 2ª demostración
example : abs (a*b) ≤ (a^2 + b^2) / 2 :=
begin
  apply abs_le.mpr,
  split,
  { have h1 : 0 ≤ a^2 + 2*a*b + b^2,
      calc 0 ≤ (a+b)^2                : by exact pow_two_nonneg (a + b)
         ... = a^2+2*a*b+b^2          : by ring,
    have h2 : -2*(a*b) ≤ a^2 + b^2,
      calc -2*(a*b)
           ≤ -2*(a*b)+(a^2+2*a*b+b^2) : by exact le_add_of_nonneg_right h1
       ... = a^2 + b^2                : by ring,
    show -((a^2 + b^2) / 2) ≤ a*b,      by linarith [h2] },
  { have h4 : 2*a*b ≤ a^2 + b^2       := two_mul_le_add_sq a b,
    show a * b ≤ (a^2 + b^2)/2,         by linarith [h4] },
end

-- 3ª demostración
example : abs (a*b) ≤ (a^2 + b^2) / 2 :=
begin
  apply abs_le.mpr,
  split,
  { have h1 : 0 ≤ a^2 + 2*a*b + b^2,
      calc 0 ≤ (a+b)^2                : by exact pow_two_nonneg (a + b)
         ... = a^2+2*a*b+b^2          : by ring,
    have h2 : -2*(a*b) ≤ a^2 + b^2,
      calc -2*(a*b)
           ≤ -2*(a*b)+(a^2+2*a*b+b^2) : by exact le_add_of_nonneg_right h1
       ... = a^2 + b^2                : by ring,
    show -((a^2 + b^2) / 2) ≤ a*b,      by linarith [h2] },
  { show a * b ≤ (a^2 + b^2)/2,         by linarith [two_mul_le_add_sq a b] },
end
