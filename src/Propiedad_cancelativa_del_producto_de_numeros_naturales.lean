-- Propiedad_cancelativa_del_producto_de_numeros_naturales.lean
-- Propiedad cancelativa del producto de números naturales
-- José A. Alonso Jiménez
-- Sevilla, 28 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean k, m, n números naturales. Demostrar que
--    k * m = k * n ↔ m = n ∨ k = 0
-- ---------------------------------------------------------------------

import data.nat.basic
open nat

variables {k m n : ℕ}

-- Para que no use la notación con puntos
set_option pp.structure_projections false

-- 1ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
begin
  have h1: k ≠ 0 → k * m = k * n → m = n,
    { induction n with n HI generalizing m,
      { by finish, },
      { cases m,
        { by finish, },
        { intros hk hS,
          congr,
          apply HI hk,
          rw mul_succ at hS,
          rw mul_succ at hS,
          exact add_right_cancel hS, }}},
  by finish,
end

-- 2ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
begin
  have h1: k ≠ 0 → k * m = k * n → m = n,
    { induction n with n HI generalizing m,
      { by finish, },
      { cases m,
        { by finish, },
        { intros hk hS,
          congr,
          apply HI hk,
          simp only [mul_succ] at hS,
          exact add_right_cancel hS, }}},
  by finish,
end

-- 3ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
begin
  have h1: k ≠ 0 → k * m = k * n → m = n,
    { induction n with n HI generalizing m,
      { by finish, },
      { cases m,
        { by finish, },
        { by finish, }}},
  by finish,
end

-- 4ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
begin
  have h1: k ≠ 0 → k * m = k * n → m = n,
    { induction n with n HI generalizing m,
      { by finish, },
      { cases m; by finish }},
  by finish,
end

-- 5ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
begin
  have h1: k ≠ 0 → k * m = k * n → m = n,
    { induction n with n HI generalizing m ; by finish },
  by finish,
end

-- 5ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
begin
  by_cases hk : k = 0,
  { by simp, },
  { rw mul_right_inj' hk,
    by tauto, },
end

-- 6ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
mul_eq_mul_left_iff

-- 7ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
by simp
