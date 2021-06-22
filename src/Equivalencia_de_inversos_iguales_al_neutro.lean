-- Equivalencia_de_inversos_iguales_al_neutro.lean
-- Equivalencia de inversos iguales al neutro
-- José A. Alonso Jiménez
-- Sevilla, 1 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea M un monoide y a, b ∈ M tales que a * b = 1. Demostrar que a = 1
-- si y sólo si b = 1.
-- ---------------------------------------------------------------------

import algebra.group.basic

variables {M : Type} [monoid M]
variables {a b : M}

-- 1ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
begin
  split,
  { intro a1,
    rw a1 at h,
    rw one_mul at h,
    exact h, },
  { intro b1,
    rw b1 at h,
    rw mul_one at h,
    exact h, },
end

-- 2ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
begin
  split,
  { intro a1,
    calc b = 1 * b : (one_mul b).symm
       ... = a * b : congr_arg (* b) a1.symm
       ... = 1     : h, },
  { intro b1,
    calc a = a * 1 : (mul_one a).symm
       ... = a * b : congr_arg ((*) a) b1.symm
       ... = 1     : h, },
end

-- 3ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
begin
  split,
  { rintro rfl,
    simpa using h, },
  { rintro rfl,
    simpa using h, },
end

-- 4ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by split ; { rintro rfl, simpa using h }

-- 5ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by split ; finish

-- 6ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by finish [iff_def]

-- 7ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
eq_one_iff_eq_one_of_mul_eq_one h
