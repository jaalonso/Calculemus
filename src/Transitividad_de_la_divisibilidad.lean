-- Transitividad_de_la_divisibilidad.lean
-- La relación de divisibilidad es transitiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 2-diciembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la relación de divisibilidad es transitiva.
-- ----------------------------------------------------------------------

import tactic

variables {a b c : ℕ}

-- 1ª demostración
-- ===============

example
  (hab : a ∣ b)
  (hbc : b ∣ c)
  : a ∣ c :=
begin
  rcases hab with ⟨d, hd : b = a * d⟩,
  rcases hbc with ⟨e, he : c = b * e⟩,
  have h1 : c = a * (d * e),
    calc c = b * e       : he
       ... = (a * d) * e : congr_arg (* e) hd
       ... = a * (d * e) : mul_assoc a d e,
  show a ∣ c,
    by exact dvd.intro (d * e) (eq.symm h1),
end

-- 2ª demostración
-- ===============

example
  (hab : a ∣ b)
  (hbc : b ∣ c)
  : a ∣ c :=
begin
  cases hab with d hd,
  cases hbc with e he,
  rw [he, hd],
  use (d * e),
  exact mul_assoc a d e,
end

-- 3ª demostración
-- ===============

example
  (hab : a ∣ b)
  (hbc : b ∣ c)
  : a ∣ c :=
begin
  rcases hbc with ⟨e, rfl⟩,
  rcases hab with ⟨d, rfl⟩,
  use (d * e),
  ring,
end

-- 4ª demostración
-- ===============

example
  (hab : a ∣ b)
  (hbc : b ∣ c)
  : a ∣ c :=
-- by library_search
dvd_trans hab hbc
