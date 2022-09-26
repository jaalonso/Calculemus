-- Divisivilidad_productos.lean
-- Si x, y, z ∈ ℕ, entonces x ∣ y * x * z
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-octubre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si x, y, z ∈ N, entonces
--    x ∣ y * x * z
-- ----------------------------------------------------------------------

import data.nat.basic
variables x y z : ℕ

-- 1ª demostración
-- ===============

example : x ∣ y * x * z :=
begin
  have h1 : x ∣ y * x,
    { exact dvd_mul_left x y },
  have h2 : (y * x) ∣ (y * x * z),
    { exact dvd.intro z rfl},
  show x ∣ y * x * z,
    { exact dvd_trans h1 h2},
end

-- 2ª demostración
-- ===============

example : x ∣ y * x * z :=
dvd_trans (dvd_mul_left x y) (dvd.intro z rfl)

-- 3ª demostración
-- ===============

example : x ∣ y * x * z :=
begin
  apply dvd_mul_of_dvd_left,
  apply dvd_mul_left
end
