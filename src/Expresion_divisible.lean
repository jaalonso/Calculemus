-- Expresion_divisible.lean
-- Si w, x, y, z ∈ ℕ tales que x ∣ w, entonces x ∣ yxz + x² + w²
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-octubre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean w, x, y, z ∈ ℕ. Demostrar que si
--    x ∣ w
-- entonces
--    x ∣ y * (x * z) + x^2 + w^2
-- ----------------------------------------------------------------------

import data.nat.gcd

variables w x y z : ℕ

-- 1ª demostración
-- ===============

example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
begin
  have h1 : x ∣ x * z,
    by exact dvd.intro z rfl,
  have h2 : x ∣ y * (x * z),
    by exact dvd_mul_of_dvd_right h1 y,
  have h3 : x ∣ x^2,
    by apply dvd_mul_right,
  have h4 : x ∣ w * w,
    by exact dvd_mul_of_dvd_left h w,
  have h5 : x ∣ w^2,
    by rwa ← pow_two w at h4,
  have h6 : x ∣ y * (x * z) + x^2,
    by exact dvd_add h2 h3,
  show x ∣ y * (x * z) + x^2 + w^2,
    by exact dvd_add h6 h5,
end

-- 2ª demostración
-- ===============

example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
begin
  apply dvd_add,
  { apply dvd_add,
    { apply dvd_mul_of_dvd_right,
      apply dvd_mul_right, },
    { rw pow_two,
      apply dvd_mul_right, }},
  { rw pow_two,
    apply dvd_mul_of_dvd_left h, },
end
