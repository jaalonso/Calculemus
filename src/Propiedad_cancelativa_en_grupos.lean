-- Propiedad_cancelativa_en_grupos.lean
-- Propiedad cancelativa en grupos
-- José A. Alonso Jiménez
-- Sevilla, 8 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sea G un grupo y a,b,c ∈ G. Demostrar que si a * b = a* c, entonces
-- b = c.
-- ---------------------------------------------------------------------

import algebra.group.basic

universe  u
variables {G : Type u} [group G]
variables {a b c : G}

-- 1ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = 1 * b         : (one_mul b).symm
   ... = (a⁻¹ * a) * b : congr_arg (* b) (inv_mul_self a).symm
   ... = a⁻¹ * (a * b) : mul_assoc a⁻¹ a b
   ... = a⁻¹ * (a * c) : congr_arg ((*) a⁻¹) h
   ... = (a⁻¹ * a) * c : (mul_assoc a⁻¹ a c).symm
   ... = 1 * c         : congr_arg (* c) (inv_mul_self a)
   ... = c             : one_mul c

-- 2ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = 1 * b         : by rw one_mul
   ... = (a⁻¹ * a) * b : by rw inv_mul_self
   ... = a⁻¹ * (a * b) : by rw mul_assoc
   ... = a⁻¹ * (a * c) : by rw h
   ... = (a⁻¹ * a) * c : by rw mul_assoc
   ... = 1 * c         : by rw inv_mul_self
   ... = c             : by rw one_mul

-- 3ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = 1 * b         : by simp
   ... = (a⁻¹ * a) * b : by simp
   ... = a⁻¹ * (a * b) : by simp
   ... = a⁻¹ * (a * c) : by simp [h]
   ... = (a⁻¹ * a) * c : by simp
   ... = 1 * c         : by simp
   ... = c             : by simp

-- 4ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
calc b = a⁻¹ * (a * b) : by simp
   ... = a⁻¹ * (a * c) : by simp [h]
   ... = c             : by simp

-- 4ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
begin
  have h1 : a⁻¹ * (a * b) = a⁻¹ * (a  * c),
    { by finish [h] },
  have h2 : (a⁻¹ * a) * b = (a⁻¹ * a)  * c,
    { by finish },
  have h3 : 1 * b = 1  * c,
    { by finish },
  have h3 : b = c,
    { by finish },
  exact h3,
end

-- 4ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
begin
  have : a⁻¹ * (a * b) = a⁻¹ * (a  * c),
    { by finish [h] },
  have h2 : (a⁻¹ * a) * b = (a⁻¹ * a)  * c,
    { by finish },
  have h3 : 1 * b = 1  * c,
    { by finish },
  have h3 : b = c,
    { by finish },
  exact h3,
end

-- 4ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
begin
  have h1 : a⁻¹ * (a * b) = a⁻¹ * (a  * c),
    { congr, exact h, },
  have h2 : (a⁻¹ * a) * b = (a⁻¹ * a)  * c,
    { simp only [h1, mul_assoc], },
  have h3 : 1 * b = 1  * c,
    { simp only [h2, (inv_mul_self a).symm], },
  rw one_mul at h3,
  rw one_mul at h3,
  exact h3,
end

-- 5ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
mul_left_cancel h

-- 6ª demostración
-- ===============

example
  (h: a * b = a  * c)
  : b = c :=
by finish

-- Referencias
-- ===========

-- Propiedad 3.22 del libro "Abstract algebra: Theory and applications"
-- de Thomas W. Judson.
-- http://abstract.ups.edu/download/aata-20200730.pdf
