-- Suma_divisible.lean
-- Si a divide a b y a c, entonces también divide a b + c.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 5-diciembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a divide a b y a c, entonces también divide a b + c.
-- ----------------------------------------------------------------------

import tactic

variables {a b c : ℕ}

-- 1ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
begin
  rcases divab with ⟨d, beq : b = a * d⟩,
  rcases divac with ⟨e, ceq: c = a * e⟩,
  have h1 : b + c = a * (d + e),
    calc b + c
         = (a * d) + c       : congr_arg (+ c) beq
     ... = (a * d) + (a * e) : congr_arg ((+) (a * d)) ceq
     ... = a * (d + e)       : by rw ← mul_add,
  show a ∣ (b + c),
    by exact dvd.intro (d + e) (eq.symm h1),
end

-- 2ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
begin
  rcases divab with ⟨d, beq : b = a * d⟩,
  rcases divac with ⟨e, ceq: c = a * e⟩,
  have h1 : b + c = a * (d + e), by linarith,
  show a ∣ (b + c),
    by exact dvd.intro (d + e) (eq.symm h1),
end

-- 3ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
begin
  rcases divab with ⟨d, beq : b = a * d⟩,
  rcases divac with ⟨e, ceq: c = a * e⟩,
  show a ∣ (b + c),
    by exact dvd.intro (d + e) (by linarith),
end

-- 4ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
begin
  cases divab with d beq,
  cases divac with e ceq,
  rw [ceq, beq],
  use (d + e),
  ring
end

-- 5ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
begin
  rcases divab with ⟨d, rfl⟩,
  rcases divac with ⟨e, rfl⟩,
  use (d + e),
  ring,
end
