---
Título: Si a divide a b y a c, entonces tambien divide a b + c.
Autor:  José A. Alonso
---

Demostrar que si a divide a b y a c, entonces tambien divide a b + c.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variables {a b c : ℕ}

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
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
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_divisible.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 33.
