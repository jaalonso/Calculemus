---
Título: La relación de divisibilidad es transitiva
Autor:  José A. Alonso
---

Demostrar que la relación de divisibilidad es transitiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variables {a b c : ℕ}

example
  (hab : a ∣ b)
  (hbc : b ∣ c)
  : a ∣ c :=
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
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Transitividad_de_la_divisibilidad.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 32.
