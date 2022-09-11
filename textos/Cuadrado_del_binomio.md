---
Título: Cuadrado del binomio.
Autor:  José A. Alonso
---

Demostrar que si a y b son números reales, entonces
<pre lang="text">
(a + b) * (a + b) = a * a + 2 * (a * b) + b * b
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables a b : ℝ

example :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
sorry
</pre>

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

variables a b : ℝ

-- 1ª demostración
-- ===============

example :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = (a + b) * a + (a + b) * b       : by rw mul_add
  ... = a * a + b * a + (a + b) * b     : by rw add_mul
  ... = a * a + b * a + (a * b + b * b) : by rw add_mul
  ... = a * a + b * a + a * b + b * b   : by rw ← add_assoc
  ... = a * a + (b * a + a * b) + b * b : by rw add_assoc (a * a)
  ... = a * a + (a * b + a * b) + b * b : by rw mul_comm b a
  ... = a * a + 2 * (a * b) + b * b     : by rw ← two_mul

-- 2ª demostración
-- ===============

example :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) : by rw [mul_add, add_mul, add_mul]
  ... = a * a + (b * a + a * b) + b * b : by rw [←add_assoc, add_assoc (a * a)]
  ... = a * a + 2 * (a * b) + b * b     : by rw [mul_comm b a, ←two_mul]

-- 3ª demostración
-- ===============

example :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) : by ring
  ... = a * a + (b * a + a * b) + b * b : by ring
  ... = a * a + 2 * (a * b) + b * b     : by ring

-- 4ª demostración
-- ===============

example :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by ring

-- 5ª demostración
-- ===============

example :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
begin
  rw mul_add,
  rw add_mul,
  rw add_mul,
  rw ← add_assoc,
  rw add_assoc (a * a),
  rw mul_comm b a,
  rw ← two_mul,
end

-- 6ª demostración
-- ===============

example :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
begin
  rw [mul_add, add_mul, add_mul],
  rw [←add_assoc, add_assoc (a * a)],
  rw [mul_comm b a, ←two_mul],
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Cuadrado_del_binomio.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 8.
