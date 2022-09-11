---
Título: Producto de dos binomios
Autor:  José A. Alonso
---

Demostrar que si a, b, c y d son números reales, entonces
<pre lang="text">
(a + b) * (c + d) = a * c + a * d + b * c + b * d
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables a b c d : ℝ

example
  : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
sorry
</pre>

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

variables a b c d : ℝ

-- 1ª demostración
-- ===============

example
  : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
calc
  (a + b) * (c + d)
      = a * (c + d) + b * (c + d)       : by rw add_mul
  ... = a * c + a * d + b * (c + d)     : by rw mul_add
  ... = a * c + a * d + (b * c + b * d) : by rw mul_add
  ... = a * c + a * d + b * c + b * d   : by rw ←add_assoc

-- 2ª demostración
-- ===============

example
  : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
calc
  (a + b) * (c + d)
      = a * (c + d) + b * (c + d)       : by ring
  ... = a * c + a * d + b * (c + d)     : by ring
  ... = a * c + a * d + (b * c + b * d) : by ring
  ... = a * c + a * d + b * c + b * d   : by ring

-- 3ª demostración
-- ===============

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
by ring

-- 4ª demostración
-- ===============

example
  : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
begin
   rw add_mul,
   rw mul_add,
   rw mul_add,
   rw ← add_assoc,
end

-- 5ª demostración
-- ===============

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
by rw [add_mul, mul_add, mul_add, ←add_assoc]
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Producto_de_dos_binomios.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 8.
