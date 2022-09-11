---
Título: Identidad condicional en los reales.
Autor:  José A. Alonso
---

Demostrar que si a, b, c, d, e y f son números reales tales que
<pre lang="text">
   a * b = c * d
   e = f
</pre>
Entonces,
<pre lang="text">
   a * (b * e) = c * (d * f)
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables a b c d e f : ℝ

example
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
</pre>

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

variables a b c d e f : ℝ

-- 1ª demostración
example
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
begin
  rw h2,
  rw ←mul_assoc,
  rw h1,
  rw mul_assoc,
end

-- 2ª demostración
example
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
calc a * (b * e)
     = a * (b * f) : by rw h2
 ... = (a * b) * f : by rw ←mul_assoc
 ... = (c * d) * f : by rw h1
 ... = c * (d * f) : by rw mul_assoc

-- 3ª demostración
example
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
calc a * (b * e)
     = a * (b * f) : by rw h2
 ... = (a * b) * f : by ring
 ... = (c * d) * f : by rw h1
 ... = c * (d * f) : by ring

-- 4ª demostración
example
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
by finish
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Identidad_condicional_en_los_reales.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 6.
