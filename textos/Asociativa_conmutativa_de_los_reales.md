---
Título: Asociativa conmutativa de los reales.
Autor:  José A. Alonso
---

Demostrar que los números reales tienen la siguente propiedad
<pre lang="text">
(a * b) * c = b * (a * c)
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables a b c : ℝ

example : (a * b) * c = b * (a * c) :=
sorry
</pre>

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

variables a b c : ℝ

-- 1ª demostración
-- ===============

example : (a * b) * c = b * (a * c) :=
begin
  rw mul_comm a b,
  rw mul_assoc b a c,
end

-- 2ª demostración
-- ===============

example : (a * b) * c = b * (a * c) :=
calc (a * b) * c
     = (b * a) * c : by rw mul_comm a b
 ... = b * (a * c) : by rw mul_assoc b a c

-- 3ª demostración
-- ===============

example : (a * b) * c = b * (a * c) :=
calc (a * b) * c
     = (b * a) * c : by ring
 ... = b * (a * c) : by ring

-- 4ª demostración
-- ===============

example : (a * b) * c = b * (a * c) :=
by ring
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Asociativa_conmutativa_de_los_reales.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
