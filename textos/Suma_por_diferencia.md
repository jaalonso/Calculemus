---
Título: Suma por diferencia.
Autor:  José A. Alonso
---

Demostrar que si a y b son números reales, entonces
<pre lang="text">
(a + b) * (a - b) = a^2 - b^2
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables a b c d : ℝ

example : (a + b) * (a - b) = a^2 - b^2 :=
sorry
</pre>

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

variables a b c d : ℝ

-- 1ª demostración
example : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
      = a * (a - b) + b * (a - b)         : by rw add_mul
  ... = (a * a - a * b) + b * (a - b)     : by rw mul_sub
  ... = (a^2 - a * b) + b * (a - b)       : by rw ← pow_two
  ... = (a^2 - a * b) + (b * a - b * b)   : by rw mul_sub
  ... = (a^2 - a * b) + (b * a - b^2)     : by rw ← pow_two
  ... = (a^2 + -(a * b)) + (b * a - b^2)  : by ring
  ... = a^2 + (-(a * b) + (b * a - b^2))  : by rw add_assoc
  ... = a^2 + (-(a * b) + (b * a + -b^2)) : by ring
  ... = a^2 + ((-(a * b) + b * a) + -b^2) : by rw ← add_assoc
                                               (-(a * b)) (b * a) (-b^2)
  ... = a^2 + ((-(a * b) + a * b) + -b^2) : by rw mul_comm
  ... = a^2 + (0 + -b^2)                  : by rw neg_add_self (a * b)
  ... = (a^2 + 0) + -b^2                  : by rw ← add_assoc
  ... = a^2 + -b^2                        : by rw add_zero
  ... = a^2 - b^2                         : by linarith


-- 2ª demostración
example : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
      = a * (a - b) + b * (a - b)         : by ring
  ... = (a * a - a * b) + b * (a - b)     : by ring
  ... = (a^2 - a * b) + b * (a - b)       : by ring
  ... = (a^2 - a * b) + (b * a - b * b)   : by ring
  ... = (a^2 - a * b) + (b * a - b^2)     : by ring
  ... = (a^2 + -(a * b)) + (b * a - b^2)  : by ring
  ... = a^2 + (-(a * b) + (b * a - b^2))  : by ring
  ... = a^2 + (-(a * b) + (b * a + -b^2)) : by ring
  ... = a^2 + ((-(a * b) + b * a) + -b^2) : by ring
  ... = a^2 + ((-(a * b) + a * b) + -b^2) : by ring
  ... = a^2 + (0 + -b^2)                  : by ring
  ... = (a^2 + 0) + -b^2                  : by ring
  ... = a^2 + -b^2                        : by ring
  ... = a^2 - b^2                         : by ring

-- 3ª demostración
example : (a + b) * (a - b) = a^2 - b^2 :=
by ring
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_por_diferencia.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
