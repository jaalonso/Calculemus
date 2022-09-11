---
Título: Si R es un anillo y a, b ∈ R, entonces (a + b) + -b = a
Autor:  José A. Alonso
---

Demostrar que si R es un anillo, entonces
<pre lang="text">
   ∀ a b : R, (a + b) + -b = a
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]
variables a b : R

example : (a + b) + -b = a :=
sorry
</pre>

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]
variables a b : R

-- 1ª demostración
-- ===============

example : (a + b) + -b = a :=
calc (a + b) + -b
     = a + (b + -b) : by rw add_assoc
 ... = a + 0        : by rw add_right_neg
 ... = a            : by rw add_zero

-- 2ª demostración
-- ===============

example : (a + b) + -b = a :=
begin
  rw add_assoc,
  rw add_right_neg,
  rw add_zero,
end

-- 3ª demostración
-- ===============

example : (a + b) + -b = a :=
by rw [add_assoc, add_right_neg, add_zero]

-- 4ª demostración
-- ===============

example : (a + b) + -b = a :=
-- by library_search
add_neg_eq_of_eq_add rfl

-- 5ª demostración
-- ===============

example : (a + b) + -b = a :=
-- by hint
by finish
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Opuesto_se_cancela_con_la_suma_por_la_derecha.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 15.
