---
Título: Si R es un anillo y a, b ∈ R, entonces -a + (a + b) = b
Autor:  José A. Alonso
---

En Lean, se declara que R es un anillo mediante la expresión
<pre lang="text">
   variables {R : Type*} [ring R]
</pre>
Como consecuencia, se tiene los siguientes axiomas
<pre lang="text">
   add_assoc    : ∀ a b c : R, (a + b) + c = a + (b + c)
   add_comm     : ∀ a b : R,   a + b = b + a
   zero_add     : ∀ a : R,     0 + a = a
   add_left_neg : ∀ a : R,     -a + a = 0
   mul_assoc    : ∀ a b c : R, a * b * c = a * (b * c)
   mul_one      : ∀ a : R,     a * 1 = a
   one_mul      : ∀ a : R,     1 * a = a
   mul_add      : ∀ a b c : R, a * (b + c) = a * b + a * c
   add_mul      : ∀ a b c : R, (a + b) * c = a * c + b * c
</pre>

Demostrar que si R es un anillo, entonces
<pre lang="text">
   ∀ a b : R, -a + (a + b) = b
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.ring
import tactic

variables {R : Type*} [ring R]
variables a b : R

example
  : -a + (a + b) = b :=
sorry
</pre>

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]
variables a b : R

-- 1ª demostración
example
  : -a + (a + b) = b :=
calc -a + (a + b)
     = (-a + a) + b : by rw ← add_assoc
 ... = 0 + b        : by rw add_left_neg
 ... = b            : by rw zero_add

-- 2ª demostración
example
  : -a + (a + b) = b :=
begin
  rw ←add_assoc,
  rw add_left_neg,
  rw zero_add,
end

-- 3ª demostración
example
  : -a + (a + b) = b :=
by rw [←add_assoc, add_left_neg, zero_add]

-- 4ª demostración
example
  : -a + (a + b) = b :=
-- by library_search
neg_add_cancel_left a b

-- 5ª demostración
example
  : -a + (a + b) = b :=
-- by hint
by finish
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Opuesto_se_cancela_con_la_suma_por_la_izquierda.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 11.
