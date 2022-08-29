---
Título: Si R es un anillo y a, b, c ∈ R tales que a + b = a + c, entonces b = c.
Autor:  José A. Alonso
---

Demostrar que si R es un anillo y a, b, c ∈ R tales que
<pre lang="text">
   a + b = a + c
</pre>
entonces
<pre lang="text">
   b = c
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.ring
import tactic

variables {R : Type*} [ring R]
variables {a b c : R}

example
  (h : a + b = a + c)
  : b = c :=
sorry
</pre>

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.ring
import tactic

variables {R : Type*} [ring R]
variables {a b c : R}

-- 1ª demostración
-- ===============

example
  (h : a + b = a + c)
  : b = c :=
calc b
     = 0 + b        : by rw zero_add
 ... = (-a + a) + b : by rw add_left_neg
 ... = -a + (a + b) : by rw add_assoc
 ... = -a + (a + c) : by rw h
 ... = (-a + a) + c : by rw ←add_assoc
 ... = 0 + c        : by rw add_left_neg
 ... = c            : by rw zero_add

-- 2ª demostración
-- ===============

example
  (h : a + b = a + c)
  : b = c :=
calc b
     = 0 + b        : by simp
 ... = (-a + a) + b : by simp
 ... = -a + (a + b) : by simp
 ... = -a + (a + c) : by rw h
 ... = (-a + a) + c : by simp
 ... = 0 + c        : by simp
 ... = c            : by simp

-- 3ª demostración
-- ===============

lemma aux : -a + (a + b) = b :=
by finish

example
  (h : a + b = a + c)
  : b = c :=
calc b
     = -a + (a + b) : aux.symm
 ... = -a + (a + c) : congr_arg (λ x, -a + x) h
 ... = c            : aux

-- 4ª demostración
-- ===============

example
  (h : a + b = a + c)
  : b = c :=
-- by library_search
(add_right_inj a).mp h

-- 4ª demostración
-- ===============

example
  (h : a + b = a + c)
  : b = c :=
-- by hint
by finish
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Cancelativa_de_la_suma_por_la_izquierda.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.
