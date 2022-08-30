---
Título: Si R es un anillo y a ∈ R, entonces -(-a) = a
Autor:  José A. Alonso
---

Demostrar que si R es un anillo y a ∈ R, entonces
<pre lang="text">
-(-a) = a.
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]
variable a : R

example : -(-a) = a :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.ring

variables {R : Type*} [ring R]
variable a : R

-- 1ª demostración
-- ===============

example : -(-a) = a :=
begin
  calc -(-a)
       = -(0 - a) : congr_arg (λ x, -x) (zero_sub a).symm
   ... = a - 0    : neg_sub (0 : R) a
   ... = a        : sub_zero a
end

-- 2ª demostración
-- ===============

example : -(-a) = a :=
begin
  calc -(-a)
       = -(0 - a) : by { congr; rw zero_sub}
   ... = a - 0    : by rw neg_sub
   ... = a        : by rw sub_zero
end

-- 3ª demostración
-- ===============

example : -(-a) = a :=
by simpa only [zero_sub, sub_zero] using (neg_sub (0 : R) a)

-- 4ª demostración
-- ===============

example : -(-a) = a :=
neg_neg a

-- 5ª demostración
-- ===============

example : -(-a) = a :=
by simp

-- 6ª demostración
-- ===============

example : -(-a) = a :=
begin
  apply neg_eq_of_add_eq_zero_right,
  rw neg_add_self a,
end

-- 7ª demostración
-- ===============

example : -(-a) = a :=
neg_eq_of_add_eq_zero_right (neg_add_self a)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Opuesto_del_opuesto.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.
