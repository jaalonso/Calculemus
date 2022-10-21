---
Título: Si R es un anillo ordenado, entonces ∀ a b ∈ R, a ≤ b → 0 ≤ b - a
Autor:  José A. Alonso
---

Demostrar que Si R es un anillo ordenado y a b ∈ R, enonces
<pre lang="text">
   a ≤ b → 0 ≤ b - a
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.order.ring
variables {R : Type*} [ordered_ring R]
variables a b : R

example : a ≤ b → 0 ≤ b - a :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.order.ring
variables {R : Type*} [ordered_ring R]
variables a b : R

-- 1ª demostración
-- ===============

example : a ≤ b → 0 ≤ b - a :=
begin
  intro h,
  calc
    0   = a - a : (sub_self a).symm
    ... ≤ b - a : sub_le_sub_right h a
end

-- 2ª demostración
-- ===============

example : a ≤ b → 0 ≤ b - a :=
-- by library_search
sub_nonneg.mpr

-- 3ª demostración
-- ===============

example : a ≤ b → 0 ≤ b - a :=
-- by hint
by simp
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Si_es_menor_o_igual_entonces_la_diferencia_es_positiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 23.
