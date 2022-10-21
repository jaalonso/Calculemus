---
Título: Si R es un anillo ordenado y a b ∈ R, entonces 0 ≤ b - a → a ≤ b
Autor:  José A. Alonso
---

Demostrar que si R es un anillo ordenado y a b ∈ R, entonces
<pre lang="text">
   0 ≤ b - a → a ≤ b
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.order.ring
variables {R : Type*} [ordered_ring R]
variables a b : R

example : 0 ≤ b - a → a ≤ b :=
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

example : 0 ≤ b - a → a ≤ b :=
begin
  intro h,
  calc
    a   = 0 + a       : (zero_add a).symm
    ... ≤ (b - a) + a : add_le_add_right h a
    ... = b           : sub_add_cancel b a
end

-- 2ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
-- by library_search
sub_nonneg.mp

-- 3ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
-- by hint
by simp
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/CN_de_diferencia_no_negativa.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 23.
