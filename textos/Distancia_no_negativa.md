---
Título: Si X es un espacio métrico y x, y ∈ X, entonces dist(x,y) ≥ 0
Autor:  José A. Alonso
---

Demostrar que si X es un espacio métrico y x, y ∈ X, entonces
<pre lang="text">
   0 ≤ dist x y
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import topology.metric_space.basic

variables {X : Type*} [metric_space X]
variables x y : X

example : 0 ≤ dist x y :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import topology.metric_space.basic

variables {X : Type*} [metric_space X]
variables x y : X

-- 1ª demostración
example : 0 ≤ dist x y :=
  have h1 : 2 * dist x y ≥ 0, by calc
    2 * dist x y = dist x y + dist x y : two_mul (dist x y)
             ... = dist x y + dist y x : by rw [dist_comm x y]
             ... ≥ dist x x            : dist_triangle x y x
             ... = 0                   : dist_self x,
  show 0 ≤ dist x y,
    by exact nonneg_of_mul_nonneg_left h1 zero_lt_two

-- 2ª demostración
example : 0 ≤ dist x y :=
-- by library_search
dist_nonneg
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Distancia_no_negativa.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 24.
