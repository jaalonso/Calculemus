---
Título: Si a, b ∈ ℝ, entonces |a| - |b| ≤ |a - b|
Autor:  José A. Alonso
---

Sean a y b números reales. Demostrar que
<pre lang="text">
   |a| - |b| ≤ |a - b|
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables a b : ℝ

example : |a| - |b| ≤ |a - b| :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import data.real.basic

variables a b : ℝ

example : |a| - |b| ≤ |a - b| :=
calc |a| - |b|
     = |a - b + b| - |b|     : by simp
 ... ≤ (|a - b| + |b|) - |b| : sub_le_sub_right (abs_add (a - b) b) (|b|)
 ... = |a - b|               : add_sub_cancel (|a - b|) (|b|)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/absoluto_resta.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 20.
