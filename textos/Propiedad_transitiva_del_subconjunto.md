---
Título: Si r ⊆ s y s ⊆ t, entonces r ⊆ t.
Autor:  José A. Alonso
---

Demostrar que si r ⊆ s y s ⊆ t, entonces r ⊆ t.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variables {α : Type*}
variables r s t : set α

example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Propiedad_transitiva_del_subconjunto.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 29.
