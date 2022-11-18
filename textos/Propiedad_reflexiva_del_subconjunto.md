---
Título: Para cualquier conjunto s, s ⊆ s
Autor:  José A. Alonso
---

Demostrar que, para cualquier conjunto s, s ⊆ s

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
variables {α : Type*} (s : set α)

example : s ⊆ s :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import tactic
variables {α : Type*} (s : set α)

-- 1ª demostración
-- ===============

example : s ⊆ s :=
begin
  assume x,
  assume xs: x ∈ s,
  show x ∈ s,
    by exact xs,
end

-- 2ª demostración
-- ===============

example : s ⊆ s :=
begin
  intros x xs,
  exact xs,
end

-- 3ª demostración
-- ===============

example : s ⊆ s :=
λ x (xs : x ∈ s), xs

-- 4ª demostración
-- ===============

example : s ⊆ s :=
-- by library_search
rfl.subset

-- 5ª demostración
-- ===============

example : s ⊆ s :=
-- by hint
by refl
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Propiedad_reflexiva_del_subconjunto.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 29.
