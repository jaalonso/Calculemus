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
import tactic

variables {α : Type*}
variables r s t : set α

-- 1ª demostración
-- ===============

example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
begin
  assume x,
  assume xr : x ∈ r,
  have h1 : x ∈ s := rs xr,
  show x ∈ t,
    by exact st h1,
end

-- 2ª demostración
-- ===============

example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
begin
  intros x xr,
  apply st,
  apply rs,
  exact xr
end

-- El desarrollo es
--
-- α : Type u_1,
-- r s t : set α
-- ⊢ r ⊆ s → s ⊆ t → r ⊆ t
--    >> intros rs st x xr,
-- rs : r ⊆ s,
-- st : s ⊆ t,
-- x : α,
-- xr : x ∈ r
-- ⊢ x ∈ t
--    >> apply st,
-- ⊢ x ∈ s
--    >> apply rs,
-- ⊢ x ∈ r
--    >> exact xr
-- no goals

-- 3ª demostración
-- ===============

example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
λ x xr, st (rs xr)

-- 4ª demostración
-- ===============

example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
-- by library_search
set.subset.trans rs st

-- 5ª demostración
-- ===============

example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
-- by hint
by tauto
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Propiedad_transitiva_del_subconjunto.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 29.
