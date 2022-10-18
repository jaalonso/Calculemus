---
Título: Si R es un retículo y x, y, z ∈ R, entonces (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z)
Autor:  José A. Alonso
---

Demostrar que si R es un retículo y x, y, z ∈ R, entonces
<pre lang="text">
(x ⊓ y) ⊓ z = x ⊓ (y ⊓ z)
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import order.lattice

variables {R : Type*} [lattice R]
variables x y z : R

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import order.lattice

variables {R : Type*} [lattice R]
variables x y z : R

-- 1ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
begin
  have h1 : (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z),
    { have h1a : (x ⊓ y) ⊓ z ≤ x, calc
        (x ⊓ y) ⊓ z ≤ x ⊓ y : inf_le_left
                ... ≤ x     : inf_le_left,
      have h1b : (x ⊓ y) ⊓ z ≤ y ⊓ z,
        { have h1b1 : (x ⊓ y) ⊓ z ≤ y, calc
            (x ⊓ y) ⊓ z ≤ x ⊓ y : inf_le_left
                    ... ≤ y     : inf_le_right,
          have h1b2 : (x ⊓ y) ⊓ z ≤ z :=
            inf_le_right,
          show (x ⊓ y) ⊓ z ≤ y ⊓ z,
            by exact le_inf h1b1 h1b2, },
      show (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z),
        by exact le_inf h1a h1b, },
  have h2 : x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z,
    { have h2a : x ⊓ (y ⊓ z) ≤ x ⊓ y,
        { have h2a1 : x ⊓ (y ⊓ z) ≤ x,
            by exact inf_le_left,
          have h2a2 : x ⊓ (y ⊓ z) ≤ y, calc
            x ⊓ (y ⊓ z) ≤ y ⊓ z : inf_le_right
                    ... ≤ y     : inf_le_left,
          show x ⊓ (y ⊓ z) ≤ x ⊓ y,
            by exact le_inf h2a1 h2a2, },
      have h2b : x ⊓ (y ⊓ z) ≤ z, calc
        x ⊓ (y ⊓ z) ≤ y ⊓ z : inf_le_right
                ... ≤ z     : inf_le_right,
      show x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z,
        by exact le_inf h2a h2b, },
  show (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z),
    by exact le_antisymm h1 h2,
end

-- 2ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
begin
  apply le_antisymm,
  { apply le_inf,
    { apply inf_le_of_left_le inf_le_left, },
    { apply le_inf (inf_le_of_left_le inf_le_right) inf_le_right}},
  {apply le_inf,
    { apply le_inf inf_le_left (inf_le_of_right_le inf_le_left), },
    { apply inf_le_of_right_le inf_le_right, },},
end

-- 3ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
le_antisymm
  (le_inf
    (inf_le_of_left_le inf_le_left)
    (le_inf (inf_le_of_left_le inf_le_right) inf_le_right))
  (le_inf
    (le_inf inf_le_left (inf_le_of_right_le inf_le_left))
    (inf_le_of_right_le inf_le_right))

-- 4ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
-- by library_search
inf_assoc

-- 5ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
-- by hint
by finish
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Asociatividad_del_infimo.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 22.
