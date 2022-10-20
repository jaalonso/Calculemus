---
Título: Si R es un retículo y x, y, z ∈ R, entonces (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z)
Autor:  José A. Alonso
---

Demostrar que si R es un retículo y x, y, z ∈ R, entonces
<pre lang="text">
(x ⊔ y) ⊔ z = x ⊔ (y ⊔ z)
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import order.lattice

variables {R : Type*} [lattice R]
variables x y z : R

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
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

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
begin
  have h1 : (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z),
    { have h1a : x ⊔ y ≤ x ⊔ (y ⊔ z), by finish,
      have h1b : z ≤ x ⊔ (y ⊔ z), by finish,
      show (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z),
        by exact sup_le h1a h1b, },
  have h2 : x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z,
    { have h2a : x ≤ (x ⊔ y) ⊔ z, by finish,
      have h2b : y ⊔ z ≤ (x ⊔ y) ⊔ z, by finish,
      show x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z,
        by exact sup_le h2a h2b, },
  show (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z),
    by exact le_antisymm h1 h2,
end

-- 2ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
begin
  have h1 : (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z),
    { have h1a : x ⊔ y ≤ x ⊔ (y ⊔ z),
        { have h1a1 : x ≤ x ⊔ (y ⊔ z) :=
            le_sup_left,
          have h1a2 : y ≤ x ⊔ (y ⊔ z), calc
            y ≤ y ⊔ z         : le_sup_left
            ... ≤ x ⊔ (y ⊔ z) : le_sup_right,
          show x ⊔ y ≤ x ⊔ (y ⊔ z),
            by exact sup_le h1a1 h1a2, },
      have h1b : z ≤ x ⊔ (y ⊔ z), calc
        z   ≤ y ⊔ z       : le_sup_right
        ... ≤ x ⊔ (y ⊔ z) : le_sup_right,
      show (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z),
        by exact sup_le h1a h1b, },
  have h2 : x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z,
    { have h2a : x ≤ (x ⊔ y) ⊔ z, calc
        x   ≤ x ⊔ y       : le_sup_left
        ... ≤ (x ⊔ y) ⊔ z : le_sup_left,
      have h2b : y ⊔ z ≤ (x ⊔ y) ⊔ z,
        { have h2b1 : y ≤ (x ⊔ y) ⊔ z, calc
            y   ≤ x ⊔ y       : le_sup_right
            ... ≤ (x ⊔ y) ⊔ z : le_sup_left,
          have h2b2 : z ≤ (x ⊔ y) ⊔ z :=
            le_sup_right,
          show y ⊔ z ≤ (x ⊔ y) ⊔ z,
            by exact sup_le h2b1 h2b2, },
      show x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z,
        by exact sup_le h2a h2b, },
  show (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z),
    by exact le_antisymm h1 h2,
end

-- 3ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
begin
  apply le_antisymm,
  { apply sup_le,
    { apply sup_le le_sup_left (le_sup_of_le_right le_sup_left)},
    { apply le_sup_of_le_right le_sup_right}},
  { apply sup_le,
    { apply le_sup_of_le_left le_sup_left},
    { apply sup_le (le_sup_of_le_left le_sup_right) le_sup_right}},
end

-- 4ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
le_antisymm
  (sup_le
    (sup_le le_sup_left (le_sup_of_le_right le_sup_left))
    (le_sup_of_le_right le_sup_right))
  (sup_le
    (le_sup_of_le_left le_sup_left)
    (sup_le (le_sup_of_le_left le_sup_right) le_sup_right))

-- 5ª demostración
-- ===============

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) :=
-- by library_search
sup_assoc

-- 6ª demostración
-- ===============

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) :=
-- by hint
by finish
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Asociatividad_del_supremo.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 22.
