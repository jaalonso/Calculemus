---
Título: Si R es un anillo ordenado y a, b, c ∈ R tales que a ≤ b y 0 ≤ c, entonces a * c ≤ b * c
Autor:  José A. Alonso
---

Demostrar que si R es un anillo ordenado y a, b, c ∈ R tales que
<pre lang="text">
   a ≤ b y
   0 ≤ c
</pre>
entonces
<pre lang="text">
a * c ≤ b * c
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.order.ring
variables {R : Type*} [ordered_ring R]
variables a b c: R

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
sorry
</pre>

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.order.ring
variables {R : Type*} [ordered_ring R]
variables a b c: R

-- 1ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
begin
  have h3 : 0 ≤ b - a :=
    sub_nonneg.mpr h1,
  have h4 : 0 ≤ (b - a) * c :=
    mul_nonneg h3 h2,
  have h5 : (b - a) * c = b * c - a * c :=
    sub_mul b a c,
  have h6 : 0 ≤ b * c - a * c :=
    eq.trans_ge h5 h4,
  show a * c ≤ b * c,
    by exact sub_nonneg.mp h6,
end

-- 2ª demostración
-- ===============

open_locale classical

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
begin
  by_cases h3 : b ≤ a,
  { have h3a : a = b :=
      le_antisymm h1 h3,
    show a * c ≤ b * c,
      by rw h3a },
  { by_cases h4 : c = 0,
    { calc a * c = a * 0 : by rw h4
             ... = 0     : by rw mul_zero
             ... ≤ 0     : le_refl 0
             ... = b * 0 : by rw mul_zero
             ... = b * c : by {congr ; rw h4}},
    { apply le_of_lt,
      apply mul_lt_mul_of_pos_right,
      { show a < b,
          by exact lt_of_le_not_le h1 h3 },
      { show 0 < c,
          by exact lt_of_le_of_ne h2 (ne.symm h4) }}},
end

-- 3ª demostración
example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
-- by library_search
mul_le_mul_of_nonneg_right h1 h2
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Producto_desigualdad_por_no_negativo.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

<b>Referencias</b>

+ J. Avigad, K. Buzzard, R.Y. Lewis y P. Massot. [Mathematics in Lean](https://bit.ly/3U4UjBk), p. 23.
