---
Título: Si a, b, c, d, f ∈ ℝ tales que a ≤ b y c < d, entonces a + eᶜ + f < b + eᵈ + f
Autor:  José A. Alonso
---

Demostrar que si a, b, c, d, f ∈ ℝ tales que
<pre lang="text">
a ≤ b
c < d
</pre>
entonces
<pre lang="text">
a + eᶜ + f < b + eᵈ + f
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import analysis.special_functions.log.basic
open real
variables a b c d f : ℝ

example
  (hab : a ≤ b)
  (hcd : c < d)
  : a + exp c + f < b + exp d + f :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import analysis.special_functions.log.basic
open real
variables a b c d f : ℝ

-- 1ª demostración
-- ===============

example
  (hab : a ≤ b)
  (hcd : c < d)
  : a + exp c + f < b + exp d + f :=
begin
  apply add_lt_add_of_lt_of_le,
  { apply add_lt_add_of_le_of_lt,
    { exact hab, },
    { apply exp_lt_exp.mpr,
      exact hcd, }},
  { apply le_refl, },
end

-- 3ª demostración
-- ===============

example
  (hab : a ≤ b)
  (hcd : c < d)
  : a + exp c + f < b + exp d + f :=
begin
  apply add_lt_add_of_lt_of_le,
  { apply add_lt_add_of_le_of_lt hab (exp_lt_exp.mpr hcd), },
  { refl, },
end

-- 4ª demostración
-- ===============

example
  (hab : a ≤ b)
  (hcd : c < d)
  : a + exp c + f < b + exp d + f :=
add_lt_add_of_lt_of_le
  (add_lt_add_of_le_of_lt hab (exp_lt_exp.mpr hcd))
  (le_refl f)

-- 5ª demostración
-- ===============

example
  (hab : a ≤ b)
  (hcd : c < d)
  : a + exp c + f < b + exp d + f :=
by linarith [exp_lt_exp.mpr hcd]
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Desigualdad_con_exponencial_2.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.
