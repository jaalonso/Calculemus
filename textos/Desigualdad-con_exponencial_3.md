---
Título: Si a, b, c ∈ ℝ tales que a ≤ b, entonces c - eᵇ ≤ c - eᵃ
Autor:  José A. Alonso
---

Demostrar que si a, b, c ∈ ℝ tales que a ≤ b, entonces c - eᵇ ≤ c - eᵃ.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import analysis.special_functions.log.basic
import tactic
open real
variables a b c : ℝ

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import analysis.special_functions.log.basic
import tactic
open real
variables a b c : ℝ

-- 1ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
begin
   apply sub_le_sub_left _ c,
   exact exp_le_exp.mpr h,
end

-- 2ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
sub_le_sub_left (exp_le_exp.mpr h) c

-- 3ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - b ≤ c - a :=
-- by library_search
sub_le_sub_left h c

-- 4ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
by linarith [exp_le_exp.mpr h]

-- 5ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
-- by hint
by finish
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Desigualdad-con_exponencial_3.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.
