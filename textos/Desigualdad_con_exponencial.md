---
Título: Si a, b, d ∈ ℝ tales que 1 ≤ a y b ≤ d, entonces 2 + a + eᵇ ≤ 3a + eᵈ
Autor:  José A. Alonso
---

Demostrar que si a, b, d ∈ ℝ tales que [latex]1 ≤ a[latex] y [latex]b ≤ d[latex], entonces
$$2 + a + e^b ≤ 3a + e^d$$

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import analysis.special_functions.log.basic
open real
variables a b d : ℝ

example
  (h  : 1 ≤ a)
  (h' : b ≤ d)
  : 2 + a + exp b ≤ 3 * a + exp d :=
sorry
</pre>

**Nota**: Se pueden usar los lemas
<pre lang="text">
add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d
exp_le_exp : exp a ≤ exp b ↔ a ≤ b
</pre>

<!--more-->
<b>Soluciones con Lean</b>

<pre lang="lean">
import analysis.special_functions.log.basic
open real
variables a b d : ℝ

-- 1ª demostración
-- ===============

example
  (h  : 1 ≤ a)
  (h' : b ≤ d)
  : 2 + a + exp b ≤ 3 * a + exp d :=
begin
  apply add_le_add,
  { calc 2 + a
         = (1 + 1) + a : by refl
     ... ≤ (1 + a) + a : by simp [h]
     ... ≤ (a + a) + a : by simp [h]
     ... = 3 * a       : by ring },
  { exact exp_le_exp.mpr h', },
end

-- 2ª demostración
-- ===============

example
  (h  : 1 ≤ a)
  (h' : b ≤ d)
  : 2 + a + exp b ≤ 3 * a + exp d :=
by linarith [exp_le_exp.mpr h']
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Desigualdad_con_exponencial.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.
