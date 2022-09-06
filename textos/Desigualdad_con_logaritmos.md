---
Título: Si a, b ∈ ℝ tales que a ≤ b, entonces log(1 + eᵃ) ≤ log(1 + eᵇ).
Autor:  José A. Alonso
---

Demostrar que si a, b ∈ ℝ tales que a ≤ b, entonces log(1 + eᵃ) ≤ log(1 + eᵇ).

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import analysis.special_functions.log.basic
open real
variables a b : ℝ

example
  (h : a ≤ b)
  : log (1 + exp a) ≤ log (1 + exp b) :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import analysis.special_functions.log.basic
open real
variables a b : ℝ

-- 1ª demostración
-- ===============

example
  (h : a ≤ b)
  : log (1 + exp a) ≤ log (1 + exp b) :=
begin
  have h₀ : 0 < 1 + exp a,
  { apply add_pos,
    exact one_pos,
    apply exp_pos, },
  have h₁ : 0 < 1 + exp b,
  { apply add_pos,
    exact one_pos,
    apply exp_pos },
  apply (log_le_log h₀ h₁).mpr,
  apply add_le_add,
   apply le_refl,
  apply exp_le_exp.mpr h,
end

-- 2ª demostración
-- ===============

example
  (h : a ≤ b)
  : log (1 + exp a) ≤ log (1 + exp b) :=
begin
  have h₀ : 0 < 1 + exp a := add_pos one_pos (exp_pos a),
  have h₁ : 0 < 1 + exp b := add_pos one_pos (exp_pos b),
  exact (log_le_log h₀ h₁).mpr (add_le_add rfl.ge (exp_le_exp.mpr h))
end

-- 3ª demostración
-- ===============

lemma aux : 0 < 1 + exp a :=
add_pos one_pos (exp_pos a)

example
  (h : a ≤ b)
  : log (1 + exp a) ≤ log (1 + exp b) :=
begin
  have h₀ : 0 < 1 + exp a := aux a,
  have h₁ : 0 < 1 + exp b := aux b,
  exact (log_le_log h₀ h₁).mpr (add_le_add rfl.ge (exp_le_exp.mpr h))
end

-- 4ª demostración
-- ===============

example
  (h : a ≤ b)
  : log (1 + exp a) ≤ log (1 + exp b) :=
(log_le_log (aux a) (aux b)).mpr (add_le_add rfl.ge (exp_le_exp.mpr h))
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Desigualdad_con_logaritmos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.
