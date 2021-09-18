---
Título: Prueba de (1+p)^n ≥ 1+np
Autor:  José A. Alonso
---

Sean p ∈ ℝ y n ∈ ℕ tales que p > -1. Demostrar que
<pre lang="text">
   (1 + p)^n ≥ 1 + n*p
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
open nat

variable (p : ℝ)
variable (n : ℕ)

example
  (h : p > -1)
  : (1 + p)^n ≥ 1 + n*p :=
begin
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
open nat

variable (p : ℝ)
variable (n : ℕ)

set_option pp.structure_projections false

example
  (h : p > -1)
  : (1 + p)^n ≥ 1 + n*p :=
begin
  induction n with n HI,
  { simp, },
  { have h1 : 1 + p > 0 := iff.mp neg_lt_iff_pos_add' h,
    have h2 : p*p ≥ 0 := mul_self_nonneg p,
    replace h2 : ↑n*(p*p) ≥ 0 := mul_nonneg (cast_nonneg n) h2,
    calc (1 + p)^succ n
         = (1 + p)^n * (1 + p)
             : pow_succ' (1 + p) n
     ... ≥ (1 + n * p) * (1 + p)
             : (mul_le_mul_right h1).mpr HI
     ... = (1 + p + n*p) + n*(p*p)
             : by ring !
     ... ≥ 1 + p + n*p
             : le_add_of_nonneg_right h2
     ... = 1 + (n + 1) * p
             : by ring !
     ... = 1 + ↑(succ n) * p
             : by norm_num },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Prueba_de_(1+p)^n_mayor_o_igual_que_1+np.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory "Prueba_de_(1+p)^n_mayor_o_igual_que_1+np"
imports Main HOL.Real
begin

lemma
  fixes p :: real
  assumes "p > -1"
  shows "(1 + p)^n ≥ 1 + n*p"
proof (induct n)
  show "(1 + p) ^ 0 ≥ 1 + real 0 * p"
    by simp
next
  fix n
  assume HI : "(1 + p)^n ≥ 1 +  n * p"
  have "1 + Suc n * p = 1 + (n + 1) * p"
    by simp
  also have "… = 1 + n*p + p"
    by (simp add: distrib_right)
  also have "… ≤ (1 + n*p + p) + n*(p*p)"
    by simp
  also have "… = (1 + n * p) * (1 + p)"
    by algebra
  also have "… ≤ (1 + p)^n * (1 + p)"
    using HI assms by simp
  also have "… = (1 + p)^(Suc n)"
    by simp
  finally show "1 + Suc n * p ≤ (1 + p)^(Suc n)" .
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
