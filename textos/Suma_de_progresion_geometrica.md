---
Título: Suma de progresión geométrica
Autor:  José A. Alonso
---

Demostrar que la suma de los términos de la progresión geométrica
<pre lang="text">
   a + aq + aq² + ··· + aq⇧nⁿ
</pre>
es
<pre lang="text">
     a(1 - qⁿ⁺¹)
    -------------
       1 - q
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
open nat

variable  (n : ℕ)
variables (a q : ℝ)

def sumaPG : ℝ → ℝ → ℕ → ℝ
| a q 0       := a
| a q (n + 1) := sumaPG a q n + (a * q^(n + 1))

example :
  (1 - q) * sumaPG a q n = a * (1 - q^(n + 1)) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
open nat

variable  (n : ℕ)
variables (a q : ℝ)

set_option pp.structure_projections false

@[simp]
def sumaPG : ℝ → ℝ → ℕ → ℝ
| a q 0       := a
| a q (n + 1) := sumaPG a q n + (a * q^(n + 1))

example :
  (1 - q) * sumaPG a q n = a * (1 - q^(n + 1)) :=
begin
  induction n with n HI,
  { simp,
    ac_refl, },
  { calc (1 - q) * sumaPG a q (succ n)
         = (1 - q) * (sumaPG a q n + (a * q^(n + 1)))
           : rfl
     ... = (1 - q) * sumaPG a q n + (1 - q) * (a * q^(n + 1))
           : by ring_nf
     ... = a * (1 - q ^ (n + 1)) + (1 - q) * (a * q^(n + 1))
           : by {congr ; rw HI}
     ... = a * (1 - q ^ (succ n + 1))
           : by ring_nf },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_de_progresion_geometrica.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Suma_de_progresion_geometrica
imports Main HOL.Real
begin

fun sumaPG :: "real ⇒ real ⇒ nat ⇒ real" where
  "sumaPG a q 0 = a"
| "sumaPG a q (Suc n) = sumaPG a q n + (a * q^(n + 1))"

thm algebra_simps
thm field_split_simps

(* 1ª demostración *)
lemma
  "(1 - q) * sumaPG a q n = a * (1 - q^(n + 1))"
proof (induct n)
  show "(1 - q) * sumaPG a q 0 = a * (1 - q ^ (0 + 1))"
    by simp
next
  fix n
  assume HI : "(1 - q) * sumaPG a q n = a * (1 - q ^ (n + 1))"
  have "(1 - q) * sumaPG a q (Suc n) =
        (1 - q) * (sumaPG a q n + (a * q^(n + 1)))"
    by simp
  also have "… = (1 - q) * sumaPG a q n + (1 - q) * a * q^(n + 1)"
    by (simp add: algebra_simps)
  also have "… = a * (1 - q ^ (n + 1)) + (1 - q) * a * q^(n + 1)"
    using HI by simp
  also have "… = a * (1 - q ^ (n + 1) + (1 - q) * q^(n + 1))"
    by (simp add: algebra_simps)
  also have "… = a * (1 - q ^ (n + 1) +  q^(n + 1) - q^(n + 2))"
    by (simp add: algebra_simps)
  also have "… = a * (1 - q^(n + 2))"
    by simp
  also have "… = a * (1 - q ^ (Suc n + 1))"
    by simp
  finally show "(1 - q) * sumaPG a q (Suc n) = a * (1 - q ^ (Suc n + 1))"
    by this
qed

(* 2ª demostración *)
lemma
  "(1 - q) * sumaPG a q n = a * (1 - q^(n + 1))"
proof (induct n)
  show "(1 - q) * sumaPG a q 0 = a * (1 - q ^ (0 + 1))"
    by simp
next
  fix n
  assume HI : "(1 - q) * sumaPG a q n = a * (1 - q ^ (n + 1))"
  have "(1 - q) * sumaPG a q (Suc n) =
        (1 - q) * sumaPG a q n + (1 - q) * a * q^(n + 1)"
    by (simp add: algebra_simps)
  also have "… = a * (1 - q ^ (n + 1)) + (1 - q) * a * q^(n + 1)"
    using HI by simp
  also have "… = a * (1 - q ^ (n + 1) +  q^(n + 1) - q^(n + 2))"
    by (simp add: algebra_simps)
  finally show "(1 - q) * sumaPG a q (Suc n) = a * (1 - q ^ (Suc n + 1))"
    by simp
qed

(* 3ª demostración *)
lemma
  "(1 - q) * sumaPG a q n = a * (1 - q^(n + 1))"
  using power_add
  by (induct n) (auto simp: algebra_simps)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
