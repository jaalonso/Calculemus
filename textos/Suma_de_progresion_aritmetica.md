---
Título: Suma de progresión aritmética
Autor:  José A. Alonso
---

Demostrar que la suma de los términos de la progresión aritmética
<pre lang="text">
   a + (a + d) + (a + 2 × d) + ··· + (a + n × d)
</pre>
es (n + 1) × (2 × a + n × d) / 2.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
open nat

variable  (n : ℕ)
variables (a d : ℝ)

@[simp]
def sumaPA : ℝ → ℝ → ℕ → ℝ
| a d 0       := a
| a d (n + 1) := sumaPA a d n + (a + (n + 1) * d)

example :
  2 * sumaPA a d n = (n + 1) * (2 * a + n * d) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
open nat

variable  (n : ℕ)
variables (a d : ℝ)

set_option pp.structure_projections false

@[simp]
def sumaPA : ℝ → ℝ → ℕ → ℝ
| a d 0       := a
| a d (n + 1) := sumaPA a d n + (a + (n + 1) * d)

example :
  2 * sumaPA a d n = (n + 1) * (2 * a + n * d) :=
begin
  induction n with n HI,
  { simp, },
  { calc 2 * sumaPA a d (succ n)
         = 2 * (sumaPA a d n + (a + (n + 1) * d))
           : rfl
     ... = 2 * sumaPA a d n + 2 * (a + (n + 1) * d)
           : by ring_nf
     ... = ((n + 1) * (2 * a + n * d)) + 2 * (a + (n + 1) * d)
           : by {congr; rw HI}
     ... = (n + 2) * (2 * a + (n + 1) * d)
           : by ring_nf
     ... = (succ n + 1) * (2 * a + succ n * d)
           : congr_arg2 (*) (by norm_cast) rfl, },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_de_progresion_aritmetica.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Suma_de_progresion_aritmetica
imports Main HOL.Real
begin

fun sumaPA :: "real ⇒ real ⇒ nat ⇒ real" where
  "sumaPA a d 0 = a"
| "sumaPA a d (Suc n) = sumaPA a d n + (a + (n + 1) * d)"

(* 1ª demostración *)
lemma
  "2 * sumaPA a d n = (n + 1) * (2 * a + n * d)"
proof (induct n)
  show "2 * sumaPA a d 0 =
        (real 0 + 1) * (2 * a + real 0 * d)"
    by simp
next
  fix n
  assume HI : "2 * sumaPA a d n =
               (n + 1) * (2 * a + n * d)"
  have "2 * sumaPA a d (Suc n) =
        2 * (sumaPA a d n + (a + (n + 1) * d))"
    by simp
  also have "… = 2 * sumaPA a d n + 2 * (a + (n + 1) * d)"
    by simp
  also have "… = (n + 1) * (2 * a + n * d) + 2 * (a + (n + 1) * d)"
    using HI by simp
  also have "… = (real (Suc n) + 1) * (2 * a + (Suc n) * d)"
    by (simp add: algebra_simps)
  finally show "2 * sumaPA a d (Suc n) =
                (real (Suc n) + 1) * (2 * a + (Suc n) * d)"
    by this
qed

(* 2ª demostración *)
lemma
  "2 * sumaPA a d n = (n + 1) * (2*a + n*d)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (simp add: algebra_simps)
qed

(* 3ª demostración *)
lemma
  "2 * sumaPA a d n = (n + 1) * (2*a + n*d)"
by (induct n) (simp_all add: algebra_simps)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
