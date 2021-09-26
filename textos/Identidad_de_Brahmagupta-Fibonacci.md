---
Título: Identidad de Brahmagupta-Fibonacci
Autor:  José A. Alonso
---

Demostrar la [identidad de Brahmagupta-Fibonacci](https://bit.ly/3ucEc80)
<pre lang="text">
   (a² + b²) * (c² + d²) = (ac - bd)² + (ad + bc)²
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables (a b c d : ℝ)

example :
  (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2 :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variables (a b c d : ℝ)

-- 1ª demostración
example : (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2 :=
calc (a^2 + b^2) * (c^2 + d^2)
     = a^2 * (c^2 + d^2) + b^2 * (c^2 + d^2)
         : right_distrib (a^2) (b^2) (c^2 + d^2)
 ... = (a^2*c^2 + a^2*d^2) + b^2 * (c^2 + d^2)
         : congr_arg2 (+) (left_distrib (a^2) (c^2) (d^2)) rfl
 ... = (a^2*c^2 + a^2*d^2) + (b^2*c^2 + b^2*d^2)
         : congr_arg2 (+) rfl (left_distrib (b^2) (c^2) (d^2))
 ... = ((a*c)^2 + (b*d)^2) + ((a*d)^2 + (b*c)^2)
         : by ring
 ... = ((a*c)^2 - 2*a*c*b*d + (b*d)^2) + ((a*d)^2 + 2*a*d*b*c + (b*c)^2)
         : by ring
 ... = (a*c - b*d)^2 + (a*d + b*c)^2
         : by ring

-- 2ª demostración
example : (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2 :=
by ring
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Identidad_de_Brahmagupta-Fibonacci.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory "Identidad_de_Brahmagupta-Fibonacci"
imports Main HOL.Real
begin

(* 1ª demostración *)
lemma
  fixes a b c d :: real
  shows "(a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2"
proof -
  have "(a^2 + b^2) * (c^2 + d^2) = a^2 * (c^2 + d^2) + b^2 * (c^2 + d^2)"
    by (simp only: distrib_right)
  also have "… = (a^2*c^2 + a^2*d^2) + b^2 * (c^2 + d^2)"
    by (simp only: distrib_left)
  also have "… = (a^2*c^2 + a^2*d^2) + (b^2*c^2 + b^2*d^2)"
    by (simp only: distrib_left)
  also have "… = ((a*c)^2 + (b*d)^2) + ((a*d)^2 + (b*c)^2)"
    by algebra
  also have "… = ((a*c)^2 - 2*a*c*b*d + (b*d)^2) + ((a*d)^2 + 2*a*d*b*c + (b*c)^2)"
    by algebra
  also have "… = (a*c - b*d)^2 + (a*d + b*c)^2"
    by algebra
  finally show "(a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2" .
qed

(* 2ª demostración *)
lemma
  fixes a b c d :: real
  shows "(a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2"
by algebra

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
