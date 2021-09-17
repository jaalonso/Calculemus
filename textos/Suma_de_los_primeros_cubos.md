---
Título: Suma de los primeros cubos
Autor:  José A. Alonso
---

Demostrar que la suma de los primeros cubos
<pre lang="text">
   0³ + 1³ + 2³ + 3³ + ··· + n³
</pre>
es (n(n+1)/2)²

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.nat.basic
import tactic
open nat

variable (n : ℕ)

def sumaCubos : ℕ → ℕ
| 0     := 0
| (n+1) := sumaCubos n + (n+1)^3

example :
  4 * sumaCubos n = (n*(n+1))^2 :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.nat.basic
import tactic
open nat

variable (n : ℕ)

set_option pp.structure_projections false

@[simp]
def sumaCubos : ℕ → ℕ
| 0     := 0
| (n+1) := sumaCubos n + (n+1)^3

-- 1ª demostración
example :
  4 * sumaCubos n = (n*(n+1))^2 :=
begin
  induction n with n HI,
  { simp,
    ring, },
  { calc 4 * sumaCubos (succ n)
         = 4 * (sumaCubos n + (n+1)^3)
           : by simp
     ... = 4 * sumaCubos n + 4*(n+1)^3
           : by ring
     ... = (n*(n+1))^2 + 4*(n+1)^3
           : by {congr; rw HI}
     ... = (n+1)^2*(n^2+4*n+4)
           : by ring
     ... = (n+1)^2*(n+2)^2
           : by ring
     ... = ((n+1)*(n+2))^2
           : by ring
     ... = (succ n * (succ n + 1)) ^ 2
           : by simp, },
end

-- 2ª demostración
example :
  4 * sumaCubos n = (n*(n+1))^2 :=
begin
  induction n with n HI,
  { simp,
    ring, },
  { calc 4 * sumaCubos (succ n)
         = 4 * sumaCubos n + 4*(n+1)^3
           : by {simp ; ring}
     ... = (n*(n+1))^2 + 4*(n+1)^3
           : by {congr; rw HI}
     ... = ((n+1)*(n+2))^2
           : by ring
     ... = (succ n * (succ n + 1)) ^ 2
           : by simp, },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_de_los_primeros_cubos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Suma_de_los_primeros_cubos
imports Main
begin

fun sumaCubos :: "nat ⇒ nat" where
  "sumaCubos 0       = 0"
| "sumaCubos (Suc n) = sumaCubos n + (Suc n)^3"

(* 1ª demostración *)
lemma
  "4 * sumaCubos n = (n*(n+1))^2"
proof (induct n)
  show "4 * sumaCubos 0 = (0 * (0 + 1))^2"
    by simp
next
  fix n
  assume HI : "4 * sumaCubos n = (n * (n + 1))^2"
  have "4 * sumaCubos (Suc n) = 4 * (sumaCubos n + (n+1)^3)"
    by simp
  also have "… = 4 * sumaCubos n + 4*(n+1)^3"
    by simp
  also have "… = (n*(n+1))^2 + 4*(n+1)^3"
    using HI by simp
  also have "… = (n+1)^2*(n^2+4*n+4)"
    by algebra
  also have "… = (n+1)^2*(n+2)^2"
    by algebra
  also have "… = ((n+1)*((n+1)+1))^2"
    by algebra
  also have "… = (Suc n * (Suc n + 1))^2"
    by (simp only: Suc_eq_plus1)
  finally show "4 * sumaCubos (Suc n) = (Suc n * (Suc n + 1))^2"
    by this
qed

(* 2ª demostración *)
lemma
  "4 * sumaCubos n = (n*(n+1))^2"
proof (induct n)
  show "4 * sumaCubos 0 = (0 * (0 + 1))^2"
    by simp
next
  fix n
  assume HI : "4 * sumaCubos n = (n * (n + 1))^2"
  have "4 * sumaCubos (Suc n) = 4 * sumaCubos n + 4*(n+1)^3"
    by simp
  also have "… = (n*(n+1))^2 + 4*(n+1)^3"
    using HI by simp
  also have "… = ((n+1)*((n+1)+1))^2"
    by algebra
  also have "… = (Suc n * (Suc n + 1))^2"
    by (simp only: Suc_eq_plus1)
  finally show "4 * sumaCubos (Suc n) = (Suc n * (Suc n + 1))^2" .
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
