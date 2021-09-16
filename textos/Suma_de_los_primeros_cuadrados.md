---
Título: Suma de los primeros cuadrados
Autor:  José A. Alonso
---

Demostrar que la suma de los primeros cuadrados
<pre lang="text">
   0² + 1² + 2² + 3² + ··· + n²
</pre>
es n(n+1)(2n+1)/6.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.nat.basic
import tactic
open nat

variable (n : ℕ)

@[simp]
def sumaCuadrados : ℕ → ℕ
| 0     := 0
| (n+1) := sumaCuadrados n + (n+1)^2

example :
  6 * sumaCuadrados n = n* (n + 1) * (2 * n + 1) :=
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
def sumaCuadrados : ℕ → ℕ
| 0     := 0
| (n+1) := sumaCuadrados n + (n+1)^2

-- 1ª demostración
example :
  6 * sumaCuadrados n = n* (n + 1) * (2 * n + 1) :=
begin
  induction n with n HI,
  { simp, },
  { calc 6 * sumaCuadrados (succ n)
         = 6 * (sumaCuadrados n + (n+1)^2)
           : by simp
     ... = 6 * sumaCuadrados n + 6 * (n+1)^2
           : by ring_nf
     ... = n * (n + 1) * (2 * n + 1) + 6 * (n+1)^2
           : by {congr; rw HI}
     ... = (n + 1) * (n * (2 * n + 1) + 6 * (n+1))
           : by ring_nf
     ... = (n + 1) * (2 * n^2 + 7 * n + 6)
           : by ring_nf
     ... = (n + 1) * (n + 2) * (2 * n + 3)
           : by ring_nf
     ... = succ n * (succ n + 1) * (2 * succ n + 1)
           : by refl, },
end

-- 2ª demostración
example :
  6 * sumaCuadrados n = n* (n + 1) * (2 * n + 1) :=
begin
  induction n with n HI,
  { simp, },
  { calc 6 * sumaCuadrados (succ n)
         = 6 * (sumaCuadrados n + (n+1)^2)
           : by simp
     ... = 6 * sumaCuadrados n + 6 * (n+1)^2
           : by ring_nf
     ... = n * (n + 1) * (2 * n + 1) + 6 * (n+1)^2
           : by {congr; rw HI}
     ... = (n + 1) * (n + 2) * (2 * n + 3)
           : by ring_nf
     ... = succ n * (succ n + 1) * (2 * succ n + 1)
           : by refl, },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_de_los_primeros_cuadrados.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Suma_de_los_primeros_cuadrados
imports Main
begin

fun sumaCuadrados :: "nat ⇒ nat" where
  "sumaCuadrados 0       = 0"
| "sumaCuadrados (Suc n) = sumaCuadrados n + (Suc n)^2"

(* 1ª demostración *)
lemma
  "6 * sumaCuadrados n = n* (n + 1) * (2 * n + 1)"
proof (induct n)
  show "6 * sumaCuadrados 0 =  0 * (0 + 1) * (2 * 0 + 1)"
    by simp
next
  fix n
  assume HI : "6 * sumaCuadrados n = n * (n + 1) * (2 * n + 1)"
  have "6 * sumaCuadrados (Suc n) =
        6 * (sumaCuadrados n + (n + 1)^2)"
    by simp
  also have "… = 6 * sumaCuadrados n + 6 * (n + 1)^2"
    by simp
  also have "… = n * (n + 1) * (2 * n + 1) + 6 * (n + 1)^2"
    using HI by simp
  also have "… = (n + 1) * (n * (2 * n + 1) + 6 * (n+1))"
    by algebra
  also have "… = (n + 1) * (2 * n^2 + 7 * n + 6)"
    by algebra
  also have "… = (n + 1) * (n + 2) * (2 * n + 3)"
    by algebra
  also have "… = (n + 1) * ((n + 1) + 1) * (2 * (n + 1) + 1)"
    by algebra
  also have "… = Suc n * (Suc n + 1) * (2 * Suc n + 1)"
    by (simp only: Suc_eq_plus1)
  finally show "6 * sumaCuadrados (Suc n) =
        Suc n * (Suc n + 1) * (2 * Suc n + 1)"
    by this
qed

(* 2ª demostración *)
lemma
  "6 * sumaCuadrados n = n* (n + 1) * (2 * n + 1)"
proof (induct n)
  show "6 * sumaCuadrados 0 =  0 * (0 + 1) * (2 * 0 + 1)"
    by simp
next
  fix n
  assume HI : "6 * sumaCuadrados n = n * (n + 1) * (2 * n + 1)"
  have "6 * sumaCuadrados (Suc n) =
        6 * sumaCuadrados n + 6 * (n + 1)^2"
    by simp
  also have "… = n * (n + 1) * (2 * n + 1) + 6 * (n + 1)^2"
    using HI by simp
  also have "… = (n + 1) * ((n + 1) + 1) * (2 * (n + 1) + 1)"
    by algebra
  finally show "6 * sumaCuadrados (Suc n) =
        Suc n * (Suc n + 1) * (2 * Suc n + 1)"
    by (simp only: Suc_eq_plus1)
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
