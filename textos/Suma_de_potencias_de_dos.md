---
Título: Suma de potencias de dos
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   1 + 2 + 2² + 2³ + ... + 2⁽ⁿ⁻¹⁾ = 2ⁿ - 1
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.big_operators
import tactic
open finset nat

open_locale big_operators

variable (n : ℕ)

example :
  ∑ k in range n, 2^k = 2^n - 1 :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import algebra.big_operators
import tactic
open finset nat

open_locale big_operators
set_option pp.structure_projections false

variable (n : ℕ)

example :
  ∑ k in range n, 2^k = 2^n - 1 :=
begin
  induction n with n HI,
  { simp, },
  { calc ∑ k in range (succ n), 2^k
         = ∑ k in range n, 2^k + 2^n
             : sum_range_succ (λ x, 2 ^ x) n
     ... = (2^n - 1) + 2^n
             : congr_arg2 (+) HI rfl
     ... = (2^n + 2^n) - 1
             : by omega
     ... = 2^n * 2 - 1
             : by {congr; simp}
     ... = 2^(succ n) - 1
             : by {congr' 1; ring_nf}, },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_de_potencias_de_dos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Suma_de_potencias_de_dos
imports Main
begin

(* 1ª demostración *)
lemma "(∑k≤n. (2::nat)^k) = 2^(n+1) - 1"
proof (induct n)
  show "(∑k≤0. (2::nat)^k) = 2^(0+1) - 1"
    by simp
next
  fix n
  assume HI : "(∑k≤n. (2::nat)^k) = 2^(n+1) - 1"
  have "(∑k≤Suc n. (2::nat)^k) =
        (∑k≤n. (2::nat)^k) + 2^Suc n"
    by simp
  also have "… = (2^(n+1) - 1) + 2^Suc n"
    using HI by simp
  also have "… = 2^(Suc n + 1) - 1"
    by simp
  finally show "(∑k≤Suc n. (2::nat)^k) = 2^(Suc n + 1) - 1" .
qed

(* 2ª demostración *)
lemma "(∑k≤n. (2::nat)^k) = 2^(n+1) - 1"
proof (induct n)
  show "(∑k≤0. (2::nat)^k) = 2^(0+1) - 1"
    by simp
next
  fix n
  assume HI : "(∑k≤n. (2::nat)^k) = 2^(n+1) - 1"
  have "(∑k≤Suc n. (2::nat)^k) =
        (2^(n+1) - 1) + 2^Suc n"
    using HI by simp
  then show "(∑k≤Suc n. (2::nat)^k) = 2^(Suc n + 1) - 1"
    by simp
qed

(* 3ª demostración *)
lemma "(∑k≤n. (2::nat)^k) = 2^(n+1) - 1"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

(* 4ª demostración *)
lemma "(∑k≤n. (2::nat)^k) = 2^(n+1) - 1"
by (induct n) simp_all
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
