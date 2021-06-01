---
Título: Intersección de los primos y los mayores que dos
Autor:  José A. Alonso
---

Los conjuntos de los números primos, los mayores que 2 y los impares se definen por
<pre lang="lean">
   def primos      : set ℕ := {n | prime n}
   def mayoresQue2 : set ℕ := {n | n > 2}
   def impares     : set ℕ := {n | ¬ even n}
</pre>

Demostrar que
<pre lang="text">
   primos ∩ mayoresQue2 ⊆ impares
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.nat.parity
import data.nat.prime
import tactic

open nat

def primos      : set ℕ := {n | prime n}
def mayoresQue2 : set ℕ := {n | n > 2}
def impares     : set ℕ := {n | ¬ even n}

example : primos ∩ mayoresQue2 ⊆ impares :=
sorry
</pre>

<h4>Soluciones</h4>
<!--more-->

**Soluciones con Lean**

<pre lang="lean">
import data.nat.parity
import data.nat.prime
import tactic

open nat

def primos      : set ℕ := {n | prime n}
def mayoresQue2 : set ℕ := {n | n > 2}
def impares     : set ℕ := {n | ¬ even n}

example : primos ∩ mayoresQue2 ⊆ impares :=
begin
  unfold primos mayoresQue2 impares,
  intro n,
  simp,
  intro hn,
  cases prime.eq_two_or_odd hn with h h,
  { rw h,
    intro,
    linarith, },
  { rw even_iff,
    rw h,
    norm_num },
end
</pre>

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Interseccion_de_los_primos_y_los_mayores_que_dos
imports Main "HOL-Number_Theory.Number_Theory"
begin

definition primos :: "nat set" where
  "primos = {n ∈ ℕ . prime n}"

definition mayoresQue2 :: "nat set" where
  "mayoresQue2 = {n ∈ ℕ . n > 2}"

definition impares :: "nat set" where
  "impares = {n ∈ ℕ . ¬ even n}"

section ‹1ª demostración›

lemma "primos ∩ mayoresQue2 ⊆ impares"
proof
  fix x
  assume "x ∈ primos ∩ mayoresQue2"
  then have "x ∈ ℕ ∧ prime x ∧ 2 < x"
    by (simp add: primos_def mayoresQue2_def)
  then have "x ∈ ℕ ∧ odd x"
    by (simp add: prime_odd_nat)
  then show "x ∈ impares"
    by (simp add: impares_def)
qed

section ‹2ª demostración›

lemma "primos ∩ mayoresQue2 ⊆ impares"
  unfolding primos_def mayoresQue2_def impares_def
  by (simp add: Collect_mono_iff Int_def prime_odd_nat)

section ‹3ª demostración›

lemma "primos ∩ mayoresQue2 ⊆ impares"
  unfolding primos_def mayoresQue2_def impares_def
  by (auto simp add: prime_odd_nat)

end
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
