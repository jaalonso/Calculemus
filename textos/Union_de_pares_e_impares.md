---
Título: Unión de los conjuntos de los pares e impares
Autor:  José A. Alonso
---

Los conjuntos de los números naturales, de los pares y de los impares se definen por
<pre lang="lean">
   def naturales : set ℕ := {n | true}
   def pares     : set ℕ := {n | even n}
   def impares   : set ℕ := {n | ¬ even n}
</pre>

Demostrar que
<pre lang="lean">
   pares ∪ impares = naturales
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.nat.parity
import data.set.basic
import tactic

open set

def naturales : set ℕ := {n | true}
def pares     : set ℕ := {n | even n}
def impares   : set ℕ := {n | ¬ even n}

example : pares ∪ impares = naturales :=
sorry
</pre>

<!--more-->

**Soluciones con Lean**

<pre lang="lean">
import data.nat.parity
import data.set.basic
import tactic

open set

def naturales : set ℕ := {n | true}
def pares     : set ℕ := {n | even n}
def impares   : set ℕ := {n | ¬ even n}

-- 1ª demostración
-- ===============

example : pares ∪ impares = naturales :=
begin
  unfold pares impares naturales,
  ext n,
  simp,
  apply classical.em,
end

-- 2ª demostración
-- ===============

example : pares ∪ impares = naturales :=
begin
  unfold pares impares naturales,
  ext n,
  finish,
end

-- 3ª demostración
-- ===============

example : pares ∪ impares = naturales :=
by finish [pares, impares, naturales, ext_iff]
</pre>

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Union_de_pares_e_impares
imports Main
begin

definition naturales :: "nat set" where
  "naturales = {n∈ℕ . True}"

definition pares :: "nat set" where
  "pares = {n∈ℕ . even n}"

definition impares :: "nat set" where
  "impares = {n∈ℕ . ¬ even n}"

section ‹1ª demostración›

lemma "pares ∪ impares = naturales"
proof -
  have "∀ n ∈ ℕ . even n ∨ ¬ even n ⟷ True"
    by simp
  then have "{n ∈ ℕ. even n} ∪ {n ∈ ℕ. ¬ even n} = {n ∈ ℕ. True}"
    by auto
  then show "pares ∪ impares = naturales"
    by (simp add: naturales_def pares_def impares_def)
qed

section ‹2ª demostración›

lemma "pares ∪ impares = naturales"
  unfolding naturales_def pares_def impares_def
  by auto

end
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
