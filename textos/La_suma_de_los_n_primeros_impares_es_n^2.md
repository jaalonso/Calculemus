---
Título: La_suma_de_los_n_primeros_impares_es_n^2
Autor:  José A. Alonso
---

En Lean, se puede definir el n-ésimo número primo por
<pre lang="text">
   def impar (n : ℕ) := 2 * n + 1
</pre>
Además, en la librería finset están definidas las funciones
<pre lang="text">
   range :: ℕ → finset ℕ
   sum :: finset α → (α → β) → β
</pre>
tales que

+ (range n) es el conjunto de los n primeros números naturales. Por
  ejemplo, el valor de (range 3) es {0, 1, 2}.
+ (sum A f) es la suma del conjunto obtenido aplicando la función f a
  los elementos del conjunto finito A. Por ejemplo, el valor de
  (sum (range 3) impar) es 9.

Demostrar que la suma de los n primeros números impares es n².

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.finset
import tactic.ring
open nat

variable (n : ℕ)

def impar (n : ℕ) := 2 * n + 1

example :
  finset.sum (finset.range n) impar = n ^ 2 :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.finset
import tactic.ring
open nat

set_option pp.structure_projections false

variable (n : ℕ)

def impar (n : ℕ) := 2 * n + 1

-- 1ª demostración
example :
  finset.sum (finset.range n) impar = n ^ 2 :=
begin
  induction n with m HI,
  { calc finset.sum (finset.range 0) impar
          = 0
            : by simp
     ...  = 0 ^ 2
            : rfl, },
  { calc finset.sum (finset.range (succ m)) impar
         = finset.sum (finset.range m) impar + impar m
           : finset.sum_range_succ impar m
     ... = m ^ 2 + impar m
           : congr_arg2 (+) HI rfl
     ... = m ^ 2 + 2 * m + 1
           : rfl
     ... = (m + 1) ^ 2
           : by ring_nf
     ... = succ m ^ 2
           : rfl },
end

-- 2ª demostración
example :
  finset.sum (finset.range n) impar = n ^ 2 :=
begin
  induction n with d hd,
  { refl, },
  { rw finset.sum_range_succ,
    rw hd,
    change d ^ 2 + (2 * d + 1) = (d + 1) ^ 2,
    ring_nf, },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_suma_de_los_n_primeros_impares_es_n^2.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory "La_suma_de_los_n_primeros_impares_es_n^2"
imports Main
begin

definition impar :: "nat ⇒ nat" where
  "impar n ≡ 2 * n + 1"

lemma "sum impar {i::nat. i < n} = n⇧2"
proof (induct n)
  show "sum impar {i. i < 0} = 0⇧2"
    by simp
next
  fix n
  assume HI : "sum impar {i. i < n} = n⇧2"
  have "{i. i < Suc n} = {i. i < n} ∪ {n}"
    by auto
  then have "sum impar {i. i < Suc n} =
             sum impar {i. i < n} + impar n"
    by simp
  also have "… = n⇧2 + (2 * n + 1)"
    using HI impar_def by simp
  also have "… = (n + 1)⇧2"
    by algebra
  also have "… = (Suc n)⇧2"
    by simp
  finally show "sum impar {i. i < Suc n} = (Suc n)⇧2" .
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
