---
Título: Caracterización de producto igual al primer factor
Autor:  José A. Alonso
---

Un [monoide cancelativo por la izquierda](https://bit.ly/3j9S0wt) es un [monoide](https://bit.ly/3h4notA) M que cumple la propiedad cancelativa por la izquierda; es decir, para todo a, b ∈ M
<pre lang="text">
   a * b = a * c ↔ b = c.
</pre>

En Lean la clase de los monoides cancelativos por la izquierda es left\_cancel\_monoid y la propiedad cancelativa por la izquierda es
<pre lang="text">
   mul_left_cancel_iff : a * b = a * c ↔ b = c
</pre>

Demostrar que si M es un monoide cancelativo por la izquierda y a, b ∈ M, entonces
<pre lang="text">
   a * b = a ↔ b = 1
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group.basic

universe  u
variables {M : Type u} [left_cancel_monoid M]
variables {a b : M}

example : a * b = a ↔ b = 1 :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import algebra.group.basic

universe  u
variables {M : Type u} [left_cancel_monoid M]
variables {a b : M}

-- ?ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
begin
  split,
  { intro h,
    rw ← @mul_left_cancel_iff _ _ a b 1,
    rw mul_one,
    exact h, },
  { intro h,
    rw h,
    exact mul_one a, },
end

-- ?ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
calc a * b = a ↔ a * b = a * 1 : by rw mul_one
           ... ↔ b = 1         : mul_left_cancel_iff

-- ?ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
mul_right_eq_self

-- ?ª demostración
-- ===============

example : a * b = a ↔ b = 1 :=
by finish
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Caracterizacion_de_producto_igual_al_primer_factor.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Caracterizacion_de_producto_igual_al_primer_factor
imports Main
begin

context cancel_comm_monoid_add
begin

(* 1ª demostración *)

lemma "a + b = a ⟷ b = 0"
proof (rule iffI)
  assume "a + b = a"
  then have "a + b = a + 0"     by (simp only: add_0_right)
  then show "b = 0"             by (simp only: add_left_cancel)
next
  assume "b = 0"
  have "a + 0 = a"              by (simp only: add_0_right)
  with ‹b = 0› show "a + b = a" by (rule ssubst)
qed

(* 2ª demostración *)

lemma "a + b = a ⟷ b = 0"
proof
  assume "a + b = a"
  then have "a + b = a + 0" by simp
  then show "b = 0"         by simp
next
  assume "b = 0"
  have "a + 0 = a"          by simp
  then show "a + b = a"     using ‹b = 0› by simp
qed

(* 3ª demostración *)

lemma "a + b = a ⟷ b = 0"
proof -
  have "(a + b = a) ⟷ (a + b = a + 0)" by (simp only: add_0_right)
  also have "… ⟷ (b = 0)"              by (simp only: add_left_cancel)
  finally show "a + b = a ⟷ b = 0"     by this
qed

(* 4ª demostración *)

lemma "a + b = a ⟷ b = 0"
proof -
  have "(a + b = a) ⟷ (a + b = a + 0)" by simp
  also have "… ⟷ (b = 0)"              by simp
  finally show "a + b = a ⟷ b = 0"     .
qed

(* 5ª demostración *)

lemma "a + b = a ⟷ b = 0"
  by (simp only: add_cancel_left_right)

(* 6ª demostración *)

lemma "a + b = a ⟷ b = 0"
  by auto

end

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
