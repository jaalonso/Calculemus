---
Título: Equivalencia de inversos iguales al neutro
Autor:  José A. Alonso
---

Sea M un monoide y a, b ∈ M tales que a * b = 1. Demostrar que a = 1 si y sólo si b = 1.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group.basic

variables {M : Type} [monoid M]
variables {a b : M}

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import algebra.group.basic

variables {M : Type} [monoid M]
variables {a b : M}

-- 1ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
begin
  split,
  { intro a1,
    rw a1 at h,
    rw one_mul at h,
    exact h, },
  { intro b1,
    rw b1 at h,
    rw mul_one at h,
    exact h, },
end

-- 2ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
begin
  split,
  { intro a1,
    calc b = 1 * b : (one_mul b).symm
       ... = a * b : congr_arg (* b) a1.symm
       ... = 1     : h, },
  { intro b1,
    calc a = a * 1 : (mul_one a).symm
       ... = a * b : congr_arg ((*) a) b1.symm
       ... = 1     : h, },
end

-- 3ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
begin
  split,
  { rintro rfl,
    simpa using h, },
  { rintro rfl,
    simpa using h, },
end

-- 4ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by split ; { rintro rfl, simpa using h }

-- 5ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by split ; finish

-- 6ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
by finish [iff_def]

-- 7ª demostración
-- ===============

example
  (h : a * b = 1)
  : a = 1 ↔ b = 1 :=
eq_one_iff_eq_one_of_mul_eq_one h
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Equivalencia_de_inversos_iguales_al_neutro.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Equivalencia_de_inversos_iguales_al_neutro
imports Main
begin

context monoid
begin

(* 1ª demostración *)

lemma
  assumes "a * b = 1"
  shows   "a = 1 ⟷ b = 1"
proof (rule iffI)
  assume "a = 1"
  have "b = 1 * b"      by (simp only: left_neutral)
  also have "… = a * b" by (simp only: ‹a = 1›)
  also have "… = 1"     by (simp only: ‹a * b = 1›)
  finally show "b = 1"  by this
next
  assume "b = 1"
  have "a = a * 1"      by (simp only: right_neutral)
  also have "… = a * b" by (simp only: ‹b = 1›)
  also have "… = 1"     by (simp only: ‹a * b = 1›)
  finally show "a = 1"  by this
qed

(* 2ª demostración *)

lemma
  assumes "a * b = 1"
  shows   "a = 1 ⟷ b = 1"
proof
  assume "a = 1"
  have "b = 1 * b"      by simp
  also have "… = a * b" using ‹a = 1› by simp
  also have "… = 1"     using ‹a * b = 1› by simp
  finally show "b = 1"  .
next
  assume "b = 1"
  have "a = a * 1"      by simp
  also have "… = a * b" using ‹b = 1› by simp
  also have "… = 1"     using ‹a * b = 1› by simp
  finally show "a = 1"  .
qed

(* 3ª demostración *)

lemma
  assumes "a * b = 1"
  shows   "a = 1 ⟷ b = 1"
  by (metis assms left_neutral right_neutral)

end

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
