---
Título: Potencias de potencias en monoides
Autor:  José A. Alonso
---

En los [monoides](https://en.wikipedia.org/wiki/Monoid) se define la potencia con exponentes naturales. En Lean la potencia x^n se caracteriza por los siguientes lemas:
<pre lang="text">
   pow_zero : x^0 = 1
   pow_succ' : x^(succ n) = x * x^n
</pre>

Demostrar que si M, a ∈ M y m, n ∈ ℕ, entonces
<pre lang="text">
   a^(m * n) = (a^m)^n
</pre>

Indicación: Se puede usar el lema
<pre lang="text">
   pow_add : a^(m + n) = a^m * a^n
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group_power.basic
open monoid nat

variables {M : Type} [monoid M]
variable  a : M
variables (m n : ℕ)

set_option pp.structure_projections false

example : a^(m * n) = (a^m)^n :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import algebra.group_power.basic
open monoid nat

variables {M : Type} [monoid M]
variable  a : M
variables (m n : ℕ)

-- Para que no use la notación con puntos
set_option pp.structure_projections false

-- 1ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
begin
  induction n with n HI,
  { calc a^(m * 0)
         = a^0             : congr_arg ((^) a) (nat.mul_zero m)
     ... = 1               : pow_zero a
     ... = (a^m)^0         : (pow_zero (a^m)).symm },
  { calc a^(m * succ n)
         = a^(m * n + m)   : congr_arg ((^) a) (nat.mul_succ m n)
     ... = a^(m * n) * a^m : pow_add a (m * n) m
     ... = (a^m)^n * a^m   : congr_arg (* a^m) HI
     ... = (a^m)^(succ n)  : (pow_succ' (a^m) n).symm },
end

-- 2ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
begin
  induction n with n HI,
  { calc a^(m * 0)
         = a^0             : by simp only [nat.mul_zero]
     ... = 1               : by simp only [pow_zero]
     ... = (a^m)^0         : by simp only [pow_zero] },
  { calc a^(m * succ n)
         = a^(m * n + m)   : by simp only [nat.mul_succ]
     ... = a^(m * n) * a^m : by simp only [pow_add]
     ... = (a^m)^n * a^m   : by simp only [HI]
     ... = (a^m)^succ n    : by simp only [pow_succ'] },
end

-- 3ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
begin
  induction n with n HI,
  { calc a^(m * 0)
         = a^0             : by simp [nat.mul_zero]
     ... = 1               : by simp
     ... = (a^m)^0         : by simp },
  { calc a^(m * succ n)
         = a^(m * n + m)   : by simp [nat.mul_succ]
     ... = a^(m * n) * a^m : by simp [pow_add]
     ... = (a^m)^n * a^m   : by simp [HI]
     ... = (a^m)^succ n    : by simp [pow_succ'] },
end

-- 4ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
begin
  induction n with n HI,
  { by simp [nat.mul_zero] },
  { by simp [nat.mul_succ,
             pow_add,
             HI,
             pow_succ'] },
end

-- 5ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
begin
  induction n with n HI,
  { rw nat.mul_zero,
    rw pow_zero,
    rw pow_zero, },
  { rw nat.mul_succ,
    rw pow_add,
    rw HI,
    rw pow_succ', }
end

-- 6ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
begin
  induction n with n HI,
  { rw [nat.mul_zero, pow_zero, pow_zero] },
  { rw [nat.mul_succ, pow_add, HI, pow_succ'] }
end

-- 7ª demostración
-- ===============

example : a^(m * n) = (a^m)^n :=
pow_mul a m n
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Potencias_de_potencias_en_monoides.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
(* Potencias_de_potencias_en_monoides.thy
theory Potencias_de_potencias_en_monoides
imports Main
begin

context monoid_mult
begin

(* 1ª demostración *)

lemma  "a^(m * n) = (a^m)^n"
proof (induct n)
  have "a ^ (m * 0) = a ^ 0"
    by (simp only: mult_0_right)
  also have "… = 1"
    by (simp only: power_0)
  also have "… = (a ^ m) ^ 0"
    by (simp only: power_0)
  finally show "a ^ (m * 0) = (a ^ m) ^ 0"
    by this
next
  fix n
  assume HI : "a ^ (m * n) = (a ^ m) ^ n"
  have "a ^ (m * Suc n) = a ^ (m + m * n)"
    by (simp only: mult_Suc_right)
  also have "… = a ^ m * a ^ (m * n)"
    by (simp only: power_add)
  also have "… = a ^ m * (a ^ m) ^ n"
    by (simp only: HI)
  also have "… = (a ^ m) ^ Suc n"
    by (simp only: power_Suc)
  finally show "a ^ (m * Suc n) = (a ^ m) ^ Suc n"
    by this
qed

(* 2ª demostración *)

lemma  "a^(m * n) = (a^m)^n"
proof (induct n)
  have "a ^ (m * 0) = a ^ 0"               by simp
  also have "… = 1"                        by simp
  also have "… = (a ^ m) ^ 0"              by simp
  finally show "a ^ (m * 0) = (a ^ m) ^ 0" .
next
  fix n
  assume HI : "a ^ (m * n) = (a ^ m) ^ n"
  have "a ^ (m * Suc n) = a ^ (m + m * n)" by simp
  also have "… = a ^ m * a ^ (m * n)"      by (simp add: power_add)
  also have "… = a ^ m * (a ^ m) ^ n"      using HI by simp
  also have "… = (a ^ m) ^ Suc n"          by simp
  finally show "a ^ (m * Suc n) =
                (a ^ m) ^ Suc n"           .
qed

(* 3ª demostración *)

lemma  "a^(m * n) = (a^m)^n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (simp add: power_add)
qed

(* 4ª demostración *)

lemma  "a^(m * n) = (a^m)^n"
  by (induct n) (simp_all add: power_add)

(* 5ª demostración *)

lemma "a^(m * n) = (a^m)^n"
  by (simp only: power_mult)

end

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
