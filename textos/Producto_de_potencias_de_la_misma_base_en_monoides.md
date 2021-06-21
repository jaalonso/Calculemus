---
Título: Producto_de_potencias_de_la_misma_base_en_monoides
Autor:  José A. Alonso
---

En los [monoides](https://en.wikipedia.org/wiki/Monoid) se define la
potencia con exponentes naturales por recursión:
<pre lang="text">
   x^0     = 1
   x^(n+1) = x * x^n
</pre>

En Lean la potencia x^n se representa por (npow n x) y se caracteriza por los siguientes lemas:
<pre lang="text">
   npow_zero' : npow 0 x = 1
   npow_succ' : npow (succ n) x = x * npow n x
</pre>

Demostrar que
<pre lang="text">
    x ^ (m + n) = x ^ m * x ^ n
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group.defs

variables {M : Type} [monoid M]
variable  x : M
variables (m n : ℕ)

example :
  npow (m + n) x = npow m x * npow n x :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import algebra.group.defs

variables {M : Type} [monoid M]
variable  x : M
variables (m n : ℕ)

-- Para que no use la notación con puntos
set_option pp.structure_projections false

-- 1ª demostración
-- ===============

example :
  npow (m + n) x = npow m x * npow n x :=
begin
  induction m with m HI,
  { rw nat.zero_add,
    rw monoid.npow_zero',
    rw monoid.one_mul, },
  { rw nat.succ_add,
    rw monoid.npow_succ',
    rw monoid.npow_succ',
    rw HI,
    rw ← mul_assoc, },
end

-- 2ª demostración
-- ===============

example :
  npow (m + n) x = npow m x * npow n x :=
begin
  induction m with m HI,
  { rw [nat.zero_add, monoid.npow_zero', monoid.one_mul], },
  { rw [nat.succ_add, monoid.npow_succ', monoid.npow_succ', HI, ← mul_assoc] }
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Producto_de_potencias_de_la_misma_base_en_monoides.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Producto_de_potencias_de_la_misma_base_en_monoides
imports Main
begin

context monoid_mult
begin

(* 1ª demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
proof (induct m)
  have "x ^ (0 + n) = x ^ n"                 by (simp only: add_0)
  also have "… = 1 * x ^ n"                 by (simp only: mult_1_left)
  also have "… = x ^ 0 * x ^ n"             by (simp only: power_0)
  finally show "x ^ (0 + n) = x ^ 0 * x ^ n"
    by this
next
  fix m
  assume HI : "x ^ (m + n) = x ^ m * x ^ n"
  have "x ^ (Suc m + n) = x ^ Suc (m + n)"    by (simp only: add_Suc)
  also have "… = x *  x ^ (m + n)"           by (simp only: power_Suc)
  also have "… = x *  (x ^ m * x ^ n)"       by (simp only: HI)
  also have "… = (x *  x ^ m) * x ^ n"       by (simp only: mult_assoc)
  also have "… = x ^ Suc m * x ^ n"          by (simp only: power_Suc)
  finally show "x ^ (Suc m + n) = x ^ Suc m * x ^ n"
    by this
qed

(* 2ª demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
proof (induct m)
  have "x ^ (0 + n) = x ^ n"                  by simp
  also have "… = 1 * x ^ n"                  by simp
  also have "… = x ^ 0 * x ^ n"              by simp
  finally show "x ^ (0 + n) = x ^ 0 * x ^ n"
    by this
next
  fix m
  assume HI : "x ^ (m + n) = x ^ m * x ^ n"
  have "x ^ (Suc m + n) = x ^ Suc (m + n)"    by simp
  also have "… = x *  x ^ (m + n)"           by simp
  also have "… = x *  (x ^ m * x ^ n)"       using HI by simp
  also have "… = (x *  x ^ m) * x ^ n"       by (simp add: mult_assoc)
  also have "… = x ^ Suc m * x ^ n"          by simp
  finally show "x ^ (Suc m + n) = x ^ Suc m * x ^ n"
    by this
qed

(* 3ª demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
proof (induct m)
  case 0
  then show ?case
    by simp
next
  case (Suc m)
  then show ?case
    by (simp add: algebra_simps)
qed

(* 4ª demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
  by (induct m) (simp_all add: algebra_simps)

(* 5ª demostración *)

lemma "x ^ (m + n) = x ^ m * x ^ n"
  by (simp only: power_add)

end

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
