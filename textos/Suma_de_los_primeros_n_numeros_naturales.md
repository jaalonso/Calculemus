---
Título: Suma de los primeros números naturales
Autor:  José A. Alonso
---

Demostrar que la suma de los primeros números naturales
<pre lang="text">
   0 + 1 + 2 + 3 + ··· + n
</pre>
es n × (n + 1)/2

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.nat.basic
import tactic
open nat

variable (n : ℕ)

def suma : ℕ → ℕ
| 0     := 0
| (n+1) := suma n + (n+1)

example :
  2 * suma n = n * (n + 1) :=
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
def suma : ℕ → ℕ
| 0     := 0
| (n+1) := suma n + (n+1)

-- 1ª demostración
example :
  2 * suma n = n * (n + 1) :=
begin
  induction n with n HI,
  { calc 2 * suma 0
         = 2 * 0       : congr_arg ((*) 2) suma.equations._eqn_1
     ... = 0           : mul_zero 2
     ... = 0 * (0 + 1) : zero_mul (0 + 1), },
  { calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    : congr_arg ((*) 2) (suma.equations._eqn_2 n)
     ... = 2 * suma n + 2 * (n + 1)  : mul_add 2 (suma n) (n + 1)
     ... = n * (n + 1) + 2 * (n + 1) : congr_arg2 (+) HI rfl
     ... = (n + 2) * (n + 1)         : (add_mul n 2 (n + 1)).symm
     ... = (n + 1) * (n + 2)         : mul_comm (n + 2) (n + 1) },
end

-- 2ª demostración
example :
  2 * suma n = n * (n + 1) :=
begin
  induction n with n HI,
  { calc 2 * suma 0
         = 2 * 0       : rfl
     ... = 0           : rfl
     ... = 0 * (0 + 1) : rfl, },
  { calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    : rfl
     ... = 2 * suma n + 2 * (n + 1)  : by ring
     ... = n * (n + 1) + 2 * (n + 1) : by simp [HI]
     ... = (n + 2) * (n + 1)         : by ring
     ... = (n + 1) * (n + 2)         : by ring, },
end

-- 3ª demostración
example :
  2 * suma n = n * (n + 1) :=
begin
  induction n with n HI,
  { simp, },
  { calc 2 * suma (n + 1)
         = 2 * (suma n + (n + 1))    : rfl
     ... = 2 * suma n + 2 * (n + 1)  : by ring
     ... = n * (n + 1) + 2 * (n + 1) : by simp [HI]
     ... = (n + 1) * (n + 2)         : by ring, },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Suma_de_los_primeros_n_numeros_naturales.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Suma_de_los_primeros_n_numeros_naturales
imports Main
begin

fun suma :: "nat ⇒ nat" where
  "suma 0       = 0"
| "suma (Suc n) = suma n + Suc n"

(* 1ª demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  have "2 * suma 0 = 2 * 0"
    by (simp only: suma.simps(1))
  also have "… = 0"
    by (rule mult_0_right)
  also have "… = 0 * (0 + 1)"
    by (rule mult_0 [symmetric])
  finally show "2 * suma 0 = 0 * (0 + 1)"
    by this
next
  fix n
  assume HI : "2 * suma n = n * (n + 1)"
  have "2 * suma (Suc n) = 2 * (suma n + Suc n)"
    by (simp only: suma.simps(2))
  also have "… = 2 * suma n + 2 * Suc n"
    by (rule add_mult_distrib2)
  also have "… = n * (n + 1) + 2 * Suc n"
    by (simp only: HI)
  also have "… = n * (n + Suc 0) + 2 * Suc n"
    by (simp only: One_nat_def)
  also have "… = n * Suc (n + 0) + 2 * Suc n"
    by (simp only: add_Suc_right)
  also have "… = n * Suc n + 2 * Suc n"
    by (simp only: add_0_right)
  also have "… = (n + 2) * Suc n"
    by (simp only: add_mult_distrib)
  also have "… = Suc (Suc n) * Suc n"
    by (simp only: add_2_eq_Suc')
  also have "… = (Suc n + 1) * Suc n"
    by (simp only: Suc_eq_plus1)
  also have "… = Suc n * (Suc n + 1)"
    by (simp only: mult.commute)
  finally show "2 * suma (Suc n) = Suc n * (Suc n + 1)"
    by this
qed

(* 2ª demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  have "2 * suma 0 = 2 * 0" by simp
  also have "… = 0" by simp
  also have "… = 0 * (0 + 1)" by simp
  finally show "2 * suma 0 = 0 * (0 + 1)" .
next
  fix n
  assume HI : "2 * suma n = n * (n + 1)"
  have "2 * suma (Suc n) = 2 * (suma n + Suc n)" by simp
  also have "… = 2 * suma n + 2 * Suc n" by simp
  also have "… = n * (n + 1) + 2 * Suc n" using HI by simp
  also have "… = n * (n + Suc 0) + 2 * Suc n" by simp
  also have "… = n * Suc (n + 0) + 2 * Suc n" by simp
  also have "… = n * Suc n + 2 * Suc n" by simp
  also have "… = (n + 2) * Suc n" by simp
  also have "… = Suc (Suc n) * Suc n" by simp
  also have "… = (Suc n + 1) * Suc n" by simp
  also have "… = Suc n * (Suc n + 1)" by simp
  finally show "2 * suma (Suc n) = Suc n * (Suc n + 1)" .
qed

(* 3ª demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  have "2 * suma 0 = 2 * 0" by simp
  also have "… = 0" by simp
  also have "… = 0 * (0 + 1)" by simp
  finally show "2 * suma 0 = 0 * (0 + 1)" .
next
  fix n
  assume HI : "2 * suma n = n * (n + 1)"
  have "2 * suma (Suc n) = 2 * (suma n + Suc n)" by simp
  also have "… = n * (n + 1) + 2 * Suc n" using HI by simp
  also have "… = (n + 2) * Suc n" by simp
  also have "… = Suc n * (Suc n + 1)" by simp
  finally show "2 * suma (Suc n) = Suc n * (Suc n + 1)" .
qed

(* 4ª demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  show "2 * suma 0 = 0 * (0 + 1)" by simp
next
  fix n
  assume "2 * suma n = n * (n + 1)"
  then show "2 * suma (Suc n) = Suc n * (Suc n + 1)" by simp
qed

(* 5ª demostración *)
lemma
  "2 * suma n = n * (n + 1)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

(* 6ª demostración *)
lemma
  "2 * suma n = n * (n + 1)"
by (induct n) simp_all

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
