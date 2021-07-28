---
Título: Propiedad cancelativa del producto de números naturales
Autor:  José A. Alonso
---

Sean k, m, n números naturales. Demostrar que
<pre lang="text">
   k * m = k * n ↔ m = n ∨ k = 0
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.nat.basic
open nat

variables {k m n : ℕ}

example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.nat.basic
open nat

variables {k m n : ℕ}

-- Para que no use la notación con puntos
set_option pp.structure_projections false

-- 1ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
begin
  have h1: k ≠ 0 → k * m = k * n → m = n,
    { induction n with n HI generalizing m,
      { by finish, },
      { cases m,
        { by finish, },
        { intros hk hS,
          congr,
          apply HI hk,
          rw mul_succ at hS,
          rw mul_succ at hS,
          exact add_right_cancel hS, }}},
  by finish,
end

-- 2ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
begin
  have h1: k ≠ 0 → k * m = k * n → m = n,
    { induction n with n HI generalizing m,
      { by finish, },
      { cases m,
        { by finish, },
        { intros hk hS,
          congr,
          apply HI hk,
          simp only [mul_succ] at hS,
          exact add_right_cancel hS, }}},
  by finish,
end

-- 3ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
begin
  have h1: k ≠ 0 → k * m = k * n → m = n,
    { induction n with n HI generalizing m,
      { by finish, },
      { cases m,
        { by finish, },
        { by finish, }}},
  by finish,
end

-- 4ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
begin
  have h1: k ≠ 0 → k * m = k * n → m = n,
    { induction n with n HI generalizing m,
      { by finish, },
      { cases m; by finish }},
  by finish,
end

-- 5ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
begin
  have h1: k ≠ 0 → k * m = k * n → m = n,
    { induction n with n HI generalizing m ; by finish },
  by finish,
end

-- 5ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
begin
  by_cases hk : k = 0,
  { by simp, },
  { rw mul_right_inj' hk,
    by tauto, },
end

-- 6ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
mul_eq_mul_left_iff

-- 7ª demostración
example :
  k * m = k * n ↔ m = n ∨ k = 0 :=
by simp
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Propiedad_cancelativa_del_producto_de_numeros_naturales.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Propiedad_cancelativa_del_producto_de_numeros_naturales
imports Main
begin

(* 1ª demostración *)
lemma
  fixes k m n :: nat
  shows "k * m = k * n ⟷ m = n ∨ k = 0"
proof -
  have "k ≠ 0 ⟹ k * m = k * n ⟹ m = n"
  proof (induct n arbitrary: m)
    fix m
    assume "k ≠ 0" and "k * m = k * 0"
    show "m = 0"
      using ‹k * m = k * 0›
      by (simp only: mult_left_cancel[OF ‹k ≠ 0›])
  next
    fix n m
    assume HI : "⋀m. ⟦k ≠ 0; k * m = k * n⟧ ⟹ m = n"
       and hk : "k ≠ 0"
       and "k * m = k * Suc n"
    then show "m = Suc n"
    proof (cases m)
      assume "m = 0"
      then show "m = Suc n"
        using ‹k * m = k * Suc n›
        by (simp only: mult_left_cancel[OF ‹k ≠ 0›])
    next
      fix m'
      assume "m = Suc m'"
      then have "k * Suc m' = k * Suc n"
        using ‹k * m = k * Suc n› by (rule subst)
      then have "k * m' + k = k * n + k"
        by (simp only: mult_Suc_right)
      then have "k * m' = k * n"
        by (simp only: add_right_imp_eq)
      then have "m' = n"
        by (simp only: HI[OF hk])
      then show "m = Suc n"
        by (simp only: ‹m = Suc m'›)
    qed
  qed
  then show "k * m = k * n ⟷ m = n ∨ k = 0"
    by auto
qed

(* 2ª demostración *)
lemma
  fixes k m n :: nat
  shows "k * m = k * n ⟷ m = n ∨ k = 0"
proof -
  have "k ≠ 0 ⟹ k * m = k * n ⟹ m = n"
  proof (induct n arbitrary: m)
    fix m
    assume "k ≠ 0" and "k * m = k * 0"
    then show "m = 0" by simp
  next
    fix n m
    assume "⋀m. ⟦k ≠ 0; k * m = k * n⟧ ⟹ m = n"
       and "k ≠ 0"
       and "k * m = k * Suc n"
    then show "m = Suc n"
    proof (cases m)
      assume "m = 0"
      then show "m = Suc n"
        using ‹k * m = k * Suc n› ‹k ≠ 0› by auto
    next
      fix m'
      assume "m = Suc m'"
      then show "m = Suc n"
        using ‹k * m = k * Suc n› ‹k ≠ 0› by force
    qed
  qed
  then show "k * m = k * n ⟷ m = n ∨ k = 0" by auto
qed

(* 3ª demostración *)
lemma
  fixes k m n :: nat
  shows "k * m = k * n ⟷ m = n ∨ k = 0"
proof -
  have "k ≠ 0 ⟹ k * m = k * n ⟹ m = n"
  proof (induct n arbitrary: m)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
    then show ?case
    proof (cases m)
      case 0
      then show ?thesis
        using Suc.prems by auto
    next
      case (Suc nat)
      then show ?thesis
        using Suc.prems by auto
    qed
  qed
  then show ?thesis
    by auto
qed

(* 4ª demostración *)
lemma
  fixes k m n :: nat
  shows "k * m = k * n ⟷ m = n ∨ k = 0"
proof -
  have "k ≠ 0 ⟹ k * m = k * n ⟹ m = n"
  proof (induct n arbitrary: m)
    case 0
    then show "m = 0" by simp
  next
    case (Suc n)
    then show "m = Suc n"
      by (cases m) (simp_all add: eq_commute [of 0])
  qed
  then show ?thesis by auto
qed

(* 5ª demostración *)
lemma
  fixes k m n :: nat
  shows "k * m = k * n ⟷ m = n ∨ k = 0"
by (simp only: mult_cancel1)

(* 6ª demostración *)
lemma
  fixes k m n :: nat
  shows "k * m = k * n ⟷ m = n ∨ k = 0"
by simp

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
