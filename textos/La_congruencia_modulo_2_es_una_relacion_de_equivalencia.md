---
Título: La congruencia módulo 2 es una relación de equivalencia
Autor:  José A. Alonso
---

Se define la relación R entre los números enteros de forma que x está relacionado con y si x-y es divisible por 2. Demostrar que R es una relación de equivalencia.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.int.basic
import tactic

def R (m n : ℤ) := 2 ∣ (m - n)

example : equivalence R :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.int.basic
import tactic

def R (m n : ℤ) := 2 ∣ (m - n)

-- 1ª demostración
example : equivalence R :=
begin
  repeat {split},
  { intro x,
    unfold R,
    rw sub_self,
    exact dvd_zero 2, },
  { intros x y hxy,
    unfold R,
    cases hxy with a ha,
    use -a,
    calc y - x
         = -(x - y) : (neg_sub x y).symm
     ... = -(2 * a) : by rw ha
     ... = 2 * -a   : neg_mul_eq_mul_neg 2 a, },
  { intros x y z hxy hyz,
    cases hxy with a ha,
    cases hyz with b hb,
    use a + b,
    calc x - z
         = (x - y) + (y - z) : (sub_add_sub_cancel x y z).symm
     ... = 2 * a + 2 * b     : congr_arg2 ((+)) ha hb
     ... = 2 * (a + b)       : (mul_add 2 a b).symm , },
end

-- 2ª demostración
example : equivalence R :=
begin
  repeat {split},
  { intro x,
    simp [R], },
  { rintros x y ⟨a, ha⟩,
    use -a,
    linarith, },
  { rintros x y z ⟨a, ha⟩ ⟨b, hb⟩,
    use a + b,
    linarith, },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_congruencia_modulo_2_es_una_relacion_de_equivalencia.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory La_congruencia_modulo_2_es_una_relacion_de_equivalencia
imports Main
begin

definition R :: "(int × int) set" where
  "R = {(m, n). even (m - n)}"

lemma R_iff [simp]:
  "((x, y) ∈ R) = even (x - y)"
by (simp add: R_def)

(* 1ª demostración *)
lemma "equiv UNIV R"
proof (rule equivI)
  show "refl R"
  proof (unfold refl_on_def; intro conjI)
    show "R ⊆ UNIV × UNIV"
    proof -
      have "R ⊆ UNIV"
        by (rule top.extremum)
      also have "… = UNIV × UNIV"
        by (rule Product_Type.UNIV_Times_UNIV[symmetric])
      finally show "R ⊆ UNIV × UNIV"
        by this
    qed
  next
    show "∀x∈UNIV. (x, x) ∈ R"
    proof
      fix x :: int
      assume "x ∈ UNIV"
      have "even 0" by (rule even_zero)
      then have "even (x - x)" by (simp only: diff_self)
      then show "(x, x) ∈ R"
        by (simp only: R_iff)
    qed
  qed
next
  show "sym R"
  proof (unfold sym_def; intro allI impI)
    fix x y :: int
    assume "(x, y) ∈ R"
    then have "even (x - y)"
      by (simp only: R_iff)
    then show "(y, x) ∈ R"
    proof (rule evenE)
      fix a :: int
      assume ha : "x - y = 2 * a"
      have "y - x = -(x - y)"
        by (rule minus_diff_eq[symmetric])
      also have "… = -(2 * a)"
        by (simp only: ha)
      also have "… = 2 * (-a)"
        by (rule mult_minus_right[symmetric])
      finally have "y - x = 2 * (-a)"
        by this
      then have "even (y - x)"
        by (rule dvdI)
      then show "(y, x) ∈ R"
        by (simp only: R_iff)
    qed
  qed
next
  show "trans R"
  proof (unfold trans_def; intro allI impI)
    fix x y z
    assume hxy : "(x, y) ∈ R" and hyz : "(y, z) ∈ R"
    have "even (x - y)"
      using hxy by (simp only: R_iff)
    then obtain a where ha : "x - y = 2 * a"
      by (rule dvdE)
    have "even (y - z)"
      using hyz by (simp only: R_iff)
    then obtain b where hb : "y - z = 2 * b"
      by (rule dvdE)
    have "x - z = (x - y) + (y - z)"
      by simp
    also have "… = (2 * a) + (2 * b)"
      by (simp only: ha hb)
    also have "… = 2 * (a + b)"
      by (simp only: distrib_left)
    finally have "x - z = 2 * (a + b)"
      by this
    then have "even (x - z)"
      by (rule dvdI)
    then show "(x, z) ∈ R"
      by (simp only: R_iff)
  qed
qed

(* 2ª demostración *)
lemma "equiv UNIV R"
proof (rule equivI)
  show "refl R"
  proof (unfold refl_on_def; intro conjI)
    show "R ⊆ UNIV × UNIV" by simp
  next
    show "∀x∈UNIV. (x, x) ∈ R"
    proof
      fix x :: int
      assume "x ∈ UNIV"
      have "x - x = 2 * 0"
        by simp
      then show "(x, x) ∈ R"
        by simp
    qed
  qed
next
  show "sym R"
  proof (unfold sym_def; intro allI impI)
    fix x y :: int
    assume "(x, y) ∈ R"
    then have "even (x - y)"
      by simp
    then obtain a where ha : "x - y = 2 * a"
      by blast
    then have "y - x = 2 *(-a)"
      by simp
    then show "(y, x) ∈ R"
      by simp
  qed
next
  show "trans R"
  proof (unfold trans_def; intro allI impI)
    fix x y z
    assume hxy : "(x, y) ∈ R" and hyz : "(y, z) ∈ R"
    have "even (x - y)"
      using hxy by simp
    then obtain a where ha : "x - y = 2 * a"
      by blast
    have "even (y - z)"
      using hyz by simp
    then obtain b where hb : "y - z = 2 * b"
      by blast
    have "x - z = 2 * (a + b)"
      using ha hb by auto
    then show "(x, z) ∈ R"
      by simp
  qed
qed

(* 3ª demostración *)
lemma "equiv UNIV R"
proof (rule equivI)
  show "refl R"
  proof (unfold refl_on_def; intro conjI)
    show " R ⊆ UNIV × UNIV"
      by simp
  next
    show "∀x∈UNIV. (x, x) ∈ R"
      by simp
  qed
next
  show "sym R"
  proof (unfold sym_def; intro allI impI)
    fix x y
    assume "(x, y) ∈ R"
    then show "(y, x) ∈ R"
      by simp
  qed
next
  show "trans R"
  proof (unfold trans_def; intro allI impI)
    fix x y z
    assume "(x, y) ∈ R" and "(y, z) ∈ R"
    then show "(x, z) ∈ R"
      by simp
  qed
qed

(* 4ª demostración *)
lemma "equiv UNIV R"
proof (rule equivI)
  show "refl R"
    unfolding refl_on_def by simp
next
  show "sym R"
    unfolding sym_def by simp
next
  show "trans R"
    unfolding trans_def by simp
qed

(* 5ª demostración *)
lemma "equiv UNIV R"
  unfolding equiv_def refl_on_def sym_def trans_def
  by simp

(* 6ª demostración *)
lemma "equiv UNIV R"
  by (simp add: equiv_def refl_on_def sym_def trans_def)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
