---
Título: Las particiones definen relaciones transitivas
Autor:  José A. Alonso
---

Cada familia de conjuntos P define una relación de forma que dos elementos están relacionados si algún conjunto de P contiene a ambos elementos. Se puede definir en Lean por
<pre lang="text">
   def relacion (P : set (set X)) (x y : X) :=
     ∃ A ∈ P, x ∈ A ∧ y ∈ A
</pre>

Una familia de subconjuntos de X es una partición de X si cada  de X pertenece a un único conjunto de P y todos los elementos de P son no vacíos. Se puede definir en Lean por
<pre lang="text">
   def particion (P : set (set X)) : Prop :=
     (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P
</pre>

Demostrar que si P es una partición de X, entonces la relación definida por P es transitiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variable {X : Type}
variable (P : set (set X))

def relacion (P : set (set X)) (x y : X) :=
  ∃ A ∈ P, x ∈ A ∧ y ∈ A

def particion (P : set (set X)) : Prop :=
  (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P

example
  (h : particion P)
  : transitive (relacion P) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic

variable {X : Type}
variable (P : set (set X))

def relacion (P : set (set X)) (x y : X) :=
  ∃ A ∈ P, x ∈ A ∧ y ∈ A

def particion (P : set (set X)) : Prop :=
  (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P

-- 1ª demostración
example
  (h : particion P)
  : transitive (relacion P) :=
begin
  unfold transitive,
  intros x y z h1 h2,
  unfold relacion at *,
  rcases h1 with ⟨B1, hB1P, hxB1, hyB1⟩,
  rcases h2 with ⟨B2, hB2P, hyB2, hzB2⟩,
  use B1,
  repeat { split },
  { exact hB1P, },
  { exact hxB1, },
  { convert hzB2,
    rcases (h.1 y) with ⟨B, -, -, hB⟩,
    have hBB1 : B = B1 := hB B1 hB1P hyB1,
    have hBB2 : B = B2 := hB B2 hB2P hyB2,
    exact eq.trans hBB1.symm hBB2, },
end

-- 2ª demostración
example
  (h : particion P)
  : transitive (relacion P) :=
begin
  rintros x y z ⟨B1,hB1P,hxB1,hyB1⟩ ⟨B2,hB2P,hyB2,hzB2⟩,
  use B1,
  repeat { split },
  { exact hB1P, },
  { exact hxB1, },
  { convert hzB2,
    rcases (h.1 y) with ⟨B, -, -, hB⟩,
    exact eq.trans (hB B1 hB1P hyB1).symm (hB B2 hB2P hyB2), },
end

-- 3ª demostración
example
  (h : particion P)
  : transitive (relacion P) :=
begin
  rintros x y z ⟨B1,hB1P,hxB1,hyB1⟩ ⟨B2,hB2P,hyB2,hzB2⟩,
  use [B1, ⟨hB1P,
            hxB1,
            by { convert hzB2,
                 rcases (h.1 y) with ⟨B, -, -, hB⟩,
                 exact eq.trans (hB B1 hB1P hyB1).symm
                                (hB B2 hB2P hyB2), }⟩],
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_particiones_definen_relaciones_transitivas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_particiones_definen_relaciones_transitivas
imports Main
begin

definition relacion :: "('a set) set ⇒ 'a ⇒ 'a ⇒ bool" where
  "relacion P x y ⟷ (∃A∈P. x ∈ A ∧ y ∈ A)"

definition particion :: "('a set) set ⇒ bool" where
  "particion P ⟷ (∀x. (∃B∈P. x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C))) ∧ {} ∉ P"

(* 1ª demostración *)
lemma
  assumes "particion P"
  shows   "transp (relacion P)"
proof (rule transpI)
  fix x y z
  assume "relacion P x y" and "relacion P y z"
  have "∃A∈P. x ∈ A ∧ y ∈ A"
    using ‹relacion P x y›
    by (simp only: relacion_def)
  then obtain A where "A ∈ P" and hA : "x ∈ A ∧ y ∈ A"
    by (rule bexE)
  have "∃B∈P. y ∈ B ∧ z ∈ B"
    using ‹relacion P y z›
    by (simp only: relacion_def)
  then obtain B where "B ∈ P" and hB : "y ∈ B ∧ z ∈ B"
    by (rule bexE)
  have "A = B"
  proof -
    have "∃C ∈ P. y ∈ C ∧ (∀D∈P. y ∈ D ⟶ C = D)"
      using assms
      by (simp only: particion_def)
    then obtain C where "C ∈ P"
                    and hC : "y ∈ C ∧ (∀D∈P. y ∈ D ⟶ C = D)"
      by (rule bexE)
    have hC' : "∀D∈P. y ∈ D ⟶ C = D"
      using hC by (rule conjunct2)
    have "C = A"
      using ‹A ∈ P› hA hC' by simp
    moreover have "C = B"
      using ‹B ∈ P› hB hC by simp
    ultimately show "A = B"
      by (rule subst)
  qed
  then have "x ∈ A ∧ z ∈ A"
    using hA hB by simp
  then have "∃A∈P. x ∈ A ∧ z ∈ A"
    using ‹A ∈ P› by (rule bexI)
  then show "relacion P x z"
    using ‹A = B› ‹A ∈ P›
    by (unfold relacion_def)
qed

(* 2ª demostración *)
lemma
  assumes "particion P"
  shows   "transp (relacion P)"
proof (rule transpI)
  fix x y z
  assume "relacion P x y" and "relacion P y z"
  obtain A where "A ∈ P" and hA : "x ∈ A ∧ y ∈ A"
    using ‹relacion P x y›
    by (meson relacion_def)
  obtain B where "B ∈ P" and hB : "y ∈ B ∧ z ∈ B"
    using ‹relacion P y z›
    by (meson relacion_def)
  have "A = B"
  proof -
    obtain C where "C ∈ P" and hC : "y ∈ C ∧ (∀D∈P. y ∈ D ⟶ C = D)"
      using assms particion_def
      by metis
    have "C = A"
      using ‹A ∈ P› hA hC by auto
    moreover have "C = B"
      using ‹B ∈ P› hB hC by auto
    ultimately show "A = B"
      by simp
  qed
  then have "x ∈ A ∧ z ∈ A"
    using hA hB by auto
  then show "relacion P x z"
    using ‹A = B› ‹A ∈ P› relacion_def
    by metis
qed

(* 3ª demostración *)
lemma
  assumes "particion P"
  shows   "transp (relacion P)"
  using assms particion_def relacion_def
  by (smt (verit) transpI)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
