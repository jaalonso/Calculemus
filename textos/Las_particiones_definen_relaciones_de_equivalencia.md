---
Título: Las particiones definen relaciones de equivalencia
Autor:  José A. Alonso
---

Cada familia de conjuntos P define una relación de forma que dos elementos están relacionados si algún conjunto de P contiene a ambos elementos. Se puede definir en Lean por
<pre lang="text">
   def relacion (P : set (set X)) (x y : X) :=
     ∃ A ∈ P, x ∈ A ∧ y ∈ A
</pre>

Una familia de subconjuntos de X es una partición de X si cada elemento de X pertenece a un único conjunto de P y todos los elementos de P son no vacíos. Se puede definir en Lean por
<pre lang="text">
   def particion (P : set (set X)) : Prop :=
     (∀ x, (∃ B ∈ P, x ∈ B ∧ ∀ C ∈ P, x ∈ C → B = C)) ∧ ∅ ∉ P
</pre>

Demostrar que si P es una partición de X, entonces la relación definida por P es una relación de equivalencia.

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
  : equivalence (relacion P) :=
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

example
  (h : particion P)
  : equivalence (relacion P) :=
begin
  repeat { split },
  { intro x,
    rcases (h.1 x) with ⟨A, hAP, hxA, -⟩,
    use [A, ⟨hAP, hxA, hxA⟩], },
  { intros x y hxy,
    rcases hxy with ⟨B, hBP, ⟨hxB, hyB⟩⟩,
    use [B, ⟨hBP, hyB, hxB⟩], },
  { rintros x y z ⟨B1,hB1P,hxB1,hyB1⟩ ⟨B2,hB2P,hyB2,hzB2⟩,
    use B1,
    repeat { split },
    { exact hB1P, },
    { exact hxB1, },
    { convert hzB2,
      rcases (h.1 y) with ⟨B, -, -, hB⟩,
      exact eq.trans (hB B1 hB1P hyB1).symm (hB B2 hB2P hyB2), }},
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_particiones_definen_relaciones_de_equivalencia.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_particiones_definen_relaciones_de_equivalencia
imports Main
begin

definition relacion :: "('a set) set ⇒ 'a ⇒ 'a ⇒ bool" where
  "relacion P x y ⟷ (∃A∈P. x ∈ A ∧ y ∈ A)"

definition particion :: "('a set) set ⇒ bool" where
  "particion P ⟷ (∀x. (∃B∈P. x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C))) ∧ {} ∉ P"

(* 1ª demostración *)
lemma
  assumes "particion P"
  shows   "equivp (relacion P)"
proof (rule equivpI)
  show "reflp (relacion P)"
  proof (rule reflpI)
    fix x
    obtain A where "A ∈ P ∧ x ∈ A"
      using assms particion_def by metis
    then show "relacion P x x"
      using relacion_def by metis
  qed
next
  show "symp (relacion P)"
  proof (rule sympI)
    fix x y
    assume "relacion P x y"
    then obtain A where "A ∈ P ∧ x ∈ A ∧ y ∈ A"
      using relacion_def by metis
    then show "relacion P y x"
      using relacion_def by metis
  qed
next
  show "transp (relacion P)"
  proof (rule transpI)
    fix x y z
    assume "relacion P x y" and "relacion P y z"
    obtain A where "A ∈ P" and hA : "x ∈ A ∧ y ∈ A"
      using ‹relacion P x y› by (meson relacion_def)
    obtain B where "B ∈ P" and hB : "y ∈ B ∧ z ∈ B"
      using ‹relacion P y z› by (meson relacion_def)
    have "A = B"
    proof -
      obtain C where "C ∈ P"
                 and hC : "y ∈ C ∧ (∀D∈P. y ∈ D ⟶ C = D)"
        using assms particion_def by metis
      then show "A = B"
        using ‹A ∈ P› ‹B ∈ P› hA hB by blast
    qed
    then have "x ∈ A ∧ z ∈ A"  using hA hB by auto
    then show "relacion P x z"
      using ‹A = B› ‹A ∈ P› relacion_def by metis
  qed
qed

(* 2ª demostración *)
lemma
  assumes "particion P"
  shows   "equivp (relacion P)"
proof (rule equivpI)
  show "reflp (relacion P)"
    using assms particion_def relacion_def
    by (metis reflpI)
next
  show "symp (relacion P)"
    using assms relacion_def
    by (metis sympI)
next
  show "transp (relacion P)"
    using assms relacion_def particion_def
    by (smt (verit) transpI)
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
