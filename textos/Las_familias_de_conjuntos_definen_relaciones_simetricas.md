---
Título: Las familias de conjuntos definen relaciones simétricas
Autor:  José A. Alonso
---

Cada familia de conjuntos P define una relación de forma que dos elementos están relacionados si algún conjunto de P contiene a ambos elementos. Se puede definir en Lean por
<pre lang="text">
   def relacion (P : set (set X)) (x y : X) :=
     ∃ A ∈ P, x ∈ A ∧ y ∈ A
</pre>

Demostrar que si P es una familia de subconjunt❙os de X, entonces la relación definida por P es simétrica.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variable {X : Type}
variable (P : set (set X))

def relacion (P : set (set X)) (x y : X) :=
  ∃ A ∈ P, x ∈ A ∧ y ∈ A

example : symmetric (relacion P) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic

variable {X : Type}
variable (P : set (set X))

def relacion (P : set (set X)) (x y : X) :=
  ∃ A ∈ P, x ∈ A ∧ y ∈ A

-- 1ª demostración
example : symmetric (relacion P) :=
begin
  unfold symmetric,
  intros x y hxy,
  unfold relacion at *,
  rcases hxy with ⟨B, hBP, ⟨hxB, hyB⟩⟩,
  use B,
  repeat { split },
  { exact hBP, },
  { exact hyB, },
  { exact hxB, },
end

-- 2ª demostración
example : symmetric (relacion P) :=
begin
  intros x y hxy,
  rcases hxy with ⟨B, hBP, ⟨hxB, hyB⟩⟩,
  use B,
  repeat { split } ;
  assumption,
end

-- 3ª demostración
example : symmetric (relacion P) :=
begin
  intros x y hxy,
  rcases hxy with ⟨B, hBP, ⟨hxB, hyB⟩⟩,
  use [B, ⟨hBP, hyB, hxB⟩],
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_familias_de_conjuntos_definen_relaciones_simetricas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_familias_de_conjuntos_definen_relaciones_simetricas
imports Main
begin

definition relacion :: "('a set) set ⇒ 'a ⇒ 'a ⇒ bool" where
  "relacion P x y ⟷ (∃A∈P. x ∈ A ∧ y ∈ A)"

(* 1ª demostración *)
lemma "symp (relacion P)"
proof (rule sympI)
  fix x y
  assume "relacion P x y"
  then have "∃A∈P. x ∈ A ∧ y ∈ A"
    by (unfold relacion_def)
  then have "∃A∈P. y ∈ A ∧ x ∈ A"
  proof (rule bexE)
    fix A
    assume hA1 : "A ∈ P" and hA2 : "x ∈ A ∧ y ∈ A"
    have "y ∈ A ∧ x ∈ A"
      using hA2 by (simp only: conj_commute)
    then show "∃A∈P. y ∈ A ∧ x ∈ A"
      using hA1 by (rule bexI)
  qed
  then show "relacion P y x"
    by (unfold relacion_def)
qed

(* 2ª demostración *)
lemma "symp (relacion P)"
proof (rule sympI)
  fix x y
  assume "relacion P x y"
  then obtain A where "A ∈ P ∧ x ∈ A ∧ y ∈ A"
    using relacion_def
    by metis
  then show "relacion P y x"
    using relacion_def
    by metis
qed

(* 3ª demostración *)
lemma "symp (relacion P)"
  using relacion_def
  by (metis sympI)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
