---
Título: Las particiones definen relaciones reflexivas
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

Demostrar que si P es una partición de X, entonces la relación definida por P es reflexiva.

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
  : reflexive (relacion P) :=
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
  : reflexive (relacion P) :=
begin
  unfold reflexive,
  intro x,
  unfold relacion,
  unfold particion at h,
  replace h : ∃ A ∈ P, x ∈ A ∧ ∀ B ∈ P, x ∈ B → A = B := h.1 x,
  rcases h with ⟨A, hAP, hxA, -⟩,
  use A,
  repeat { split },
  { exact hAP, },
  { exact hxA, },
  { exact hxA, },
end

-- 2ª demostración
example
  (h : particion P)
  : reflexive (relacion P) :=
begin
  intro x,
  replace h : ∃ A ∈ P, x ∈ A ∧ ∀ B ∈ P, x ∈ B → A = B := h.1 x,
  rcases h with ⟨A, hAP, hxA, -⟩,
  use A,
  repeat { split } ; assumption,
end

-- 3ª demostración
example
  (h : particion P)
  : reflexive (relacion P) :=
begin
  intro x,
  rcases (h.1 x) with ⟨A, hAP, hxA, -⟩,
  use A,
  repeat { split } ; assumption,
end

-- 4ª demostración
example
  (h : particion P)
  : reflexive (relacion P) :=
begin
  intro x,
  rcases (h.1 x) with ⟨A, hAP, hxA, -⟩,
  use [A, ⟨hAP, hxA, hxA⟩],
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_particiones_definen_relaciones_reflexivas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_particiones_definen_relaciones_reflexivas
imports Main
begin

definition relacion :: "('a set) set ⇒ 'a ⇒ 'a ⇒ bool" where
  "relacion P x y ⟷ (∃A∈P. x ∈ A ∧ y ∈ A)"

definition particion :: "('a set) set ⇒ bool" where
  "particion P ⟷ (∀x. (∃B∈P. x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C))) ∧ {} ∉ P"

thm conj_assoc
(* 1ª demostración *)
lemma
  assumes "particion P"
  shows   "reflp (relacion P)"
proof (rule reflpI)
  fix x
  have "(∀x. (∃B∈P. x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C))) ∧ {} ∉ P"
    using assms by (unfold particion_def)
  then have "∀x. (∃B∈P. x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C))"
    by (rule conjunct1)
  then have "∃B∈P. x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C)"
    by (rule allE)
  then obtain B where "B ∈ P ∧ (x ∈ B ∧ (∀C∈P. x ∈ C ⟶ B = C))"
    by (rule someI2_bex)
  then obtain B where "(B ∈ P ∧ x ∈ B) ∧ (∀C∈P. x ∈ C ⟶ B = C)"
    by (simp only: conj_assoc)
  then have "B ∈ P ∧ x ∈ B"
    by (rule conjunct1)
  then have "x ∈ B"
    by (rule conjunct2)
  then have "x ∈ B ∧ x ∈ B"
    using ‹x ∈ B› by (rule conjI)
  moreover have "B ∈ P"
    using ‹B ∈ P ∧ x ∈ B› by (rule conjunct1)
  ultimately have "∃B∈P. x ∈ B ∧ x ∈ B"
    by (rule bexI)
  then show "relacion P x x"
    by (unfold relacion_def)
qed

(* 2ª demostración *)
lemma
  assumes "particion P"
  shows   "reflp (relacion P)"
proof (rule reflpI)
  fix x
  obtain A where "A ∈ P ∧ x ∈ A"
    using assms particion_def
    by metis
  then show "relacion P x x"
    using relacion_def
    by metis
qed

(* 3ª demostración *)
lemma
  assumes "particion P"
  shows   "reflp (relacion P)"
  using assms particion_def relacion_def
  by (metis reflp_def)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
