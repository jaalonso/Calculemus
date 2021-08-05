---
Título: La equipotencia es una relación reflexiva
Autor:  José A. Alonso
---

Dos conjuntos A y B son equipotentes (y se denota por A ≃ B) si existe una aplicación biyectiva entre ellos. La equipotencia se puede definir en Lean por
<pre lang="text">
   def es_equipotente (A B : Type*) :=
     ∃ g : A → B, bijective g

   infix ` ⋍ `: 50 := es_equipotente
</pre>

Demostrar que la relación de equipotencia es reflexiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function

def es_equipotente (A B : Type*) :=
  ∃ g : A → B, bijective g
infix ` ⋍ `: 50 := es_equipotente

example : reflexive (⋍) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic
open function

def es_equipotente (A B : Type*) :=
  ∃ g : A → B, bijective g

infix ` ⋍ `: 50 := es_equipotente

-- 1ª demostración
example : reflexive (⋍) :=
begin
  intro X,
  use id,
  exact bijective_id,
end

-- 2ª demostración
example : reflexive (⋍) :=
begin
  intro X,
  use [id, bijective_id],
end

-- 3ª demostración
example : reflexive (⋍) :=
λ X, ⟨id, bijective_id⟩

-- 4ª demostración
example : reflexive (⋍) :=
by tidy
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_equipotencia_es_una_relacion_reflexiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory La_equipotencia_es_una_relacion_reflexiva
imports Main "HOL-Library.Equipollence"
begin

(* 1ª demostración *)
lemma "reflp (≈)"
proof (rule reflpI)
  fix x :: "'a set"
  have "bij_betw id x x"
    by (simp only: bij_betw_id)
  then have "∃f. bij_betw f x x"
    by (simp only: exI)
  then show "x ≈ x"
    by (simp only: eqpoll_def)
qed

(* 2ª demostración *)
lemma "reflp (≈)"
by (simp only: reflpI eqpoll_refl)

(* 3ª demostración *)
lemma "reflp (≈)"
by (simp add: reflpI)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
