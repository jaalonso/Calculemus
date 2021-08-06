---
Título: La equipotencia es una relación transitiva
Autor:  José A. Alonso
---

Dos conjuntos A y B son equipotentes (y se denota por A ≃ B) si existe una aplicación biyectiva entre ellos. La equipotencia se puede definir en Lean por
<pre lang="text">
   def es_equipotente (A B : Type*) :=
     ∃ g : A → B, bijective g

   infix ` ⋍ `: 50 := es_equipotente
</pre>

Demostrar que la relación de equipotencia es transitiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function

def es_equipotente (A B : Type*) :=
  ∃ g : A → B, bijective g

infix ` ⋍ `: 50 := es_equipotente

example : transitive (⋍) :=
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
example : transitive (⋍) :=
begin
  intros X Y Z hXY hYZ,
  unfold es_equipotente at *,
  cases hXY with f hf,
  cases hYZ with g hg,
  use (g ∘ f),
  exact bijective.comp hg hf,
end

-- 2ª demostración
example : transitive (⋍) :=
begin
  rintros X Y Z ⟨f, hf⟩ ⟨g, hg⟩,
  use [g ∘ f, bijective.comp hg hf],
end

-- 3ª demostración
example : transitive (⋍) :=
λ X Y Z ⟨f, hf⟩ ⟨g, hg⟩, by use [g ∘ f, bijective.comp hg hf]

-- 4ª demostración
example : transitive (⋍) :=
λ X Y Z ⟨f, hf⟩ ⟨g, hg⟩, exists.intro (g ∘ f) (bijective.comp hg hf)

-- 4ª demostración
example : transitive (⋍) :=
λ X Y Z ⟨f, hf⟩ ⟨g, hg⟩, ⟨g ∘ f, bijective.comp hg hf⟩
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_equipotencia_es_una_relacion_transitiva.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory La_equipotencia_es_una_relacion_transitiva
imports Main "HOL-Library.Equipollence"
begin

(* 1ª demostración *)
lemma "transp (≈)"
proof (rule transpI)
  fix x y z :: "'a set"
  assume "x ≈ y" and "y ≈ z"
  show "x ≈ z"
  proof (unfold eqpoll_def)
    obtain f where hf : "bij_betw f x y"
      using ‹x ≈ y› eqpoll_def by auto
    obtain g where hg : "bij_betw g y z"
      using ‹y ≈ z› eqpoll_def by auto
    have "bij_betw (g ∘ f) x z"
      using hf hg by (rule bij_betw_trans)
    then show "∃h. bij_betw h x z"
      by auto
  qed
qed

(* 2ª demostración *)
lemma "transp (≈)"
  unfolding eqpoll_def transp_def
  by (meson bij_betw_trans)

(* 3ª demostración *)
lemma "transp (≈)"
  by (simp add: eqpoll_trans transpI)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
