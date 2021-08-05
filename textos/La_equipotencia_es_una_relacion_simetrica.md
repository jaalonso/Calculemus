---
Título: La equipotencia es una relación simétrica
Autor:  José A. Alonso
---

Dos conjuntos A y B son equipotentes (y se denota por A ≃ B) si existe una aplicación biyectiva entre ellos. La equipotencia se puede definir en Lean por
<pre lang="text">
   def es_equipotente (A B : Type*) :=
     ∃ g : A → B, bijective g

   infix ` ⋍ `: 50 := es_equipotente
</pre>

Demostrar que la relación de equipotencia es simétrica.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic
open function

def es_equipotente (A B : Type*) :=
  ∃ g : A → B, bijective g

infix ` ⋍ `: 50 := es_equipotente

variables {X Y : Type*}
variable  {f : X → Y}
variable  {g : Y → X}

example : symmetric (⋍) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic
open function

def es_equipotente (A B : Type*) :=
  ∃ g : A → B, bijective g

infix ` ⋍ `: 50 := es_equipotente

variables {X Y : Type*}
variable  {f : X → Y}
variable  {g : Y → X}

def inversa (f : X → Y) (g : Y → X) :=
  (∀ x, (g ∘ f) x = x) ∧ (∀ y, (f ∘ g) y = y)

def tiene_inversa (f : X → Y) :=
  ∃ g, inversa g f

lemma aux1
  (hf : bijective f)
  : tiene_inversa f :=
begin
  cases (bijective_iff_has_inverse.mp hf) with g hg,
  by tidy,
end

lemma aux2
  (hf : bijective f)
  (hg : inversa g f)
  : bijective g :=
bijective_iff_has_inverse.mpr (by use [f, hg])

-- 1ª demostración
example : symmetric (⋍) :=
begin
  unfold symmetric,
  intros x y hxy,
  unfold es_equipotente at *,
  cases hxy with f hf,
  have h1 : tiene_inversa f := aux1 hf,
  cases h1 with g hg,
  use g,
  exact aux2 hf hg,
end

-- 2ª demostración
example : symmetric (⋍) :=
begin
  intros x y hxy,
  cases hxy with f hf,
  cases (aux1 hf) with g hg,
  use [g, aux2 hf hg],
end

-- 3ª demostración
example : symmetric (⋍) :=
begin
  rintros x y ⟨f, hf⟩,
  cases (aux1 hf) with g hg,
  use [g, aux2 hf hg],
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_equipotencia_es_una_relacion_simetrica.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory La_equipotencia_es_una_relacion_simetrica
imports Main "HOL-Library.Equipollence"
begin

(* 1ª demostración *)
lemma "symp (≈)"
proof (rule sympI)
  fix x y :: "'a set"
  assume "x ≈ y"
  then obtain f where "bij_betw f x y"
    using eqpoll_def by blast
  then have "bij_betw (the_inv_into x f) y x"
    by (rule bij_betw_the_inv_into)
  then have "∃g. bij_betw g y x"
    by auto
  then show "y ≈ x"
    by (simp only: eqpoll_def)
qed

(* 2ª demostración *)
lemma "symp (≈)"
  unfolding eqpoll_def symp_def
  using bij_betw_the_inv_into by auto

(* 3ª demostración *)
lemma "symp (≈)"
  by (simp add: eqpoll_sym sympI)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
