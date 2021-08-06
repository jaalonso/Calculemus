---
Título: La equipotencia es una relación de equivalencia
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

example : equivalence (⋍) :=
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

example : equivalence (⋍) :=
begin
  repeat {split},
  { exact λ X, ⟨id, bijective_id⟩ },
  { rintros X Y ⟨f, hf⟩,
    cases (aux1 hf) with g hg,
    use [g, aux2 hf hg], },
  { rintros X Y Z ⟨f, hf⟩ ⟨g, hg⟩,
    exact ⟨g ∘ f, bijective.comp hg hf⟩, },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/La_equipotencia_es_una_relacion_de_equivalencia.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory La_equipotencia_es_una_relacion_de_equivalencia
imports Main "HOL-Library.Equipollence"
begin

(* 1ª demostración *)
lemma "equivp (≈)"
proof (rule equivpI)
  show "reflp (≈)"
    using reflpI eqpoll_refl by blast
next
  show "symp (≈)"
    using sympI eqpoll_sym by blast
next
  show "transp (≈)"
    using transpI eqpoll_trans by blast
qed

(* 2ª demostración *)
lemma "equivp (≈)"
  by (simp add: equivp_reflp_symp_transp
                reflpI
                sympI
                eqpoll_sym
                transpI
                eqpoll_trans)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
