---
Título: Las clases de equivalencia son iguales a las de sus elementos
Autor:  José A. Alonso
---

Este ejercicio es el 6º de una serie, que comenzó con el [ejercicio del 30 de septiembre](https://bit.ly/2YfsvBZ), cuyo objetivo es demostrar que el tipo de las particiones de un conjunto `X` es isomorfo al tipo de las relaciones de equivalencia sobre `X`.

El ejercicio consiste en demostrar que si `C` es una clase de equivalencia y `a ∈ C`, entonces la clase de equivalencia de `a` es `C`.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variable {A : Type}
variable (R : A → A → Prop)

def clase (a : A) :=
  {b : A | R b a}

example
  (hR: equivalence R)
  {a b : A}
  : a ∈ clase R b → clase R a = clase R b :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic

variable {A : Type}
variable (R : A → A → Prop)

def clase (a : A) :=
  {b : A | R b a}

-- Se usarán los siguientes dos lemas auxiliares
lemma pertenece_clase_syss
  {a b : A}
  : b ∈ clase R a ↔ R b a :=
by refl

lemma subclase_si_pertenece
  {R : A → A → Prop}
  (hR: equivalence R)
  {a b : A}
  : a ∈ clase R b → clase R a ⊆ clase R b :=
λ hab z hza, hR.2.2 hza hab

-- 1ª demostración
example
  (hR: equivalence R)
  {a b : A}
  : a ∈ clase R b → clase R a = clase R b :=
begin
  intro hab,
  apply set.subset.antisymm,
  { apply subclase_si_pertenece hR hab, },
  { apply subclase_si_pertenece hR,
    rcases hR with ⟨-, hsymm, -⟩,
    exact hsymm hab }
end

-- 2ª demostración
example
  (hR: equivalence R)
  {a b : A}
  : a ∈ clase R b → clase R a = clase R b :=
begin
  intro hab,
  apply set.subset.antisymm,
  { exact subclase_si_pertenece hR hab, },
  { exact subclase_si_pertenece hR (hR.2.1 hab), }
end

-- 3ª demostración
example
  (hR: equivalence R)
  {a b : A}
  : a ∈ clase R b → clase R a = clase R b :=
begin
  intro hab,
  exact set.subset.antisymm
         (subclase_si_pertenece hR hab)
         (subclase_si_pertenece hR (hR.2.1 hab))
end

-- 4ª demostración
lemma clases_iguales_si_pertenece
  (hR: equivalence R)
  {a b : A}
  : a ∈ clase R b → clase R a = clase R b :=
λ hab, set.subset.antisymm
        (subclase_si_pertenece hR hab)
        (subclase_si_pertenece hR (hR.2.1 hab))
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_clases_de_equivalencia_son_iguales_a_las_de_sus_elementos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
