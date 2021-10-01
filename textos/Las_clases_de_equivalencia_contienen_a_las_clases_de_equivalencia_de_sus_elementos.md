---
Título: Las clases de equivalencia contienen a las clases de equivalencia de sus elementos
Autor:  José A. Alonso
---

Este ejercicio es el 4º de una serie, que comenzó con el [ejercicio
 del 30 de septiembre](https://bit.ly/2YfsvBZ), cuyo objetivo es demostrar que el tipo de las particiones de un conjunto `X` es isomorfo al tipo de las relaciones de equivalencia sobre `X`.

El ejercicio consiste en demostrar que si `C` es una clase de equivalencia y `a ∈ C`, entonces la clase de equivalencia de `a` está contenida en `C`.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variable {A : Type}
variable (R : A → A → Prop)

def clase (a : A) :=
  {b : A | R b a}

example
  {hR: equivalence R}
  {a b : A}
  : a ∈ clase R b → clase R a ⊆ clase R b :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic

variable {A : Type}
variable (R : A → A → Prop)

def clase (a : A) :=
  {b : A | R b a}

-- Se usará el siguiente lema auxiliar
lemma pertenece_clase_syss
  {a b : A}
  : b ∈ clase R a ↔ R b a :=
by refl

-- 1ª demostración
example
  {hR: equivalence R}
  {a b : A}
  : a ∈ clase R b → clase R a ⊆ clase R b :=
begin
  intro hab,
  intros z hza,
  rw pertenece_clase_syss at hab hza ⊢,
  obtain ⟨-, -, htrans⟩ := hR,
  exact htrans hza hab,
end

-- 2ª demostración
example
  {hR: equivalence R}
  {a b : A}
  : a ∈ clase R b → clase R a ⊆ clase R b :=
begin
  intros hab z hza,
  exact hR.2.2 hza hab,
end

-- 3ª demostración
lemma subclase_si_pertenece
  {hR: equivalence R}
  {a b : A}
  : a ∈ clase R b → clase R a ⊆ clase R b :=
λ hab z hza, hR.2.2 hza hab
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_clases_de_equivalencia_contienen_a_las_clases_de_equivalencia_de_sus_elementos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
