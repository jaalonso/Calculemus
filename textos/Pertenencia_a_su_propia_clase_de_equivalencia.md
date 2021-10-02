---
Título: Pertenencia a su propia clase de equivalencia
Autor:  José A. Alonso
---

Este ejercicio es el 3º de una serie, cuyo objetivo es demostrar que el tipo de las particiones de un conjunto `X` es isomorfo al tipo de las relaciones de equivalencia sobre `X`.

Los anteriores son
1. [Igualdad de bloques de una partición cuando tienen elementos comunes](https://bit.ly/2YfsvBZ).
2. [Pertenencia a bloques de una partición con elementos comunes](https://bit.ly/3l2onxZ).

Los anteriores fueron sobre particiones y con este empezamos con las relaciones de equivalencia que están
definidas en Lean por:
<pre lang="text">
   reflexive R := ∀ (x : A), R x x
   symmetric R := ∀ ⦃x y : A⦄, R x y → R y x
   transitive R := ∀ ⦃x y z : A⦄, R x y → R y z → R x z
   equivalence R := reflexive R ∧ symmetric R ∧ transitive R
</pre>
donde `A` un tipo y `R: A → A → Prop` es una relación binaria en `A`.

Además, en Lean se puede definir la clase de equivalencia de un elemento `a` respecto de una relación de equivalencia `R` por
<pre lang="text">
   def clase (a : A) :=
     {b : A | R b a}
</pre>

Demostrar que cada elemento pertenece a su clase de equivalencia.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

variable {A : Type}
variable (R : A → A → Prop)

def clase (a : A) :=
  {b : A | R b a}

example
  {hR : equivalence R}
  (a : A)
  : a ∈ clase R a :=
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
  {hR : equivalence R}
  (a : A)
  : a ∈ clase R a :=
begin
  rw pertenece_clase_syss,
  suffices h : reflexive R,
  { exact h a, },
  { rcases hR with ⟨h2, -, -⟩,
    exact h2, },
end

-- 1ª demostración
example
  {hR : equivalence R}
  (a : A)
  : a ∈ clase R a :=
begin
  rw pertenece_clase_syss,
  suffices h : reflexive R,
  { exact h a, },
  { exact hR.1, },
end

-- 3ª demostración
example
  {hR : equivalence R}
  (a : A)
  : a ∈ clase R a :=
begin
  rw pertenece_clase_syss,
  rcases hR with ⟨hrefl, -, -⟩,
  exact hrefl a,
end

-- 4ª demostración
example
  {hR : equivalence R}
  (a : A)
  : a ∈ clase R a :=
begin
  obtain ⟨hrefl, -, -⟩ := hR,
  rw pertenece_clase_syss,
  apply hrefl,
end

-- 5ª demostración
example
  {hR : equivalence R}
  (a : A)
  : a ∈ clase R a :=
begin
  rw pertenece_clase_syss,
  apply hR.1,
end

-- 6ª demostración
lemma pertenece_clase_propia
  {hR : equivalence R}
  (a : A)
  : a ∈ clase R a :=
(pertenece_clase_syss R).mpr (hR.1 a)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Pertenencia_a_su_propia_clase_de_equivalencia.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
