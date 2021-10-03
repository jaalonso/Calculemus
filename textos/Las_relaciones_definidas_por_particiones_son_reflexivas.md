---
Título: Las relaciones definidas por particiones son reflexivas
Autor:  José A. Alonso
---

Este ejercicio es el 10º de una serie cuyo objetivo es demostrar que el tipo de las particiones de un conjunto `X` es isomorfo al tipo de las relaciones de equivalencia sobre `X`.

Los anteriores son
1. [Igualdad de bloques de una partición cuando tienen elementos comunes](https://bit.ly/2YfsvBZ).
2. [Pertenencia a bloques de una partición con elementos comunes](https://bit.ly/3l2onxZ).
3. [Pertenencia a su propia clase de equivalencia](https://bit.ly/3FlVKUy).
4. [Las clases de equivalencia contienen a las clases de equivalencia de sus elementos](https://bit.ly/3uwL1Sd).
5. [Las clases de equivalencia son iguales a las de sus elementos](https://bit.ly/2Y7FJjO).
6. [Las clases de equivalencia son no vacías](https://bit.ly/39YHuCv).
7. [Las clases de equivalencia recubren el conjunto](https://bit.ly/3a1wmFc).
8. [Las clases de equivalencia son disjuntas](https://bit.ly/3FfAX54).
9. [El cociente aplica relaciones de equivalencia en particiones](https://bit.ly/3FmAtKv).

Para cada partición se define una relación de forma que un par de elementos están relacionados si pertenecen al mismo bloque de la partición. En Lean,
<pre lang="lean">
   def relacion : (particion A) → (A → A → Prop) :=
     λ P a b, ∀ X ∈ Bloques P, a ∈ X → b ∈ X
</pre>

Demostrar que la relación definida por la partición `P` es reflexiva.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

@[ext] structure particion (A : Type) :=
(Bloques    : set (set A))
(Hno_vacios : ∀ X ∈ Bloques, (X : set A).nonempty)
(Hrecubren  : ∀ a, ∃ X ∈ Bloques, a ∈ X)
(Hdisjuntos : ∀ X Y ∈ Bloques, (X ∩ Y : set A).nonempty → X = Y)

namespace particion

variable  {A : Type}

def relacion : (particion A) → (A → A → Prop) :=
  λ P a b, ∀ X ∈ Bloques P, a ∈ X → b ∈ X

example
  (P : particion A)
  : reflexive (relacion P) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic

@[ext] structure particion (A : Type) :=
(Bloques    : set (set A))
(Hno_vacios : ∀ X ∈ Bloques, (X : set A).nonempty)
(Hrecubren  : ∀ a, ∃ X ∈ Bloques, a ∈ X)
(Hdisjuntos : ∀ X Y ∈ Bloques, (X ∩ Y : set A).nonempty → X = Y)

namespace particion

variable  {A : Type}

def relacion : (particion A) → (A → A → Prop) :=
  λ P a b, ∀ X ∈ Bloques P, a ∈ X → b ∈ X

-- 1ª demostración
example
  (P : particion A)
  : reflexive (relacion P) :=
begin
  rw reflexive,
  intro a,
  unfold relacion,
  intros X hXC haX,
  exact haX,
end

-- 2ª demostración
example
  (P : particion A)
  : reflexive (relacion P) :=
begin
  intro a,
  intros X hXC haX,
  exact haX,
end

-- 3ª demostración
example
  (P : particion A)
  : reflexive (relacion P) :=
begin
  intros a X hXC haX,
  exact haX,
end

-- 4ª demostración
lemma reflexiva
  (P : particion A)
  : reflexive (relacion P) :=
λ a X hXC haX, haX

end particion
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_relaciones_definidas_por_particiones_son_reflexivas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
