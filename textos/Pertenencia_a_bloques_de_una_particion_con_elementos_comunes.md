---
Título: Pertenencia a bloques de una partición con elementos comunes
Autor:  José A. Alonso
---

Este ejercicio es el 2º de una serie cuyo objetivo es demostrar que el tipo de las particiones de un conjunto `X` es isomorfo al tipo de las relaciones de equivalencia sobre `X`. El desarrollo de dicha serie está basado en la [cuarta parte](https://bit.ly/3AQWY7o) de la primera sesión del curso de Kevin Buzzard [Formalising mathematics: workshop 1 — logic, sets, functions, relations](https://bit.ly/3kJo231).

Una [partición](https://bit.ly/3uplABS) de un conjunto `A` es un conjunto de subconjuntos no vacíos de `A` tal que todo elemento de `A` está exactamente en uno de dichos subconjuntos. Es decir, una famila de conjuntos `C` es una partición de `A` si se verifican las siguientes condiciones:

+ Los conjuntos de `C` son no vacíos; es decir,
<pre lang="text">
     ∀ X ∈ C, X ≠ ∅.
</pre>
+ Los conjuntos de `C` recubren `A`; es decir,
<pre lang="text">
     ∀ a ∈ A, ∃ X ∈ C, a ∈ X
</pre>
+ Los conjuntos de `C` son disjuntos entre sí; es decir,
<pre lang="text">
     ∀ X Y ∈ C, X ∩ Y ≠ ∅ → X = Y
</pre>

En Lean, se puede definir el tipo de las particiones sobre un tipo `A` mediante una estructura con 4 campos donde el primero es el conjunto de los elementos de la partición y los restantes expresan las tres condiciones anteriores:
<pre lang="text">
   @[ext] structure particion (A : Type) :=
   (C : set (set A))
   (Hno_vacios : ∀ X ∈ C, (X : set A).nonempty)
   (Hrecubren : ∀ a, ∃ X ∈ C, a ∈ X)
   (Hdisjuntos : ∀ X Y ∈ C, (X ∩ Y : set A).nonempty → X = Y)
</pre>

El término `P : particion A`  expresa que `P` es una partición sobre `A`.

Se puede usar la notación de puntos para obtener los campos de una partición `P`. Por ejemplo, `P.C` es el conjunto de los conjuntos de la partición y `P.Hno_vacios` expresa que los conjuntos de `P` son no vacíos.

Los conjuntos de `P.C` se llamarán los bloques de `P`.

Demostrar que si dos bloques de una partición tienen elementos comunes, entonces los elementos de uno también pertenecen al otro.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import tactic

@[ext] structure particion (A : Type) :=
(C : set (set A))
(Hno_vacios : ∀ X ∈ C, (X : set A).nonempty)
(Hrecubren : ∀ a, ∃ X ∈ C, a ∈ X)
(Hdisjuntos : ∀ X Y ∈ C, (X ∩ Y : set A).nonempty → X = Y)

variable  {A : Type}
variable  {P : particion A}
variables {X Y : set A}

example
  (hX : X ∈ P.C)
  (hY : Y ∈ P.C)
  {a b : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  (hbX : b ∈ X)
  : b ∈ Y :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import tactic

@[ext] structure particion (A : Type) :=
(C : set (set A))
(Hno_vacios : ∀ X ∈ C, (X : set A).nonempty)
(Hrecubren : ∀ a, ∃ X ∈ C, a ∈ X)
(Hdisjuntos : ∀ X Y ∈ C, (X ∩ Y : set A).nonempty → X = Y)

variable  {A : Type}
variable  {P : particion A}
variables {X Y : set A}

lemma iguales_si_comun
  (hX : X ∈ P.C)
  (hY : Y ∈ P.C)
  {a : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  : X = Y :=
P.Hdisjuntos X Y hX hY ⟨a, haX, haY⟩

-- 1ª demostración
example
  (hX : X ∈ P.C)
  (hY : Y ∈ P.C)
  {a b : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  (hbX : b ∈ X)
  : b ∈ Y :=
begin
  convert hbX,
  apply iguales_si_comun hY hX haY,
  exact haX,
end

-- 2ª demostración
example
  (hX : X ∈ P.C)
  (hY : Y ∈ P.C)
  {a b : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  (hbX : b ∈ X)
  : b ∈ Y :=
begin
  have hXY : X = Y := iguales_si_comun hX hY haX haY,
  rw ← hXY,
  exact hbX,
end

-- 3ª demostración
lemma pertenece_si_pertenece
  (hX : X ∈ P.C)
  (hY : Y ∈ P.C)
  {a b : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  (hbX : b ∈ X)
  : b ∈ Y :=
begin
  convert hbX,
  exact iguales_si_comun hY hX haY haX,
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Pertenencia_a_bloques_de_una_particion_con_elementos_comunes.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
