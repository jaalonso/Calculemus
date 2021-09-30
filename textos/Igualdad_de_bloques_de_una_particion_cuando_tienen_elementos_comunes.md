---
Título: Igualdad de bloques de una partición cuando tienen elementos comunes
Autor:  José A. Alonso
---

Este ejercicio es el primero de una serie cuyo objetivo es demostrar que el tipo de las particiones de un conjunto `X` es isomorfo al tipo de las relaciones de equivalencia sobre `X`. El desarrollo de dicha serie está basado en la [cuarta parte](https://bit.ly/3AQWY7o) de la primera sesión del curso de Kevin Buzzard
[Formalising mathematics: workshop 1 — logic, sets, functions, relations](https://bit.ly/3kJo231).

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

En Lean, se puede definir el tipo de las particiones sobre un tipo `A` mediante una estructura con 4 campos:

+ Un conjunto de subconjuntos de `A` llamados los bloques de la partición.
+ Una prueba de que los bloques son no vacíos.
+ Una prueba de que cada término de tipo `A` está en uno de los bloques.
+ Una prueba de que dos bloques con intersección no vacía son iguales.

Su definición es
<pre lang="text">
    @[ext] structure particion (A : Type) :=
    (Bloques    : set (set A))
    (Hno_vacios : ∀ X ∈ Bloques, (X : set A).nonempty)
    (Hrecubren  : ∀ a, ∃ X ∈ Bloques, a ∈ X)
    (Hdisjuntos : ∀ X Y ∈ Bloques, (X ∩ Y : set A).nonempty → X = Y)
</pre>

Con la definición anterior,

+ `P : particion A` expresa que `P` es una partición de `A`.
+ `Bloques P` es el conjunto de los bloque de P.
+ `Hno_vacios P` prueba que los bloques de `P` son no vacíos.
+ `Hrecubren P` prueba que los bloque de `P` recubren a `A`.
+ `Hdisjuntos p` prueba que los bloques de `P` son disjuntos entre sí

Demostrar que si dos bloques de una partición tienen un elemento en común, entonces son iguales.

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
variable  {P : particion A}
variables {X Y : set A}

example
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  : X = Y :=
sorry

end particion
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
variable  {P : particion A}
variables {X Y : set A}

-- 1ª demostración
example
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  : X = Y :=
begin
  apply P.Hdisjuntos,
  { exact hX, },
  { exact hY, },
  { rw set.nonempty_def,
    use a,
    split,
    { exact haX, },
    { exact haY, }},
end

-- 2ª demostración
example
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  : X = Y :=
begin
  apply P.Hdisjuntos,
  { exact hX, },
  { exact hY, },
  { use a,
    exact ⟨haX, haY⟩, },
end

-- 3ª demostración
example
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  : X = Y :=
begin
  apply P.Hdisjuntos,
  { exact hX, },
  { exact hY, },
  { exact ⟨a, haX, haY⟩, },
end

-- 4ª demostración
lemma iguales_si_comun
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  : X = Y :=
Hdisjuntos P X Y hX hY ⟨a, haX, haY⟩

end particion
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Igualdad_de_bloques_de_una_particion_cuando_tienen_elementos_comunes.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
