---
Título: Pertenencia a bloques de una partición con elementos comunes
Autor:  José A. Alonso
---

Este ejercicio es el 2º de una serie, que comenzó con el [ejercicio del 30 de septiembre](https://bit.ly/2YfsvBZ), cuyo objetivo es demostrar que el tipo de las particiones de un conjunto `X` es isomorfo al tipo de las relaciones de equivalencia sobre `X`.

El ejercicio consiste en demostrar que si dos bloques de una partición tienen elementos comunes, entonces los elementos de uno también pertenecen al otro.

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
  {a b : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  (hbX : b ∈ X)
  : b ∈ Y :=
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

lemma iguales_si_comun
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  : X = Y :=
Hdisjuntos P X Y hX hY ⟨a, haX, haY⟩

-- 1ª demostración
example
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
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
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
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
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a b : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  (hbX : b ∈ X)
  : b ∈ Y :=
begin
  convert hbX,
  exact iguales_si_comun hY hX haY haX,
end

end particion
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Pertenencia_a_bloques_de_una_particion_con_elementos_comunes.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
