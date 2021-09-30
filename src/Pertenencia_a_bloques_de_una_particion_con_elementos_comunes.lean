-- Pertenencia_a_bloques_de_una_particion_con_elementos_comunes.lean
-- Pertenencia a bloques de una partición con elementos comunes
-- José A. Alonso Jiménez
-- Sevilla, 1 de octubre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Este ejercicio es el 2º de una serie cuyo objetivo es demostrar
-- que el tipo de las particiones de un conjunto `X` es isomorfo al tipo
-- de las relaciones de equivalencia sobre `X`. El desarrollo de dicha
-- serie está basado en la [cuarta parte](https://bit.ly/3AQWY7o) de la
-- primera sesión del curso de Kevin Buzzard
-- "Formalising mathematics: workshop 1 — logic, sets, functions,
-- relations" (https://bit.ly/3kJo231).
--
-- Una [partición](https://bit.ly/3uplABS) de un conjunto A es un conjunto
-- de subconjuntos no vacíos de A tal que todo elemento de A está
-- exactamente en uno de dichos subconjuntos. Es decir, una famila de
-- conjuntos C es una partición de A si se verifican las siguientes
-- condiciones:
-- + Los conjuntos de C son no vacíos; es decir,
--      ∀ X ∈ C, X ≠ ∅.
-- + Los conjuntos de C recubren A; es decir,
--      ∀ a ∈ A, ∃ X ∈ C, a ∈ X
-- + Los conjuntos de C son disjuntos entre sí; es decir,
--      ∀ X Y ∈ C, X ∩ Y ≠ ∅ → X = Y
--
-- En Lean, se puede definir el tipo de las particiones sobre un tipo A
-- mediante una estructura con 4 campos:
-- + Un conjunto de subconjuntos de A llamados los bloques de la partición.
-- + Una prueba de que los bloques son no vacíos.
-- + Una prueba de que cada término de tipo A está en uno de los bloques.
-- + Una prueba de que dos bloques con intersección no vacía son iguales.
-- Su definición es
--     @[ext] structure particion (A : Type) :=
--     (Bloques    : set (set A))
--     (Hno_vacios : ∀ X ∈ Bloques, (X : set A).nonempty)
--     (Hrecubren  : ∀ a, ∃ X ∈ Bloques, a ∈ X)
--     (Hdisjuntos : ∀ X Y ∈ Bloques, (X ∩ Y : set A).nonempty → X = Y)
--
-- Con la definición anterior,
-- + `P : particion A` expresa que `P` es una partición de `A`.
-- + `Bloques P` es el conjunto de los bloque de P.
-- + `Hno_vacios P` prueba que los bloques de `P` son no vacíos.
-- + `Hrecubren P` prueba que los bloque de `P` recubren a `A`.
-- + `Hdisjuntos P` prueba que los bloques de `P` son disjuntos entre sí
--
-- Demostrar que si dos bloques de una partición tienen elementos
-- comunes, entonces los elementos de uno también pertenecen al otro.
-- ---------------------------------------------------------------------

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
