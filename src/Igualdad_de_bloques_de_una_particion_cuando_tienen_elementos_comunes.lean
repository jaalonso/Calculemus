-- Igualdad_de_bloques_de_una_particion_cuando_tienen_elementos_comunes.lean
-- Igualdad de bloques de una partición cuando tienen elementos comunes
-- José A. Alonso Jiménez
-- Sevilla, 30 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Este ejercicio es el primero de una serie cuyo objetivo es demostrar
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
-- +  Un conjunto de subconjuntos de A llamados los bloques de la partición.
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
-- + `Hdisjuntos p` prueba que los bloques de `P` son disjuntos entre sí
--
-- Demostrar que si dos bloques de una partición tienen un elemento en
-- común, entonces son iguales.
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
Hdisjuntos P X hX Y hY ⟨a, haX, haY⟩

end particion
