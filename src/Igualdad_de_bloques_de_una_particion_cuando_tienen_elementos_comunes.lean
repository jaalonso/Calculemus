-- Igualdad_de_bloques_de_una_particion_cuando_tienen_elementos_comunes.lean
-- Igualdad de bloques de una partición cuando tienen elementos comunes
-- José A. Alonso Jiménez
-- Sevilla, 30 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Una partición https://bit.ly/3uplABS de un conjunto A es un conjunto
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
-- mediante una estructura con 4 campos donde el primero es el conjunto
-- de los elementos de la partición y los restantes expresan las tres
-- condiciones anteriores:
--    @[ext] structure particion (A : Type) :=
--    (C : set (set A))
--    (Hno_vacios : ∀ X ∈ C, (X : set A).nonempty)
--    (Hrecubren : ∀ a, ∃ X ∈ C, a ∈ X)
--    (Hdisjuntos : ∀ X Y ∈ C, (X ∩ Y : set A).nonempty → X = Y)
--
-- El término `P : particion A`  expresa que P es una partición sobre
-- A.
--
-- Se puede usar la notación de puntos para obtener los campos de una
-- partición P. Por ejemplo, `P.C` es el conjunto de los conjuntos de la
-- partición y `P.Hno_vacios` expresa que los conjuntos de P son no
-- vacíos.
--
-- Los conjuntos de P.C se llamarán los bloques de P-
--
-- Demostrar que si dos bloques de una partición tienen un elemento en
-- común, entonces son iguales.
-- ---------------------------------------------------------------------

import tactic

@[ext] structure particion (A : Type) :=
(C : set (set A))
(Hno_vacios : ∀ X ∈ C, (X : set A).nonempty)
(Hrecubren : ∀ a, ∃ X ∈ C, a ∈ X)
(Hdisjuntos : ∀ X Y ∈ C, (X ∩ Y : set A).nonempty → X = Y)

variable  {A : Type}
variable  {P : particion A}
variables {X Y : set A}

-- 1ª demostración
example
  (hX : X ∈ P.C)
  (hY : Y ∈ P.C)
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
  (hX : X ∈ P.C)
  (hY : Y ∈ P.C)
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
  (hX : X ∈ P.C)
  (hY : Y ∈ P.C)
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
  (hX : X ∈ P.C)
  (hY : Y ∈ P.C)
  {a : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  : X = Y :=
P.Hdisjuntos X Y hX hY ⟨a, haX, haY⟩
