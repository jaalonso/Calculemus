-- Pertenencia_a_bloques_de_una_particion_con_elementos_comunes.lean
-- Pertenencia a bloques de una partición con elementos comunes
-- José A. Alonso Jiménez
-- Sevilla, 1 de octubre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Este ejercicio es el 2º de una serie, que comenzó con el [ejercicio
-- del 30 de septiembre](https://bit.ly/2YfsvBZ), cuyo objetivo es
-- demostrar que el tipo de las particiones de un conjunto `X` es
-- isomorfo al tipo de las relaciones de equivalencia sobre `X`.
--
-- El ejercicio consiste en demostrar que si dos bloques de una
-- partición tienen elementos comunes, entonces los elementos de uno
-- también pertenecen al otro.
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
Hdisjuntos P X hX Y  hY ⟨a, haX, haY⟩

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
