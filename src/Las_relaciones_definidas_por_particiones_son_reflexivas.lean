-- Las_relaciones_definidas_por_particiones_son_reflexivas.lean
-- Las relaciones definidas por particiones son reflexivas
-- José A. Alonso Jiménez
-- Sevilla, 9 de octubre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Para cada partición se define una relación de forma que un par de
-- elementos están relacionados si pertenecen al mismo bloque de la
-- partición. En Lena,
--    def relacion : (particion A) → (A → A → Prop) :=
--      λ P a b, ∀ X ∈ Bloques P, a ∈ X → b ∈ X
--
-- Demostrar que la relación definida por la partición P es reflexiva.
-- ---------------------------------------------------------------------

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
