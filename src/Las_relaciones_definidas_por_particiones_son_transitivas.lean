-- Las_relaciones_definidas_por_particiones_son_transitivas.lean
-- Las relaciones definidas por particiones son transitivas
-- José A. Alonso Jiménez
-- Sevilla, 11 de octubre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la relación correspondiente a una partición es
-- transitiva.
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

def relacion : (particion A) → (A → A → Prop) :=
  λ P a b, ∀ X ∈ Bloques P, a ∈ X → b ∈ X

-- 1ª demostración
example
  (P : particion A)
  : transitive (relacion P) :=
begin
  unfold transitive,
  intros a b c hab hbc,
  unfold relacion at *,
  intros X hX haX,
  apply hbc,
  { exact hX, },
  { apply hab,
    { exact hX, },
    { exact haX, }},
end

-- 2ª demostración
example
  (P : particion A)
  : transitive (relacion P) :=
begin
  intros a b c hab hbc,
  intros X hX haX,
  apply hbc X hX,
  apply hab X hX,
  exact haX,
end

-- 3ª demostración
example
  (P : particion A)
  : transitive (relacion P) :=
begin
  intros a b c hab hbc X hX haX,
  exact hbc X hX (hab X hX haX),
end

-- 4ª demostración
lemma transitiva
  (P : particion A)
  : transitive (relacion P) :=
λ a b c hab hbc X hX haX, hbc X hX (hab X hX haX)

end particion
