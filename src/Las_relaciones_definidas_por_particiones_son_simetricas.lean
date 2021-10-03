-- Las_relaciones_definidas_por_particiones_son_simetricas.lean
-- Las relaciones definidas por particiones son simétricas
-- José A. Alonso Jiménez
-- Sevilla, 10 de octubre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que la relación correspondiente a unaa partición es
-- simétrica.
-- ---------------------------------------------------------------------

import tactic

@[ext] structure particion (A : Type) :=
(Bloques    : set (set A))
(Hno_vacios : ∀ X ∈ Bloques, (X : set A).nonempty)
(Hrecubren  : ∀ a, ∃ X ∈ Bloques, a ∈ X)
(Hdisjuntos : ∀ X Y ∈ Bloques, (X ∩ Y : set A).nonempty → X = Y)

namespace particion

variable  {A : Type}
variables {X Y : set A}
variable  {P : particion A}

def relacion : (particion A) → (A → A → Prop) :=
  λ P a b, ∀ X ∈ Bloques P, a ∈ X → b ∈ X

-- Se usarán los siguientes lemas auxiliares

lemma iguales_si_comun
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  : X = Y :=
Hdisjuntos P X Y hX hY ⟨a, haX, haY⟩

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

-- 1ª demostración
example
  (P : particion A)
  : symmetric (relacion P) :=
begin
  rw symmetric,
  intros a b hab,
  unfold relacion at *,
  intros X hX hbX,
  obtain ⟨Y, hY, haY⟩ := Hrecubren P a,
  specialize hab Y hY haY,
  exact pertenece_si_pertenece hY hX hab hbX haY,
end

-- 2ª demostración
example
  (P : particion A)
  : symmetric (relacion P) :=
begin
  intros a b hab,
  intros X hX hbX,
  obtain ⟨Y, hY, haY⟩ := Hrecubren P a,
  specialize hab Y hY haY,
  exact pertenece_si_pertenece hY hX hab hbX haY,
end

-- 3ª demostración
lemma simetrica
  (P : particion A)
  : symmetric (relacion P) :=
begin
  intros a b h X hX hbX,
  obtain ⟨Y, hY, haY⟩ := Hrecubren P a,
  specialize h Y hY haY,
  exact pertenece_si_pertenece hY hX h hbX haY,
end

end particion
