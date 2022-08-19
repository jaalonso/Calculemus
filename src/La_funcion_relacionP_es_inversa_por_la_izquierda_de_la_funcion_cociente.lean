-- La_funcion_relacionP_es_inversa_por_la_izquierda_de_la_funcion_cociente.lean
-- La función relacionP es inversa por la izquierda de la función cociente
-- José A. Alonso Jiménez
-- Sevilla, 13 de octubre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que relacionP es inversa por la izquierda de cociente.
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
variable  (R : A → A → Prop)

def clase (a : A) :=
  {b : A | R b a}

def clases : (A → A → Prop) → set (set A) :=
  λ R, {B : set A | ∃ x : A, B = clase R x}

lemma pertenece_clase_syss
  {a b : A}
  : b ∈ clase R a ↔ R b a :=
by refl

lemma clases_no_vacias
  (hR: equivalence R)
  : ∀ (X : set A), X ∈ clases R → X.nonempty :=
begin
  rintros _ ⟨a, rfl⟩,
  use a,
  rw pertenece_clase_syss,
  apply hR.1,
end

lemma clases_recubren
  (hR: equivalence R)
  : ∀ a, ∃ X ∈ clases R, a ∈ X :=
begin
  intro a,
  use clase R a,
  split,
  { use a, },
  { exact hR.1 a, },
end

lemma subclase_si_pertenece
  {R : A → A → Prop}
  (hR: equivalence R)
  {a b : A}
  : a ∈ clase R b → clase R a ⊆ clase R b :=
λ hab z hza, hR.2.2 hza hab

lemma clases_iguales_si_pertenece
  {R : A → A → Prop}
  (hR: equivalence R)
  {a b : A}
  : a ∈ clase R b → clase R a = clase R b :=
λ hab, set.subset.antisymm
        (subclase_si_pertenece hR hab)
        (subclase_si_pertenece hR (hR.2.1 hab))

lemma clases_disjuntas
  (hR: equivalence R)
  : ∀ X Y ∈ clases R, (X ∩ Y : set A).nonempty → X = Y :=
begin
  rintros X ⟨a, rfl⟩ Y ⟨b, rfl⟩ ⟨c, hca, hcb⟩,
  exact clases_iguales_si_pertenece hR (hR.2.2 (hR.2.1 hca) hcb),
end

def cociente : {R : A → A → Prop // equivalence R} → particion A :=
  λ R, { Bloques    := {B : set A | ∃ x : A, B = clase R.1 x},
         Hno_vacios := clases_no_vacias R.1 R.2,
         Hrecubren  := clases_recubren R.1 R.2,
         Hdisjuntos := clases_disjuntas R.1 R.2, }

def relacion : (particion A) → (A → A → Prop) :=
  λ P a b, ∀ X ∈ Bloques P, a ∈ X → b ∈ X

lemma reflexiva
  (P : particion A)
  : reflexive (relacion P) :=
λ a X hXC haX, haX

lemma iguales_si_comun
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  : X = Y :=
Hdisjuntos P X hX Y hY ⟨a, haX, haY⟩

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

lemma simetrica
  (P : particion A)
  : symmetric (relacion P) :=
begin
  intros a b h X hX hbX,
  obtain ⟨Y, hY, haY⟩ := Hrecubren P a,
  specialize h Y hY haY,
  exact pertenece_si_pertenece hY hX h hbX haY,
end

lemma transitiva
  (P : particion A)
  : transitive (relacion P) :=
λ a b c hab hbc X hX haX, hbc X hX (hab X hX haX)

def relacionP : particion A → {R : A → A → Prop // equivalence R} :=
  λ P, ⟨λ a b, ∀ X ∈ Bloques P, a ∈ X → b ∈ X,
        ⟨reflexiva P, simetrica P, transitiva P⟩⟩

-- 1ª demostración
example :
  function.left_inverse relacionP (@cociente A) :=
begin
  unfold function.left_inverse,
  intro S,
  cases S with R hR,
  unfold relacionP cociente relacion,
  simp,
  ext a b,
  split,
  { intros hab,
    apply hR.2.1,
    unfold clase at hab,
    dsimp at hab,
    apply hab,
    apply hR.1, },
  { intros hab c hac,
    unfold clase at *,
    dsimp at *,
    apply hR.2.2 (hR.2.1 hab) hac, },
end

-- 2ª demostración
example :
  function.left_inverse relacionP (@cociente A) :=
begin
  rintro ⟨R, hR⟩,
  simp [relacionP, cociente],
  ext a b,
  split,
  { intros hab,
    apply hR.2.1,
    apply hab,
    apply hR.1, },
  { intros hab c hac,
    apply hR.2.2 (hR.2.1 hab) hac, },
end

-- 3ª demostración
example :
  function.left_inverse relacionP (@cociente A) :=
begin
  rintro ⟨R, hR⟩,
  simp [relacionP, cociente],
  ext a b,
  split,
  { intros hab,
    exact hR.2.1 (hab a (hR.1 a)), },
  { intros hab c hac,
    exact hR.2.2 (hR.2.1 hab) hac, },
end

-- 4ª demostración
example :
  function.left_inverse relacionP (@cociente A) :=
begin
  rintro ⟨R, hR⟩,
  simp [relacionP, cociente],
  ext a b,
  split,
  { exact λ hab, hR.2.1 (hab a (hR.1 a)), },
  { exact λ hab c hac, hR.2.2 (hR.2.1 hab) hac, },
end

-- 5ª demostración
lemma inversa_izq :
  function.left_inverse relacionP (@cociente A) :=
begin
  rintro ⟨R, hR⟩,
  simp [relacionP, cociente],
  ext a b,
  exact ⟨λ hab, hR.2.1 (hab a (hR.1 a)),
         λ hab c hac, hR.2.2 (hR.2.1 hab) hac⟩,
end

end particion
