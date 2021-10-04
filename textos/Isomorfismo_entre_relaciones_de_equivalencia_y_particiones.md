---
Título: Isomorfismo entre relaciones de equivalencia y particiones
Autor:  José A. Alonso
---

Este ejercicio es el 16º de una serie cuyo objetivo es demostrar que el tipo de las particiones de un conjunto `X` es isomorfo al tipo de las relaciones de equivalencia sobre `X`.

Los anteriores son
1. [Igualdad de bloques de una partición cuando tienen elementos comunes](https://bit.ly/2YfsvBZ).
2. [Pertenencia a bloques de una partición con elementos comunes](https://bit.ly/3l2onxZ).
3. [Pertenencia a su propia clase de equivalencia](https://bit.ly/3FlVKUy).
4. [Las clases de equivalencia contienen a las clases de equivalencia de sus elementos](https://bit.ly/3uwL1Sd).
5. [Las clases de equivalencia son iguales a las de sus elementos](https://bit.ly/2Y7FJjO).
6. [Las clases de equivalencia son no vacías](https://bit.ly/39YHuCv).
7. [Las clases de equivalencia recubren el conjunto](https://bit.ly/3a1wmFc).
8. [Las clases de equivalencia son disjuntas](https://bit.ly/3FfAX54).
9. [El cociente aplica relaciones de equivalencia en particiones](https://bit.ly/3FmAtKv).
10. [Las relaciones definidas por particiones son reflexivas](https://bit.ly/3B2lLpc).
11. [Las relaciones definidas por particiones son simétricas](https://bit.ly/2ZWmY3O).
12. [Las relaciones definidas por particiones son transitivas](https://bit.ly/3B9e54J).
13. [Aplicación de particiones en relaciones de equivalencia](https://bit.ly/3a8AuTP).
14. [La función `relacionP` es inversa por la izquierda de la función `cociente`](https://bit.ly/3l8kwz8)
15. [La función `relacionP` es inversa por la derecha de la función `cociente`](https://bit.ly/3FfqzKo).

En Lean, el tipo de los isomorfimos de un tipo `α` en un tipo `β` está definido mediante la siguiente estructura
<pre lang="lean">
   structure equiv (α : Sort*) (β : Sort*) :=
   (to_fun    : α → β)
   (inv_fun   : β → α)
   (left_inv  : left_inverse inv_fun to_fun)
   (right_inv : right_inverse inv_fun to_fun)
</pre>
y se `equiv α β` se denota por `α ≃ β`. Por tanto, para demostrar que los dos tipos don isomorfos hay que definir dos funciones entre ellos y demostrar que una es la inversa de la otra.

Demostrar que los tipos de las relaciones de equivalencia sobre `A` y el de las particiones de `A` son isomorfos.

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
  rintros X Y ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, hca, hcb⟩,
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

lemma inversa_izq :
  function.left_inverse relacionP (@cociente A) :=
begin
  rintro ⟨R, hR⟩,
  simp [relacionP, cociente],
  ext a b,
  exact ⟨λ hab, hR.2.1 (hab a (hR.1 a)),
         λ hab c hac, hR.2.2 (hR.2.1 hab) hac⟩,
end

lemma inversa_dcha :
  function.right_inverse relacionP (@cociente A) :=
begin
  intro P,
  ext X,
  show (∃ (a : A), X = clase _ a) ↔ X ∈ Bloques P,
  split,
  { rintro ⟨a, rfl⟩,
    obtain ⟨X, hX, haX⟩ := Hrecubren P a,
    convert hX,
    ext b,
    rw pertenece_clase_syss,
    split,
    { intro hba,
      obtain ⟨Y, hY, hbY⟩ := Hrecubren P b,
      specialize hba Y hY hbY,
      convert hbY,
      exact iguales_si_comun hX hY haX hba, },
    { intros hbX Y hY hbY,
      apply pertenece_si_pertenece hX hY hbX hbY haX, }},
  { intro hX,
    rcases Hno_vacios P X hX with ⟨a, ha⟩,
    use a,
    ext b,
    split,
    { intro hbX,
      rw pertenece_clase_syss,
      intros Y hY hbY,
      exact pertenece_si_pertenece hX hY hbX hbY ha, },
    { rw pertenece_clase_syss,
      intro hba,
      obtain ⟨Y, hY, hbY⟩ := Hrecubren P b,
      specialize hba Y hY hbY,
      exact pertenece_si_pertenece hY hX hba ha hbY, }}
end

theorem equivalencia_particiones
  (A : Type)
  : {R : A → A → Prop // equivalence R} ≃ particion A :=
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
  rintros X Y ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, hca, hcb⟩,
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

lemma inversa_izq :
  function.left_inverse relacionP (@cociente A) :=
begin
  rintro ⟨R, hR⟩,
  simp [relacionP, cociente],
  ext a b,
  exact ⟨λ hab, hR.2.1 (hab a (hR.1 a)),
         λ hab c hac, hR.2.2 (hR.2.1 hab) hac⟩,
end

lemma inversa_dcha :
  function.right_inverse relacionP (@cociente A) :=
begin
  intro P,
  ext X,
  show (∃ (a : A), X = clase _ a) ↔ X ∈ Bloques P,
  split,
  { rintro ⟨a, rfl⟩,
    obtain ⟨X, hX, haX⟩ := Hrecubren P a,
    convert hX,
    ext b,
    rw pertenece_clase_syss,
    split,
    { intro hba,
      obtain ⟨Y, hY, hbY⟩ := Hrecubren P b,
      specialize hba Y hY hbY,
      convert hbY,
      exact iguales_si_comun hX hY haX hba, },
    { intros hbX Y hY hbY,
      apply pertenece_si_pertenece hX hY hbX hbY haX, }},
  { intro hX,
    rcases Hno_vacios P X hX with ⟨a, ha⟩,
    use a,
    ext b,
    split,
    { intro hbX,
      rw pertenece_clase_syss,
      intros Y hY hbY,
      exact pertenece_si_pertenece hX hY hbX hbY ha, },
    { rw pertenece_clase_syss,
      intro hba,
      obtain ⟨Y, hY, hbY⟩ := Hrecubren P b,
      specialize hba Y hY hbY,
      exact pertenece_si_pertenece hY hX hba ha hbY, }}
end

theorem equivalencia_particiones
  (A : Type)
  : {R : A → A → Prop // equivalence R} ≃ particion A :=
{ to_fun    := cociente,
  inv_fun   := relacionP,
  left_inv  := inversa_izq,
  right_inv := inversa_dcha, }

end particion
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Isomorfismo_entre_relaciones_de_equivalencia_y_particiones.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
