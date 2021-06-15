---
Título: Imagen de la intersección general
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   f[⋂ i, A i] ⊆ ⋂ i, f[A i]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*} {I : Type*}
variable  f : α → β
variables A : ℕ → set α

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*} {I : Type*}
variable  f : α → β
variables A : ℕ → set α

-- 1ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intros y h,
  apply mem_Inter_of_mem,
  intro i,
  cases h with x hx,
  cases hx with xIA fxy,
  rw ← fxy,
  apply mem_image_of_mem,
  exact mem_Inter.mp xIA i,
end

-- 2ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intros y h,
  apply mem_Inter_of_mem,
  intro i,
  rcases h with ⟨x, xIA, rfl⟩,
  exact mem_image_of_mem f (mem_Inter.mp xIA i),
end

-- 3ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intro y,
  simp,
  intros x xIA fxy i,
  use [x, xIA i, fxy],
end

-- 4ª demostración
-- ===============

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
by tidy
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Imagen_de_la_interseccion_general.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Imagen_de_la_interseccion_general
imports Main
begin

(* 1ª demostración *)

lemma "f ` (⋂ i ∈ I. A i) ⊆ (⋂ i ∈ I. f ` A i)"
proof (rule subsetI)
  fix y
  assume "y ∈ f ` (⋂ i ∈ I. A i)"
  then show "y ∈ (⋂ i ∈ I. f ` A i)"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume xIA : "x ∈ (⋂ i ∈ I. A i)"
    have "f x ∈ (⋂ i ∈ I. f ` A i)"
    proof (rule INT_I)
      fix i
      assume "i ∈ I"
      with xIA have "x ∈ A i"
        by (rule INT_D)
      then show "f x ∈ f ` A i"
        by (rule imageI)
    qed
    with ‹y = f x› show "y ∈ (⋂ i ∈ I. f ` A i)"
      by (rule ssubst)
  qed
qed

(* 2ª demostración *)

lemma "f ` (⋂ i ∈ I. A i) ⊆ (⋂ i ∈ I. f ` A i)"
proof
  fix y
  assume "y ∈ f ` (⋂ i ∈ I. A i)"
  then show "y ∈ (⋂ i ∈ I. f ` A i)"
  proof
    fix x
    assume "y = f x"
    assume xIA : "x ∈ (⋂ i ∈ I. A i)"
    have "f x ∈ (⋂ i ∈ I. f ` A i)"
    proof
      fix i
      assume "i ∈ I"
      with xIA have "x ∈ A i" by simp
      then show "f x ∈ f ` A i" by simp
    qed
    with ‹y = f x› show "y ∈ (⋂ i ∈ I. f ` A i)" by simp
  qed
qed

(* 3ª demostración *)

lemma "f ` (⋂ i ∈ I. A i) ⊆ (⋂ i ∈ I. f ` A i)"
  by auto

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
