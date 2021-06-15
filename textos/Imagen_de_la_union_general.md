---
Título: Imagen de la unión general
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   f [⋃ i, A i] = ⋃ i, f [A i]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*} {I : Type*}
variable  f : α → β
variables A : ℕ → set α

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
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

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y,
  split,
  { intro hy,
    rw mem_image at hy,
    cases hy with x hx,
    cases hx with xUA fxy,
    rw mem_Union at xUA,
    cases xUA with i xAi,
    rw mem_Union,
    use i,
    rw ← fxy,
    apply mem_image_of_mem,
    exact xAi, },
  { intro hy,
    rw mem_Union at hy,
    cases hy with i yAi,
    cases yAi with x hx,
    cases hx with xAi fxy,
    rw ← fxy,
    apply mem_image_of_mem,
    rw mem_Union,
    use i,
    exact xAi, },
end

-- 2ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y,
  simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxy⟩,
    use [i, x, xAi, fxy] },
  { rintros ⟨i, x, xAi, fxy⟩,
    exact ⟨x, ⟨i, xAi⟩, fxy⟩ },
end

-- 3ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
by tidy

-- 4ª demostración
-- ===============

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
image_Union
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Imagen_de_la_union_general.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Imagen_de_la_union_general
imports Main
begin

(* 1ª demostración *)

lemma "f ` (⋃ i ∈ I. A i) = (⋃ i ∈ I. f ` A i)"
proof (rule equalityI)
  show "f ` (⋃ i ∈ I. A i) ⊆ (⋃ i ∈ I. f ` A i)"
  proof (rule subsetI)
    fix y
    assume "y ∈ f ` (⋃ i ∈ I. A i)"
    then show "y ∈ (⋃ i ∈ I. f ` A i)"
    proof (rule imageE)
      fix x
      assume "y = f x"
      assume "x ∈ (⋃ i ∈ I. A i)"
      then have "f x ∈ (⋃ i ∈ I. f ` A i)"
      proof (rule UN_E)
        fix i
        assume "i ∈ I"
        assume "x ∈ A i"
        then have "f x ∈ f ` A i"
          by (rule imageI)
        with ‹i ∈ I› show "f x ∈ (⋃ i ∈ I. f ` A i)"
          by (rule UN_I)
      qed
      with ‹y = f x› show "y ∈ (⋃ i ∈ I. f ` A i)"
        by (rule ssubst)
    qed
  qed
next
  show "(⋃ i ∈ I. f ` A i) ⊆ f ` (⋃ i ∈ I. A i)"
  proof (rule subsetI)
    fix y
    assume "y ∈ (⋃ i ∈ I. f ` A i)"
    then show "y ∈ f ` (⋃ i ∈ I. A i)"
    proof (rule UN_E)
      fix i
      assume "i ∈ I"
      assume "y ∈ f ` A i"
      then show "y ∈ f ` (⋃ i ∈ I. A i)"
      proof (rule imageE)
        fix x
        assume "y = f x"
        assume "x ∈ A i"
        with ‹i ∈ I› have "x ∈ (⋃ i ∈ I. A i)"
          by (rule UN_I)
        then have "f x ∈ f ` (⋃ i ∈ I. A i)"
          by (rule imageI)
        with ‹y = f x› show "y ∈ f ` (⋃ i ∈ I. A i)"
          by (rule ssubst)
      qed
    qed
  qed
qed

(* 2ª demostración *)

lemma "f ` (⋃ i ∈ I. A i) = (⋃ i ∈ I. f ` A i)"
proof
  show "f ` (⋃ i ∈ I. A i) ⊆ (⋃ i ∈ I. f ` A i)"
  proof
    fix y
    assume "y ∈ f ` (⋃ i ∈ I. A i)"
    then show "y ∈ (⋃ i ∈ I. f ` A i)"
    proof
      fix x
      assume "y = f x"
      assume "x ∈ (⋃ i ∈ I. A i)"
      then have "f x ∈ (⋃ i ∈ I. f ` A i)"
      proof
        fix i
        assume "i ∈ I"
        assume "x ∈ A i"
        then have "f x ∈ f ` A i" by simp
        with ‹i ∈ I› show "f x ∈ (⋃ i ∈ I. f ` A i)" by (rule UN_I)
      qed
      with ‹y = f x› show "y ∈ (⋃ i ∈ I. f ` A i)" by simp
    qed
  qed
next
  show "(⋃ i ∈ I. f ` A i) ⊆ f ` (⋃ i ∈ I. A i)"
  proof
    fix y
    assume "y ∈ (⋃ i ∈ I. f ` A i)"
    then show "y ∈ f ` (⋃ i ∈ I. A i)"
    proof
      fix i
      assume "i ∈ I"
      assume "y ∈ f ` A i"
      then show "y ∈ f ` (⋃ i ∈ I. A i)"
      proof
        fix x
        assume "y = f x"
        assume "x ∈ A i"
        with ‹i ∈ I› have "x ∈ (⋃ i ∈ I. A i)" by (rule UN_I)
        then have "f x ∈ f ` (⋃ i ∈ I. A i)" by simp
        with ‹y = f x› show "y ∈ f ` (⋃ i ∈ I. A i)" by simp
      qed
    qed
  qed
qed

(* 3ª demostración *)

lemma "f ` (⋃ i ∈ I. A i) = (⋃ i ∈ I. f ` A i)"
  by (simp only: image_UN)

(* 4ª demostración *)

lemma "f ` (⋃ i ∈ I. A i) = (⋃ i ∈ I. f ` A i)"
  by auto

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
