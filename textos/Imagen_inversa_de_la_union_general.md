---
Título: Imagen inversa de la unión general
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   f⁻¹[⋃ i, B i] = ⋃ i, f⁻¹[B i]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*} {I : Type*}
variable  f : α → β
variables B : I → set β

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*} {I : Type*}
variable  f : α → β
variables B : I → set β

-- 1ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
begin
  ext x,
  split,
  { intro hx,
    rw mem_preimage at hx,
    rw mem_Union at hx,
    cases hx with i fxBi,
    rw mem_Union,
    use i,
    apply mem_preimage.mpr,
    exact fxBi, },
  { intro hx,
    rw mem_preimage,
    rw mem_Union,
    rw mem_Union at hx,
    cases hx with i xBi,
    use i,
    rw mem_preimage at xBi,
    exact xBi, },
end

-- 2ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
preimage_Union

-- 3ª demostración
-- ===============

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by  simp
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Imagen_inversa_de_la_union_general.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Imagen_inversa_de_la_union_general
imports Main
begin

(* 1ª demostración *)

lemma "f -` (⋃ i ∈ I. B i) = (⋃ i ∈ I. f -` B i)"
proof (rule equalityI)
  show "f -` (⋃ i ∈ I. B i) ⊆ (⋃ i ∈ I. f -` B i)"
  proof (rule subsetI)
    fix x
    assume "x ∈ f -` (⋃ i ∈ I. B i)"
    then have "f x ∈ (⋃ i ∈ I. B i)"
      by (rule vimageD)
    then show "x ∈ (⋃ i ∈ I. f -` B i)"
    proof (rule UN_E)
      fix i
      assume "i ∈ I"
      assume "f x ∈ B i"
      then have "x ∈ f -` B i"
        by (rule vimageI2)
      with ‹i ∈ I› show "x ∈ (⋃ i ∈ I. f -` B i)"
        by (rule UN_I)
    qed
  qed
next
  show "(⋃ i ∈ I. f -` B i) ⊆ f -` (⋃ i ∈ I. B i)"
  proof (rule subsetI)
    fix x
    assume "x ∈ (⋃ i ∈ I. f -` B i)"
    then show "x ∈ f -` (⋃ i ∈ I. B i)"
    proof (rule UN_E)
      fix i
      assume "i ∈ I"
      assume "x ∈ f -` B i"
      then have "f x ∈ B i"
        by (rule vimageD)
      with ‹i ∈ I› have "f x ∈ (⋃ i ∈ I. B i)"
        by (rule UN_I)
      then show "x ∈ f -` (⋃ i ∈ I. B i)"
        by (rule vimageI2)
    qed
  qed
qed

(* 2ª demostración *)

lemma "f -` (⋃ i ∈ I. B i) = (⋃ i ∈ I. f -` B i)"
proof
  show "f -` (⋃ i ∈ I. B i) ⊆ (⋃ i ∈ I. f -` B i)"
  proof
    fix x
    assume "x ∈ f -` (⋃ i ∈ I. B i)"
    then have "f x ∈ (⋃ i ∈ I. B i)" by simp
    then show "x ∈ (⋃ i ∈ I. f -` B i)"
    proof
      fix i
      assume "i ∈ I"
      assume "f x ∈ B i"
      then have "x ∈ f -` B i" by simp
      with ‹i ∈ I› show "x ∈ (⋃ i ∈ I. f -` B i)" by (rule UN_I)
    qed
  qed
next
  show "(⋃ i ∈ I. f -` B i) ⊆ f -` (⋃ i ∈ I. B i)"
  proof
    fix x
    assume "x ∈ (⋃ i ∈ I. f -` B i)"
    then show "x ∈ f -` (⋃ i ∈ I. B i)"
    proof
      fix i
      assume "i ∈ I"
      assume "x ∈ f -` B i"
      then have "f x ∈ B i" by simp
      with ‹i ∈ I› have "f x ∈ (⋃ i ∈ I. B i)" by (rule UN_I)
      then show "x ∈ f -` (⋃ i ∈ I. B i)" by simp
    qed
  qed
qed

(* 3ª demostración *)

lemma "f -` (⋃ i ∈ I. B i) = (⋃ i ∈ I. f -` B i)"
  by (simp only: vimage_UN)

(* 4ª demostración *)

lemma "f -` (⋃ i ∈ I. B i) = (⋃ i ∈ I. f -` B i)"
  by auto

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
