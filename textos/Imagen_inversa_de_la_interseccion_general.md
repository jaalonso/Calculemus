---
Título: Imagen inversa de la intersección general
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   f⁻¹[⋂ i, B(i)] = ⋂ i, f⁻¹[B(i)]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*} {I : Type*}
variable  f : α → β
variables B : I → set β

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
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

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
begin
  ext x,
  split,
  { intro hx,
    apply mem_Inter_of_mem,
    intro i,
    rw mem_preimage,
    rw mem_preimage at hx,
    rw mem_Inter at hx,
    exact hx i, },
  { intro hx,
    rw mem_preimage,
    rw mem_Inter,
    intro i,
    rw ← mem_preimage,
    rw mem_Inter at hx,
    exact hx i, },
end

-- 2ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
begin
  ext x,
  calc  (x ∈ f ⁻¹' ⋂ (i : I), B i)
      ↔ f x ∈ ⋂ (i : I), B i       : mem_preimage
  ... ↔ (∀ i : I, f x ∈ B i)       : mem_Inter
  ... ↔ (∀ i : I, x ∈ f ⁻¹' B i)   : iff_of_eq rfl
  ... ↔ x ∈ ⋂ (i : I), f ⁻¹' B i   : mem_Inter.symm,
end

-- 3ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
begin
  ext x,
  simp,
end

-- 4ª demostración
-- ===============

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext, simp }
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Imagen_inversa_de_la_interseccion_general.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Imagen_inversa_de_la_interseccion_general
imports Main
begin

(* 1ª demostración *)

lemma "f -` (⋂ i ∈ I. B i) = (⋂ i ∈ I. f -` B i)"
proof (rule equalityI)
  show "f -` (⋂ i ∈ I. B i) ⊆ (⋂ i ∈ I. f -` B i)"
  proof (rule subsetI)
    fix x
    assume "x ∈ f -` (⋂ i ∈ I. B i)"
    show "x ∈ (⋂ i ∈ I. f -` B i)"
    proof (rule INT_I)
      fix i
      assume "i ∈ I"
      have "f x ∈ (⋂ i ∈ I. B i)"
        using ‹x ∈ f -` (⋂ i ∈ I. B i)› by (rule vimageD)
      then have "f x ∈ B i"
        using ‹i ∈ I› by (rule INT_D)
      then show "x ∈ f -` B i"
        by (rule vimageI2)
    qed
  qed
next
  show "(⋂ i ∈ I. f -` B i) ⊆ f -` (⋂ i ∈ I. B i)"
  proof (rule subsetI)
    fix x
    assume "x ∈ (⋂ i ∈ I. f -` B i)"
    have "f x ∈ (⋂ i ∈ I. B i)"
    proof (rule INT_I)
      fix i
      assume "i ∈ I"
      with ‹x ∈ (⋂ i ∈ I. f -` B i)› have "x ∈ f -` B i"
        by (rule INT_D)
      then show "f x ∈ B i"
        by (rule vimageD)
    qed
    then show "x ∈ f -` (⋂ i ∈ I. B i)"
      by (rule vimageI2)
  qed
qed

(* 2ª demostración *)

lemma "f -` (⋂ i ∈ I. B i) = (⋂ i ∈ I. f -` B i)"
proof
  show "f -` (⋂ i ∈ I. B i) ⊆ (⋂ i ∈ I. f -` B i)"
  proof (rule subsetI)
    fix x
    assume hx : "x ∈ f -` (⋂ i ∈ I. B i)"
    show "x ∈ (⋂ i ∈ I. f -` B i)"
    proof
      fix i
      assume "i ∈ I"
      have "f x ∈ (⋂ i ∈ I. B i)" using hx by simp
      then have "f x ∈ B i" using ‹i ∈ I› by simp
      then show "x ∈ f -` B i" by simp
    qed
  qed
next
  show "(⋂ i ∈ I. f -` B i) ⊆ f -` (⋂ i ∈ I. B i)"
  proof
    fix x
    assume "x ∈ (⋂ i ∈ I. f -` B i)"
    have "f x ∈ (⋂ i ∈ I. B i)"
    proof
      fix i
      assume "i ∈ I"
      with ‹x ∈ (⋂ i ∈ I. f -` B i)› have "x ∈ f -` B i" by simp
      then show "f x ∈ B i" by simp
    qed
    then show "x ∈ f -` (⋂ i ∈ I. B i)" by simp
  qed
qed

(* 3 demostración *)

lemma "f -` (⋂ i ∈ I. B i) = (⋂ i ∈ I. f -` B i)"
  by (simp only: vimage_INT)

(* 4ª demostración *)

lemma "f -` (⋂ i ∈ I. B i) = (⋂ i ∈ I. f -` B i)"
  by auto

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
