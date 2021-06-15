---
Título: Unión con la imagen inversa
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   s ∩ f⁻¹[v] ⊆ f⁻¹[f[s] ∩ v]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α
variable  v : set β

example : s ∩ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∩ v) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α
variable  v : set β

-- 1ª demostración
-- ===============

example : s ∩ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∩ v) :=
begin
  intros x hx,
  rw mem_preimage,
  split,
  { apply mem_image_of_mem,
    exact hx.1, },
  { rw ← mem_preimage,
    exact hx.2, },
end

-- 2ª demostración
-- ===============

example : s ∩ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∩ v) :=
begin
  rintros x ⟨xs, xv⟩,
  split,
  { exact mem_image_of_mem f xs, },
  { exact xv, },
end

-- 3ª demostración
-- ===============

example : s ∩ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∩ v) :=
begin
  rintros x ⟨xs, xv⟩,
  exact ⟨mem_image_of_mem f xs, xv⟩,
end

-- 4ª demostración
-- ===============

example : s ∩ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∩ v) :=
begin
  rintros x ⟨xs, xv⟩,
  show f x ∈ f '' s ∩ v,
  split,
  { use [x, xs, rfl] },
  { exact xv },
end

-- 5ª demostración
-- ===============

example : s ∩ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∩ v) :=
inter_preimage_subset s v f
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Union_con_la_imagen_inversa.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Union_con_la_imagen_inversa
imports Main
begin

(* 1ª demostración *)

lemma "s ∩ f -`  v ⊆ f -` (f ` s ∩ v)"
proof (rule subsetI)
  fix x
  assume "x ∈ s ∩ f -`  v"
  have "f x ∈ f ` s"
  proof -
    have "x ∈ s"
      using ‹x ∈ s ∩ f -`  v› by (rule IntD1)
    then show "f x ∈ f ` s"
      by (rule imageI)
  qed
  moreover
  have "f x ∈ v"
  proof -
    have "x ∈ f -`  v"
      using ‹x ∈ s ∩ f -`  v› by (rule IntD2)
    then show "f x ∈ v"
      by (rule vimageD)
  qed
  ultimately have "f x ∈ f ` s ∩ v"
    by (rule IntI)
  then show "x ∈ f -` (f ` s ∩ v)"
    by (rule vimageI2)
qed

(* 2ª demostración *)

lemma "s ∩ f -`  v ⊆ f -` (f ` s ∩ v)"
proof (rule subsetI)
  fix x
  assume "x ∈ s ∩ f -`  v"
  have "f x ∈ f ` s"
  proof -
    have "x ∈ s" using ‹x ∈ s ∩ f -`  v› by simp
    then show "f x ∈ f ` s" by simp
  qed
  moreover
  have "f x ∈ v"
  proof -
    have "x ∈ f -`  v" using ‹x ∈ s ∩ f -`  v› by simp
    then show "f x ∈ v" by simp
  qed
  ultimately have "f x ∈ f ` s ∩ v" by simp
  then show "x ∈ f -` (f ` s ∩ v)" by simp
qed

(* 3ª demostración *)

lemma "s ∩ f -`  v ⊆ f -` (f ` s ∩ v)"
  by auto

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
