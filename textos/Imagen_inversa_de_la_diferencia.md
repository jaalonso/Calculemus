---
Título: Imagen inversa de la diferencia
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   f⁻¹[u] - f⁻¹[v] ⊆ f⁻¹[u - v]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables u v : set β

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables u v : set β

-- 1ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  intros x hx,
  rw mem_preimage,
  split,
  { rw ← mem_preimage,
    exact hx.1, },
  { dsimp,
    rw ← mem_preimage,
    exact hx.2, },
end

-- 2ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  intros x hx,
  split,
  { exact hx.1, },
  { exact hx.2, },
end

-- 3ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  intros x hx,
  exact ⟨hx.1, hx.2⟩,
end

-- 4ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
begin
  rintros x ⟨h1, h2⟩,
  exact ⟨h1, h2⟩,
end

-- 5ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
subset.rfl

-- 6ª demostración
-- ===============

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
by finish
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Imagen_inversa_de_la_diferencia.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,

Otras soluciones: En los comentarios se pueden escribir nuevas soluciones. El código se debe escribir entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Imagen_inversa_de_la_diferencia
imports Main
begin

(* 1ª demostración *)

lemma "f -` u - f -` v ⊆ f -` (u - v)"
proof (rule subsetI)
  fix x
  assume "x ∈ f -` u - f -` v"
  then have "f x ∈ u - v"
  proof (rule DiffE)
    assume "x ∈ f -` u"
    assume "x ∉ f -` v"
    have "f x ∈ u"
      using ‹x ∈ f -` u› by (rule vimageD)
    moreover
    have "f x ∉ v"
    proof (rule notI)
      assume "f x ∈ v"
      then have "x ∈ f -` v"
        by (rule vimageI2)
      with ‹x ∉ f -` v› show False
        by (rule notE)
    qed
    ultimately show "f x ∈ u - v"
      by (rule DiffI)
  qed
  then show "x ∈ f -` (u - v)"
    by (rule vimageI2)
qed

(* 2ª demostración *)

lemma "f -` u - f -` v ⊆ f -` (u - v)"
proof
  fix x
  assume "x ∈ f -` u - f -` v"
  then have "f x ∈ u - v"
  proof
    assume "x ∈ f -` u"
    assume "x ∉ f -` v"
    have "f x ∈ u" using ‹x ∈ f -` u› by simp
    moreover
    have "f x ∉ v"
    proof
      assume "f x ∈ v"
      then have "x ∈ f -` v" by simp
      with ‹x ∉ f -` v› show False by simp
    qed
    ultimately show "f x ∈ u - v" by simp
  qed
  then show "x ∈ f -` (u - v)" by simp
qed

(* 3ª demostración *)

lemma "f -` u - f -` v ⊆ f -` (u - v)"
  by (simp only: vimage_Diff)

(* 4ª demostración *)

lemma "f -` u - f -` v ⊆ f -` (u - v)"
  by auto

end
</pre>

Otras soluciones: En los comentarios se pueden escribir nuevas soluciones. El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
