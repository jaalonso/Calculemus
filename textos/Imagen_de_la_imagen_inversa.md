---
Título: Imagen de la imagen inversa
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   f[f¹[u]] ⊆ u
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  u : set β

example : f '' (f⁻¹' u) ⊆ u :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.set.basic
open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  u : set β

-- 1ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
begin
  intros y h,
  cases h with x h2,
  cases h2 with hx fxy,
  rw ← fxy,
  exact hx,
end

-- 2ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
begin
  intros y h,
  rcases h with ⟨x, hx, fxy⟩,
  rw ← fxy,
  exact hx,
end

-- 3ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
begin
  rintros y ⟨x, hx, fxy⟩,
  rw ← fxy,
  exact hx,
end

-- 4ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
begin
  rintros y ⟨x, hx, rfl⟩,
  exact hx,
end

-- 5ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
image_preimage_subset f u

-- 6ª demostración
-- ===============

example : f '' (f⁻¹' u) ⊆ u :=
by simp
</pre>

Se puede interactuar con la prueba anterior en <a href="https://bit.ly/3z5qxBD" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Imagen_de_la_imagen_inversa
imports Main
begin

section ‹1ª demostración›

lemma "f ` (f -` u) ⊆ u"
proof (rule subsetI)
  fix y
  assume "y ∈ f ` (f -` u)"
  then show "y ∈ u"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x ∈ f -` u"
    then have "f x ∈ u"
      by (rule vimageD)
    with ‹y = f x› show "y ∈ u"
      by (rule ssubst)
  qed
qed

section ‹2ª demostración›

lemma "f ` (f -` u) ⊆ u"
proof
  fix y
  assume "y ∈ f ` (f -` u)"
  then show "y ∈ u"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ f -` u"
    then have "f x ∈ u"
      by simp
    with ‹y = f x› show "y ∈ u"
      by simp
  qed
qed

section ‹3ª demostración›

lemma "f ` (f -` u) ⊆ u"
  by (simp only: image_vimage_subset)

section ‹4ª demostración›

lemma "f ` (f -` u) ⊆ u"
  by auto

end
</pre>
[/expand]

[expand title="Nuevas soluciones"]
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
[/expand]
