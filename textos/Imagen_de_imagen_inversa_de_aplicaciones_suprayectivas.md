---
Título: Imagen de imagen inversa de aplicaciones suprayectivas
Autor:  José A. Alonso
---

Demostrar que si f es suprayectiva, entonces
<pre lang="text">
   u ⊆ f[f⁻¹[u]]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set function

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  u : set β

example
  (h : surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.set.basic
open set function

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  u : set β

-- 1ª demostración
-- ===============

example
  (h : surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
begin
  intros y yu,
  cases h y with x fxy,
  use x,
  split,
  { apply mem_preimage.mpr,
    rw fxy,
    exact yu },
  { exact fxy },
end

-- 2ª demostración
-- ===============

example
  (h : surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
begin
  intros y yu,
  cases h y with x fxy,
  use x,
  split,
  { show f x ∈ u,
    rw fxy,
    exact yu },
  { exact fxy },
end

-- 3ª demostración
-- ===============

example
  (h : surjective f)
  : u ⊆ f '' (f⁻¹' u) :=
begin
  intros y yu,
  cases h y with x fxy,
  by finish,
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://bit.ly/3prF7Pz" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Imagen_de_imagen_inversa_de_aplicaciones_suprayectivas
imports Main
begin

section ‹1ª demostración›

lemma
  assumes "surj f"
  shows "u ⊆ f ` (f -` u)"
proof (rule subsetI)
  fix y
  assume "y ∈ u"
  have "∃x. y = f x"
    using ‹surj f› by (rule surjD)
  then obtain x where "y = f x"
    by (rule exE)
  then have "f x ∈ u"
    using ‹y ∈ u› by (rule subst)
  then have "x ∈ f -` u"
    by (simp only: vimage_eq)
  then have "f x ∈ f ` (f -` u)"
    by (rule imageI)
  with ‹y = f x› show "y ∈ f ` (f -` u)"
    by (rule ssubst)
qed

section ‹2ª demostración›

lemma
  assumes "surj f"
  shows "u ⊆ f ` (f -` u)"
proof
  fix y
  assume "y ∈ u"
  have "∃x. y = f x"
    using ‹surj f› by (rule surjD)
  then obtain x where "y = f x"
    by (rule exE)
  then have "f x ∈ u"
    using ‹y ∈ u› by simp
  then have "x ∈ f -` u"
    by simp
  then have "f x ∈ f ` (f -` u)"
    by simp
  with ‹y = f x› show "y ∈ f ` (f -` u)"
    by simp
qed

section ‹3ª demostración›

lemma
  assumes "surj f"
  shows "u ⊆ f ` (f -` u)"
  using assms
  by (simp only: surj_image_vimage_eq)

section ‹4ª demostración›

lemma
  assumes "surj f"
  shows "u ⊆ f ` (f -` u)"
  using assms
  unfolding surj_def
  by auto

section ‹5ª demostración›

lemma
  assumes "surj f"
  shows "u ⊆ f ` (f -` u)"
  using assms
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
