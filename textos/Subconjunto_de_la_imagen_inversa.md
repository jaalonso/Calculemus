---
Título: Subconjunto de la imagen inversa
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   f[s] ⊆ u ↔ s ⊆ f⁻¹[u]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α
variable  u : set β

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α
variable  u : set β

-- 1ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
begin
  split,
  { intros h x xs,
    apply mem_preimage.mpr,
    apply h,
    apply mem_image_of_mem,
    exact xs, },
  { intros h y hy,
    rcases hy with ⟨x, xs, fxy⟩,
    rw ← fxy,
    exact h xs, },
end

-- 2ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
begin
  split,
  { intros h x xs,
    apply h,
    apply mem_image_of_mem,
    exact xs, },
  { rintros h y ⟨x, xs, rfl⟩,
    exact h xs, },
end

-- 3ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
image_subset_iff

-- 4ª demostración
-- ===============

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
by simp
</pre>

Se puede interactuar con la prueba anterior en <a href="https://bit.ly/3wZXj5l" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Subconjunto_de_la_imagen_inversa
imports Main
begin

section ‹1ª demostración›

lemma "f ` s ⊆ u ⟷ s ⊆ f -` u"
proof (rule iffI)
  assume "f ` s ⊆ u"
  show "s ⊆ f -` u"
  proof (rule subsetI)
    fix x
    assume "x ∈ s"
    then have "f x ∈ f ` s"
      by (simp only: imageI)
    then have "f x ∈ u"
      using ‹f ` s ⊆ u› by (rule set_rev_mp)
    then show "x ∈ f -` u"
      by (simp only: vimageI)
  qed
next
  assume "s ⊆ f -` u"
  show "f ` s ⊆ u"
  proof (rule subsetI)
    fix y
    assume "y ∈ f ` s"
    then show "y ∈ u"
    proof
      fix x
      assume "y = f x"
      assume "x ∈ s"
      then have "x ∈ f -` u"
        using ‹s ⊆ f -` u› by (rule set_rev_mp)
      then have "f x ∈ u"
        by (rule vimageD)
      with ‹y = f x› show "y ∈ u"
        by (rule ssubst)
    qed
  qed
qed

section ‹2ª demostración›

lemma "f ` s ⊆ u ⟷ s ⊆ f -` u"
proof
  assume "f ` s ⊆ u"
  show "s ⊆ f -` u"
  proof
    fix x
    assume "x ∈ s"
    then have "f x ∈ f ` s"
      by simp
    then have "f x ∈ u"
      using ‹f ` s ⊆ u› by (simp add: set_rev_mp)
    then show "x ∈ f -` u"
      by simp
  qed
next
  assume "s ⊆ f -` u"
  show "f ` s ⊆ u"
  proof
    fix y
    assume "y ∈ f ` s"
    then show "y ∈ u"
    proof
      fix x
      assume "y = f x"
      assume "x ∈ s"
      then have "x ∈ f -` u"
        using ‹s ⊆ f -` u› by (simp only: set_rev_mp)
      then have "f x ∈ u"
        by simp
      with ‹y = f x› show "y ∈ u"
        by simp
    qed
  qed
qed

section ‹3ª demostración›

lemma "f ` s ⊆ u ⟷ s ⊆ f -` u"
  by (simp only: image_subset_iff_subset_vimage)

section ‹4ª demostración›

lemma "f ` s ⊆ u ⟷ s ⊆ f -` u"
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
