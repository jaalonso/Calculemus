---
Título: Unión con la imagen inversa
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   s ∪ f⁻¹[v] ⊆ f¹[f[s] ∪ v]]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α
variable  v : set β

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
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

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
begin
  intros x hx,
  rw mem_preimage,
  cases hx with xs xv,
  { apply mem_union_left,
    apply mem_image_of_mem,
    exact xs, },
  { apply mem_union_right,
    rw ← mem_preimage,
    exact xv, },
end

-- 2ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
begin
  intros x hx,
  cases hx with xs xv,
  { apply mem_union_left,
    apply mem_image_of_mem,
    exact xs, },
  { apply mem_union_right,
    exact xv, },
end

-- 3ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
begin
  rintros x (xs | xv),
  { left,
    exact mem_image_of_mem f xs, },
  { right,
    exact xv, },
end

-- 4ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
begin
  rintros x (xs | xv),
  { exact or.inl (mem_image_of_mem f xs), },
  { exact or.inr xv, },
end

-- 5ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
begin
  intros x h,
  exact or.elim h (λ xs, or.inl (mem_image_of_mem f xs)) or.inr,
end

-- 6ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
λ x h, or.elim h (λ xs, or.inl (mem_image_of_mem f xs)) or.inr

-- 7ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
begin
  rintros x (xs | xv),
  { show f x ∈ f '' s ∪ v,
    use [x, xs, rfl] },
  { show f x ∈ f '' s ∪ v,
    right,
    apply xv },
end

-- 8ª demostración
-- ===============

example : s ∪ f ⁻¹' v ⊆ f ⁻¹' (f '' s ∪ v) :=
union_preimage_subset s v f
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

lemma "s ∪ f -` v ⊆ f -` (f ` s ∪ v)"
proof (rule subsetI)
  fix x
  assume "x ∈ s ∪ f -` v"
  then have "f x ∈ f ` s ∪ v"
  proof (rule UnE)
    assume "x ∈ s"
    then have "f x ∈ f ` s"
      by (rule imageI)
    then show "f x ∈ f ` s ∪ v"
      by (rule UnI1)
  next
    assume "x ∈ f -` v"
    then have "f x ∈ v"
      by (rule vimageD)
    then show "f x ∈ f ` s ∪ v"
      by (rule UnI2)
  qed
  then show "x ∈ f -` (f ` s ∪ v)"
    by (rule vimageI2)
qed

(* 2ª demostración *)

lemma "s ∪ f -` v ⊆ f -` (f ` s ∪ v)"
proof
  fix x
  assume "x ∈ s ∪ f -` v"
  then have "f x ∈ f ` s ∪ v"
  proof
    assume "x ∈ s"
    then have "f x ∈ f ` s" by simp
    then show "f x ∈ f ` s ∪ v" by simp
  next
    assume "x ∈ f -` v"
    then have "f x ∈ v" by simp
    then show "f x ∈ f ` s ∪ v" by simp
  qed
  then show "x ∈ f -` (f ` s ∪ v)" by simp
qed

(* 3ª demostración *)

lemma "s ∪ f -` v ⊆ f -` (f ` s ∪ v)"
proof
  fix x
  assume "x ∈ s ∪ f -` v"
  then have "f x ∈ f ` s ∪ v"
  proof
    assume "x ∈ s"
    then show "f x ∈ f ` s ∪ v" by simp
  next
    assume "x ∈ f -` v"
    then show "f x ∈ f ` s ∪ v" by simp
  qed
  then show "x ∈ f -` (f ` s ∪ v)" by simp
qed

(* 4ª demostración *)

lemma "s ∪ f -` v ⊆ f -` (f ` s ∪ v)"
  by auto

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
