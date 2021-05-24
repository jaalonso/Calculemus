---
Título: Conmutatividad de la intersección
Autor:  José A. Alonso
---

Demostrar que

> s ∩ t = t ∩ s

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t u : set α

example : s ∩ t = t ∩ s :=
sorry
</pre>

**Notas**

* En [este enlace](https://bit.ly/3yw2r2O) se puede escribir las soluciones en Lean.
* A continuación se muestran algunas soluciones (que se pueden probar en [este enlace](https://bit.ly/3hNkUBU)).
* En los comentarios se pueden publicar otras soluciones, en Lean o en otros sistemas de razonamiento.
  + Para publicar las demostraciones en Lean se deben de escribir entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
  + Para publicar las demostraciones en Isabelle/HOL se deben de escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;

**Soluciones con Lean**

<pre lang="lean">
import data.set.basic
open set

variable {α : Type}
variables s t u : set α

-- 1ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext x,
  simp only [mem_inter_eq],
  split,
  { intro h,
    split,
    { exact h.2, },
    { exact h.1, }},
  { intro h,
    split,
    { exact h.2, },
    { exact h.1, }},
end

-- 2ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext,
  simp only [mem_inter_eq],
  exact ⟨λ h, ⟨h.2, h.1⟩,
         λ h, ⟨h.2, h.1⟩⟩,
end

-- 3ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext,
  exact ⟨λ h, ⟨h.2, h.1⟩,
         λ h, ⟨h.2, h.1⟩⟩,
end

-- 4ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext x,
  simp only [mem_inter_eq],
  split,
  { rintros ⟨xs, xt⟩,
    exact ⟨xt, xs⟩ },
  { rintros ⟨xt, xs⟩,
    exact ⟨xs, xt⟩ },
end

-- 5ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext x,
  exact and.comm,
end

-- 6ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
ext (λ x, and.comm)

-- 7ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by ext x; simp [and.comm]

-- 8ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
inter_comm s t

-- 9ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by finish
</pre>

**Soluciones con Isabelle/HOL**

<pre lang="isar">
theory Conmutatividad_de_la_interseccion
imports Main
begin

(* 1ª demostración *)
lemma "s ∩ t = t ∩ s"
proof (rule set_eqI)
  fix x
  show "x ∈ s ∩ t ⟷ x ∈ t ∩ s"
  proof (rule iffI)
    assume h : "x ∈ s ∩ t"
    then have xs : "x ∈ s"
      by (simp only: IntD1)
    have xt : "x ∈ t"
      using h by (simp only: IntD2)
    then show "x ∈ t ∩ s"
      using xs by (rule IntI)
  next
    assume h : "x ∈ t ∩ s"
    then have xt : "x ∈ t"
      by (simp only: IntD1)
    have xs : "x ∈ s"
      using h by (simp only: IntD2)
    then show "x ∈ s ∩ t"
      using xt by (rule IntI)
  qed
qed

(* 2ª demostración *)
lemma "s ∩ t = t ∩ s"
proof (rule set_eqI)
  fix x
  show "x ∈ s ∩ t ⟷ x ∈ t ∩ s"
  proof
    assume h : "x ∈ s ∩ t"
    then have xs : "x ∈ s"
      by simp
    have xt : "x ∈ t"
      using h by simp
    then show "x ∈ t ∩ s"
      using xs by simp
  next
    assume h : "x ∈ t ∩ s"
    then have xt : "x ∈ t"
      by simp
    have xs : "x ∈ s"
      using h by simp
    then show "x ∈ s ∩ t"
      using xt by simp
  qed
qed

(* 3ª demostración *)
lemma "s ∩ t = t ∩ s"
proof (rule equalityI)
  show "s ∩ t ⊆ t ∩ s"
  proof (rule subsetI)
    fix x
    assume h : "x ∈ s ∩ t"
    then have xs : "x ∈ s"
      by (simp only: IntD1)
    have xt : "x ∈ t"
      using h by (simp only: IntD2)
    then show "x ∈ t ∩ s"
      using xs by (rule IntI)
  qed
next
  show "t ∩ s ⊆ s ∩ t"
  proof (rule subsetI)
    fix x
    assume h : "x ∈ t ∩ s"
    then have xt : "x ∈ t"
      by (simp only: IntD1)
    have xs : "x ∈ s"
      using h by (simp only: IntD2)
    then show "x ∈ s ∩ t"
      using xt by (rule IntI)
  qed
qed

(* 4ª demostración *)
lemma "s ∩ t = t ∩ s"
proof
  show "s ∩ t ⊆ t ∩ s"
  proof
    fix x
    assume h : "x ∈ s ∩ t"
    then have xs : "x ∈ s"
      by simp
    have xt : "x ∈ t"
      using h by simp
    then show "x ∈ t ∩ s"
      using xs by simp
  qed
next
  show "t ∩ s ⊆ s ∩ t"
  proof
    fix x
    assume h : "x ∈ t ∩ s"
    then have xt : "x ∈ t"
      by simp
    have xs : "x ∈ s"
      using h by simp
    then show "x ∈ s ∩ t"
      using xt by simp
  qed
qed

(* 5ª demostración *)
lemma "s ∩ t = t ∩ s"
proof
  show "s ∩ t ⊆ t ∩ s"
  proof
    fix x
    assume "x ∈ s ∩ t"
    then show "x ∈ t ∩ s"
      by simp
  qed
next
  show "t ∩ s ⊆ s ∩ t"
  proof
    fix x
    assume "x ∈ t ∩ s"
    then show "x ∈ s ∩ t"
      by simp
  qed
qed

(* 6ª demostración *)
lemma "s ∩ t = t ∩ s"
by (fact Int_commute)

(* 7ª demostración *)
lemma "s ∩ t = t ∩ s"
by (fact inf_commute)

(* 8ª demostración *)
lemma "s ∩ t = t ∩ s"
by auto

end
</pre>
