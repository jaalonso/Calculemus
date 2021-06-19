---
Título: Teorema de Cantor
Autor:  José A. Alonso
---

Demostrar que el teorema de Cantor; es decir, que no existe ninhuna aplicación suprayectiva de un conjunto en su conjunto potencia.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open function

variables {α : Type}

example : ∀ f : α → set α, ¬ surjective f :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.set.basic
open function

variables {α : Type}

-- 1ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := {i | i ∉ f i},
  unfold surjective at surjf,
  cases surjf S with j fjS,
  by_cases j ∈ S,
  { apply absurd _ h,
    rw fjS,
    exact h, },
  { apply h,
    rw ← fjS at h,
    exact h, },
end

-- 2ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := {i | i ∉ f i},
  cases surjf S with j fjS,
  by_cases j ∈ S,
  { apply absurd _ h,
    rwa fjS, },
  { apply h,
    rwa ← fjS at h, },
end

-- 3ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := {i | i ∉ f i},
  cases surjf S with j fjS,
  have h : (j ∈ S) = (j ∉ S), from
    calc  (j ∈ S)
        = (j ∉ f j) : set.mem_set_of_eq
    ... = (j ∉ S)   : congr_arg not (congr_arg (has_mem.mem j) fjS),
  exact false_of_a_eq_not_a h,
end

-- 4ª demostración
-- ===============

example : ∀ f : α → set α, ¬ surjective f :=
cantor_surjective
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Teorema_de_Cantor.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Teorema_de_Cantor
imports Main
begin

(* 1ª demostración *)

theorem
  fixes f :: "'α ⇒ 'α set"
  shows "¬ surj f"
proof (rule notI)
  assume "surj f"
  let ?S = "{i. i ∉ f i}"
  have "∃ j. ?S = f j"
    using ‹surj f› by (simp only: surjD)
  then obtain j where "?S = f j"
    by (rule exE)
  show False
  proof (cases "j ∈ ?S")
    assume "j ∈ ?S"
    then have "j ∉ f j"
      by (rule CollectD)
    moreover
    have "j ∈ f j"
      using ‹?S = f j› ‹j ∈ ?S› by (rule subst)
    ultimately show False
      by (rule notE)
  next
    assume "j ∉ ?S"
    with ‹?S = f j› have "j ∉ f j"
      by (rule subst)
    then have "j ∈ ?S"
      by (rule CollectI)
    with ‹j ∉ ?S› show False
      by (rule notE)
  qed
qed

(* 2ª demostración *)

theorem
  fixes f :: "'α ⇒ 'α set"
  shows "¬ surj f"
proof (rule notI)
  assume "surj f"
  let ?S = "{i. i ∉ f i}"
  have "∃ j. ?S = f j"
    using ‹surj f› by (simp only: surjD)
  then obtain j where "?S = f j"
    by (rule exE)
  have "j ∉ ?S"
  proof (rule notI)
    assume "j ∈ ?S"
    then have "j ∉ f j"
      by (rule CollectD)
    with ‹?S = f j› have "j ∉ ?S"
      by (rule ssubst)
    then show False
      using ‹j ∈ ?S› by (rule notE)
  qed
  moreover
  have "j ∈ ?S"
  proof (rule CollectI)
    show "j ∉ f j"
    proof (rule notI)
      assume "j ∈ f j"
      with ‹?S = f j› have "j ∈ ?S"
        by (rule ssubst)
      then have "j ∉ f j"
        by (rule CollectD)
      then show False
        using ‹j ∈ f j› by (rule notE)
    qed
  qed
  ultimately show False
    by (rule notE)
qed

(* 3ª demostración *)

theorem
  fixes f :: "'α ⇒ 'α set"
  shows "¬ surj f"
proof
  assume "surj f"
  let ?S = "{i. i ∉ f i}"
  have "∃ j. ?S = f j" using ‹surj f› by (simp only: surjD)
  then obtain j where "?S = f j" by (rule exE)
  have "j ∉ ?S"
  proof
    assume "j ∈ ?S"
    then have "j ∉ f j" by simp
    with ‹?S = f j› have "j ∉ ?S" by simp
    then show False using ‹j ∈ ?S› by simp
  qed
  moreover
  have "j ∈ ?S"
  proof
    show "j ∉ f j"
    proof
      assume "j ∈ f j"
      with ‹?S = f j› have "j ∈ ?S" by simp
      then have "j ∉ f j" by simp
      then show False using ‹j ∈ f j› by simp
    qed
  qed
  ultimately show False by simp
qed

(* 4ª demostración *)

theorem
  fixes f :: "'α ⇒ 'α set"
  shows "¬ surj f"
proof (rule notI)
  assume "surj f"
  let ?S = "{i. i ∉ f i}"
  have "∃ j. ?S = f j"
    using ‹surj f› by (simp only: surjD)
  then obtain j where "?S = f j"
    by (rule exE)
  have "j ∈ ?S = (j ∉ f j)"
    by (rule mem_Collect_eq)
  also have "… = (j ∉ ?S)"
    by (simp only: ‹?S = f j›)
  finally show False
    by (simp only: simp_thms(10))
qed

(* 5ª demostración *)

theorem
  fixes f :: "'α ⇒ 'α set"
  shows "¬ surj f"
proof
  assume "surj f"
  let ?S = "{i. i ∉ f i}"
  have "∃ j. ?S = f j" using ‹surj f› by (simp only: surjD)
  then obtain j where "?S = f j" by (rule exE)
  have "j ∈ ?S = (j ∉ f j)" by simp
  also have "… = (j ∉ ?S)" using ‹?S = f j› by simp
  finally show False by simp
qed

(* 6ª demostración *)

theorem
  fixes f :: "'α ⇒ 'α set"
  shows "¬ surj f"
  unfolding surj_def
  by best

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
