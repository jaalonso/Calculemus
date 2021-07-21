---
Título: Los supremos de las sucesiones crecientes son sus límites
Autor:  José A. Alonso
---

Demostrar que si M es un supremo de una sucesión creciente u, entonces el límite de u es M.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variable (u : ℕ → ℝ)
variable (M : ℝ)

notation `|`x`|` := abs x

-- (limite u c) expresa que el límite de u es c.
def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

-- (supremo u M) expresa que el supremo de u es M.
def supremo (u : ℕ → ℝ) (M : ℝ) :=
  (∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example
  (hu : monotone u)
  (hM : supremo u M)
  : limite u M :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variable (u : ℕ → ℝ)
variable (M : ℝ)

notation `|`x`|` := abs x

-- (limite u c) expresa que el límite de u es c.
def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

-- (supremo u M) expresa que el supremo de u es M.
def supremo (u : ℕ → ℝ) (M : ℝ) :=
  (∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

-- 1ª demostración
example
  (hu : monotone u)
  (hM : supremo u M)
  : limite u M :=
begin
  -- unfold limite,
  intros ε hε,
  -- unfold supremo at h,
  cases hM with hM₁ hM₂,
  cases hM₂ ε hε with n₀ hn₀,
  use n₀,
  intros n hn,
  rw abs_le,
  split,
  { -- unfold monotone at h',
    specialize hu hn,
    calc -ε
         = (M - ε) - M : by ring
     ... ≤ u n₀ - M    : sub_le_sub_right hn₀ M
     ... ≤ u n - M     : sub_le_sub_right hu M },
  { calc u n - M
         ≤ M - M       : sub_le_sub_right (hM₁ n) M
     ... = 0           : sub_self M
     ... ≤ ε           : le_of_lt hε, },
end

-- 2ª demostración
example
  (hu : monotone u)
  (hM : supremo u M)
  : limite u M :=
begin
  intros ε hε,
  cases hM with hM₁ hM₂,
  cases hM₂ ε hε with n₀ hn₀,
  use n₀,
  intros n hn,
  rw abs_le,
  split,
  { linarith [hu hn] },
  { linarith [hM₁ n] },
end

-- 3ª demostración
example
  (hu : monotone u)
  (hM : supremo u M)
  : limite u M :=
begin
  intros ε hε,
  cases hM with hM₁ hM₂,
  cases hM₂ ε hε with n₀ hn₀,
  use n₀,
  intros n hn,
  rw abs_le,
  split ; linarith [hu hn, hM₁ n],
end

-- 4ª demostración
example
  (hu : monotone u)
  (hM : supremo u M)
  : limite u M :=
assume ε,
assume hε : ε > 0,
have hM₁ : ∀ (n : ℕ), u n ≤ M,
  from hM.left,
have hM₂ : ∀ (ε : ℝ), ε > 0 → (∃ (n₀ : ℕ), u n₀ ≥ M - ε),
  from hM.right,
exists.elim (hM₂ ε hε)
  ( assume n₀,
    assume hn₀ : u n₀ ≥ M - ε,
    have h1 : ∀ n, n ≥ n₀ → |u n - M| ≤ ε,
      { assume n,
        assume hn : n ≥ n₀,
        have h2 : -ε ≤ u n - M,
          { have h3 : u n₀ ≤ u n,
              from hu hn,
            calc -ε
                 = (M - ε) - M : by ring
             ... ≤ u n₀ - M    : sub_le_sub_right hn₀ M
             ... ≤ u n - M     : sub_le_sub_right h3 M },
        have h4 : u n - M ≤ ε,
          { calc u n - M
                 ≤ M - M       : sub_le_sub_right (hM₁ n) M
             ... = 0           : sub_self M
             ... ≤ ε           : le_of_lt hε },
        show |u n - M| ≤ ε,
          from abs_le.mpr (and.intro h2 h4) },
    show ∃ N, ∀ n, n ≥ N → |u n - M| ≤ ε,
      from exists.intro n₀ h1)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Los_supremos_de_las_sucesiones_crecientes_son_sus_limites.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Los_supremos_de_las_sucesiones_crecientes_son_sus_limites
imports Main HOL.Real
begin

(* (limite u c) expresa que el límite de u es c. *)
definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "limite u c ⟷ (∀ε>0. ∃k. ∀n≥k. ¦u n - c¦ ≤ ε)"

(* (supremo u M) expresa que el supremo de u es M. *)
definition supremo :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "supremo u M ⟷ ((∀n. u n ≤ M) ∧ (∀ε>0. ∃k. ∀n≥k. u n ≥ M - ε))"

(* 1ª demostración *)
lemma
  assumes "mono u"
          "supremo u M"
  shows   "limite u M"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  have hM : "((∀n. u n ≤ M) ∧ (∀ε>0. ∃k. ∀n≥k. u n ≥ M - ε))"
    using assms(2)
    by (simp add: supremo_def)
  then have "∀ε>0. ∃k. ∀n≥k. u n ≥ M - ε"
    by (rule conjunct2)
  then have "∃k. ∀n≥k. u n ≥ M - ε"
    by (simp only: ‹0 < ε›)
  then obtain n0 where "∀n≥n0. u n ≥ M - ε"
    by (rule exE)
  have "∀n≥n0. ¦u n - M¦ ≤ ε"
  proof (intro allI impI)
    fix n
    assume "n ≥ n0"
    show "¦u n - M¦ ≤ ε"
    proof (rule abs_leI)
      have "∀n. u n ≤ M"
        using hM by (rule conjunct1)
      then have "u n - M ≤ M - M"
        by simp
      also have "… = 0"
        by (simp only: diff_self)
      also have "… ≤ ε"
        using ‹0 < ε› by (simp only: less_imp_le)
      finally show "u n - M ≤ ε"
        by this
    next
      have "-ε = (M - ε) - M"
        by simp
      also have "… ≤ u n - M"
        using ‹∀n≥n0. M - ε ≤ u n› ‹n0 ≤ n› by auto
      finally have "-ε ≤ u n - M"
        by this
      then show "- (u n - M) ≤ ε"
        by simp
    qed
  qed
  then show "∃k. ∀n≥k. ¦u n - M¦ ≤ ε"
    by (rule exI)
qed

(* 2ª demostración *)
lemma
  assumes "mono u"
          "supremo u M"
  shows   "limite u M"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  have hM : "((∀n. u n ≤ M) ∧ (∀ε>0. ∃k. ∀n≥k. u n ≥ M - ε))"
    using assms(2)
    by (simp add: supremo_def)
  then have "∃k. ∀n≥k. u n ≥ M - ε"
    using ‹0 < ε› by presburger
  then obtain n0 where "∀n≥n0. u n ≥ M - ε"
    by (rule exE)
  then have "∀n≥n0. ¦u n - M¦ ≤ ε"
    using hM by auto
  then show "∃k. ∀n≥k. ¦u n - M¦ ≤ ε"
    by (rule exI)
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
