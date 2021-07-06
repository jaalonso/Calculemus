---
Título: Límite de la suma de sucesiones convergentes
Autor:  José A. Alonso
---

En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante una función (u : ℕ → ℝ) de forma que u(n) es uₙ.

Se define que a es el límite de la sucesión u, por
<pre lang="text">
   def limite : (ℕ → ℝ) → ℝ → Prop :=
   λ u a, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
</pre>
donde se usa la notación |x| para el valor absoluto de x
<pre lang="text">
   notation `|`x`|` := abs x
</pre>

Demostrar que el límite de la suma de dos sucesiones convergentes es la suma de los límites de dichas sucesiones.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables (u v : ℕ → ℝ)
variables (a b : ℝ)

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variables (u v : ℕ → ℝ)
variables (a b : ℝ)

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε hε,
  have hε2 : 0 < ε / 2,
    { linarith },
  cases hu (ε / 2) hε2 with Nu hNu,
  cases hv (ε / 2) hε2 with Nv hNv,
  clear hu hv hε2 hε,
  use max Nu Nv,
  intros n hn,
  have hn₁ : n ≥ Nu,
    { exact le_of_max_le_left hn },
  specialize hNu n hn₁,
  have hn₂ : n ≥ Nv,
    { exact le_of_max_le_right hn },
  specialize hNv n hn₂,
  clear hn hn₁ hn₂ Nu Nv,
  calc |(u + v) n - (a + b)|
       = |(u n + v n) - (a + b)|  : by refl
   ... = |(u n - a) + (v n -  b)| : by {congr, ring}
   ... ≤ |u n - a| + |v n -  b|   : by apply abs_add
   ... < ε / 2 + ε / 2            : by linarith
   ... = ε                        : by apply add_halves,
end

-- 2ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε hε,
  cases hu (ε/2) (by linarith) with Nu hNu,
  cases hv (ε/2) (by linarith) with Nv hNv,
  use max Nu Nv,
  intros n hn,
  have hn₁ : n ≥ Nu := le_of_max_le_left hn,
  specialize hNu n hn₁,
  have hn₂ : n ≥ Nv := le_of_max_le_right hn,
  specialize hNv n hn₂,
  calc |(u + v) n - (a + b)|
       = |(u n + v n) - (a + b)|  : by refl
   ... = |(u n - a) + (v n -  b)| : by {congr, ring}
   ... ≤ |u n - a| + |v n -  b|   : by apply abs_add
   ... < ε / 2 + ε / 2            : by linarith
   ... = ε                        : by apply add_halves,
end

-- 3ª demostración
-- ===============

lemma max_ge_iff
  {α : Type*}
  [linear_order α]
  {p q r : α}
  : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε hε,
  cases hu (ε/2) (by linarith) with Nu hNu,
  cases hv (ε/2) (by linarith) with Nv hNv,
  use max Nu Nv,
  intros n hn,
  cases max_ge_iff.mp hn with hn₁ hn₂,
  have cota₁ : |u n - a| < ε/2 := hNu n hn₁,
  have cota₂ : |v n - b| < ε/2 := hNv n hn₂,
  calc |(u + v) n - (a + b)|
       = |u n + v n - (a + b)|   : by rfl
   ... = |(u n - a) + (v n - b)| : by { congr, ring }
   ... ≤ |u n - a| + |v n - b|   : by apply abs_add
   ... < ε                       : by linarith,
end

-- 4ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε hε,
  cases hu (ε/2) (by linarith) with Nu hNu,
  cases hv (ε/2) (by linarith) with Nv hNv,
  use max Nu Nv,
  intros n hn,
  cases max_ge_iff.mp hn with hn₁ hn₂,
  calc |(u + v) n - (a + b)|
       = |u n + v n - (a + b)|   : by refl
   ... = |(u n - a) + (v n - b)| : by { congr, ring }
   ... ≤ |u n - a| + |v n - b|   : by apply abs_add
   ... < ε/2 + ε/2               : add_lt_add (hNu n hn₁) (hNv n hn₂)
   ... = ε                       : by simp
end

-- 5ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε hε,
  cases hu (ε/2) (by linarith) with Nu hNu,
  cases hv (ε/2) (by linarith) with Nv hNv,
  use max Nu Nv,
  intros n hn,
  rw max_ge_iff at hn,
  calc |(u + v) n - (a + b)|
       = |u n + v n - (a + b)|   : by refl
   ... = |(u n - a) + (v n - b)| : by { congr, ring }
   ... ≤ |u n - a| + |v n - b|   : by apply abs_add
   ... < ε                       : by linarith [hNu n (by linarith), hNv n (by linarith)],
end

-- 6ª demostración
-- ===============

example
  (hu : limite u a)
  (hv : limite v b)
  : limite (u + v) (a + b) :=
begin
  intros ε Hε,
  cases hu (ε/2) (by linarith) with L HL,
  cases hv (ε/2) (by linarith) with M HM,
  set N := max L M with hN,
  use N,
  have HLN : N ≥ L := le_max_left _ _,
  have HMN : N ≥ M := le_max_right _ _,
  intros n Hn,
  have H3 : |u n - a| < ε/2 := HL n (by linarith),
  have H4 : |v n - b| < ε/2 := HM n (by linarith),
  calc |(u + v) n - (a + b)|
       = |(u n + v n) - (a + b)|   : by refl
   ... = |(u n - a) + (v n - b)|   : by { congr, ring }
   ... ≤ |(u n - a)| + |(v n - b)| : by apply abs_add
   ... < ε/2 + ε/2                 : by linarith
   ... = ε                         : by ring
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Limite_de_la_suma_de_sucesiones_convergentes.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Limite_de_la_suma_de_sucesiones_convergentes
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

(* 1ª demostración *)

lemma
  assumes "limite u a"
          "limite v b"
  shows   "limite (λ n. u n + v n) (a + b)"
proof (unfold limite_def)
  show "∀ε>0. ∃k. ∀n≥k. ¦(u n + v n) - (a + b)¦ < ε"
  proof (intro allI impI)
    fix ε :: real
    assume "0 < ε"
    then have "0 < ε/2"
      by simp
    then have "∃k. ∀n≥k. ¦u n - a¦ < ε/2"
      using assms(1) limite_def by blast
    then obtain Nu where hNu : "∀n≥Nu. ¦u n - a¦ < ε/2"
      by (rule exE)
    then have "∃k. ∀n≥k. ¦v n - b¦ < ε/2"
      using ‹0 < ε/2› assms(2) limite_def by blast
    then obtain Nv where hNv : "∀n≥Nv. ¦v n - b¦ < ε/2"
      by (rule exE)
    have "∀n≥max Nu Nv. ¦(u n + v n) - (a + b)¦ < ε"
    proof (intro allI impI)
      fix n :: nat
      assume "n ≥ max Nu Nv"
      have "¦(u n + v n) - (a + b)¦ = ¦(u n - a) + (v n - b)¦"
        by simp
      also have "… ≤ ¦u n - a¦ + ¦v n - b¦"
        by simp
      also have "… < ε/2 + ε/2"
        using hNu hNv ‹max Nu Nv ≤ n› by fastforce
      finally show "¦(u n + v n) - (a + b)¦ < ε"
        by simp
    qed
    then show "∃k. ∀n≥k. ¦u n + v n - (a + b)¦ < ε "
      by (rule exI)
  qed
qed

(* 2ª demostración *)

lemma
  assumes "limite u a"
          "limite v b"
  shows   "limite (λ n. u n + v n) (a + b)"
proof (unfold limite_def)
  show "∀ε>0. ∃k. ∀n≥k. ¦(u n + v n) - (a + b)¦ < ε"
  proof (intro allI impI)
    fix ε :: real
    assume "0 < ε"
    then have "0 < ε/2" by simp
    obtain Nu where hNu : "∀n≥Nu. ¦u n - a¦ < ε/2"
      using ‹0 < ε/2› assms(1) limite_def by blast
    obtain Nv where hNv : "∀n≥Nv. ¦v n - b¦ < ε/2"
      using ‹0 < ε/2› assms(2) limite_def by blast
    have "∀n≥max Nu Nv. ¦(u n + v n) - (a + b)¦ < ε"
      using hNu hNv
      by (smt (verit, ccfv_threshold) field_sum_of_halves max.boundedE)
    then show "∃k. ∀n≥k. ¦u n + v n - (a + b)¦ < ε "
      by blast
  qed
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
