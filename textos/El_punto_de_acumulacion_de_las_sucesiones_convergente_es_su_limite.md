---
Título: El punto de acumulación de las sucesiones convergente es su límite
Autor:  José A. Alonso
---

Para extraer una subsucesión se aplica una función de extracción que conserva el orden; por ejemplo, la subsucesión
<pre lang="text">
   uₒ, u₂, u₄, u₆, ...
</pre>
se ha obtenido con la función de extracción φ tal que φ(n) = 2*n.

En Lean, se puede definir que φ es una función de extracción por
<pre lang="text">
   def extraccion (φ : ℕ → ℕ) :=
     ∀ n m, n < m → φ n < φ m
</pre>
que a es un límite de u por
<pre lang="text">
   def limite (u : ℕ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε
</pre>
que u es convergente por
<pre lang="text">
   def convergente (u : ℕ → ℝ) :=
     ∃ a, limite u a
</pre>
que a es un punto de acumulación de u por
<pre lang="text">
   def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
     ∃ φ, extraccion φ ∧ limite (u ∘ φ) a
</pre>

Demostrar que si u es una sucesión convergente y a es un punto de acumulación de u, entonces a es un límite de u.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
open nat

variable  {u : ℕ → ℝ}
variables {a : ℝ}

def extraccion (φ : ℕ → ℕ) :=
  ∀ n m, n < m → φ n < φ m

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

def convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
open nat

variable  {u : ℕ → ℝ}
variables {a : ℝ}

def extraccion (φ : ℕ → ℕ) :=
  ∀ n m, n < m → φ n < φ m

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

def convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

-- Lemas auxiliares
-- ================

lemma unicidad_limite_aux
  {a b: ℝ}
  (ha : limite u a)
  (hb : limite u b)
  : b ≤ a :=
begin
  by_contra h,
  set ε := b - a with hε,
  cases ha (ε/2) (by linarith) with A hA,
  cases hb (ε/2) (by linarith) with B hB,
  set N := max A B with hN,
  have hAN : A ≤ N := le_max_left A B,
  have hBN : B ≤ N := le_max_right A B,
  specialize hA N hAN,
  specialize hB N hBN,
  rw abs_lt at hA hB,
  linarith,
end

lemma unicidad_limite
  {a b: ℝ}
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
le_antisymm (unicidad_limite_aux hb ha)
            (unicidad_limite_aux ha hb)

lemma limite_subsucesion_aux
  {φ : ℕ → ℕ}
  (h : extraccion φ)
  : ∀ n, n ≤ φ n :=
begin
  intro n,
  induction n with m HI,
  { exact nat.zero_le (φ 0), },
  { apply nat.succ_le_of_lt,
    calc m ≤ φ m        : HI
       ... < φ (succ m) : h m (m+1) (lt_add_one m), },
end

lemma limite_subsucesion
  {φ : ℕ → ℕ}
  {a : ℝ}
  (h : limite u a)
  (hφ : extraccion φ)
  : limite (u ∘ φ) a :=
begin
  intros ε hε,
  cases h ε hε with N hN,
  use N,
  intros k hk,
  calc |(u ∘ φ) k - a|
       = |u (φ k) - a| : rfl
   ... < ε             : hN (φ k) _,
  calc φ k
       ≥ k : limite_subsucesion_aux hφ k
   ... ≥ N : hk,
end

-- 1ª demostración
example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
begin
  unfold convergente at hu,
  cases hu with b hb,
  convert hb,
  unfold punto_acumulacion at ha,
  rcases ha with ⟨φ, hφ₁, hφ₂⟩,
  have hφ₃ : limite (u ∘ φ) b,
    from limite_subsucesion hb hφ₁,
  exact unicidad_limite hφ₂ hφ₃,
end

-- 1ª demostración
example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
begin
  cases hu with b hb,
  convert hb,
  rcases ha with ⟨φ, hφ₁, hφ₂⟩,
  apply unicidad_limite hφ₂ _,
  exact limite_subsucesion hb hφ₁,
end

-- 2ª demostración
example
  (hu : convergente u)
  (ha : punto_acumulacion u a)
  : limite u a :=
begin
  cases hu with b hb,
  convert hb,
  rcases ha with ⟨φ, hφ₁, hφ₂⟩,
  exact unicidad_limite hφ₂ (limite_subsucesion hb hφ₁),
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/El_punto_de_acumulacion_de_las_sucesiones_convergente_es_su_limite.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory El_punto_de_acumulacion_de_las_sucesiones_convergente_es_su_limite
imports Main HOL.Real
begin

definition extraccion :: "(nat ⇒ nat) ⇒ bool" where
  "extraccion φ ⟷ (∀ n m. n < m ⟶ φ n < φ m)"

definition subsucesion :: "(nat ⇒ real) ⇒ (nat ⇒ real) ⇒ bool"
  where "subsucesion v u ⟷ (∃ φ. extraccion φ ∧ v = u ∘ φ)"

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "limite u c ⟷ (∀ε>0. ∃k. ∀n≥k. ¦u n - c¦ < ε)"

definition convergente :: "(nat ⇒ real) ⇒ bool" where
  "convergente u ⟷ (∃ a. limite u a)"

definition punto_acumulacion :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "punto_acumulacion u a ⟷ (∃φ. extraccion φ ∧ limite (u ∘ φ) a)"

(* Lemas auxiliares *)

lemma unicidad_limite_aux :
  assumes "limite u a"
          "limite u b"
  shows   "b ≤ a"
proof (rule ccontr)
  assume "¬ b ≤ a"
  let ?ε = "b - a"
  have "0 < ?ε/2"
    using ‹¬ b ≤ a› by auto
  obtain A where hA : "∀n≥A. ¦u n - a¦ < ?ε/2"
    using assms(1) limite_def ‹0 < ?ε/2› by blast
  obtain B where hB : "∀n≥B. ¦u n - b¦ < ?ε/2"
    using assms(2) limite_def ‹0 < ?ε/2› by blast
  let ?C = "max A B"
  have hCa : "∀n≥?C. ¦u n - a¦ < ?ε/2"
    using hA by simp
  have hCb : "∀n≥?C. ¦u n - b¦ < ?ε/2"
    using hB by simp
  have "∀n≥?C. ¦a - b¦ < ?ε"
  proof (intro allI impI)
    fix n assume "n ≥ ?C"
    have "¦a - b¦ = ¦(a - u n) + (u n - b)¦" by simp
    also have "… ≤ ¦u n - a¦ + ¦u n - b¦" by simp
    finally show "¦a - b¦ < b - a"
      using hCa hCb ‹n ≥ ?C› by fastforce
  qed
  then show False by fastforce
qed

lemma unicidad_limite :
  assumes "limite u a"
          "limite u b"
  shows   "a = b"
proof (rule antisym)
  show "a ≤ b" using assms(2) assms(1)
    by (rule unicidad_limite_aux)
next
  show "b ≤ a" using assms(1) assms(2)
    by (rule unicidad_limite_aux)
qed

lemma limite_subsucesion_aux :
  assumes "extraccion φ"
  shows   "n ≤ φ n"
proof (induct n)
  show "0 ≤ φ 0" by simp
next
  fix n assume HI : "n ≤ φ n"
  then show "Suc n ≤ φ (Suc n)"
    using assms extraccion_def
    by (metis Suc_leI lessI order_le_less_subst1)
qed

lemma limite_subsucesion :
  assumes "subsucesion v u"
          "limite u a"
  shows   "limite v a"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "ε > 0"
  then obtain N where hN : "∀k≥N. ¦u k - a¦ < ε"
    using assms(2) limite_def by auto
  obtain φ where hφ1 : "extraccion φ" and hφ2 : "v = u ∘ φ"
    using assms(1) subsucesion_def by auto
  have "∀k≥N. ¦v k - a¦ < ε"
  proof (intro allI impI)
    fix k
    assume "N ≤ k"
    also have "... ≤ φ k"
      by (simp add: limite_subsucesion_aux hφ1)
    finally have "N ≤ φ k" .
    have "¦v k - a¦ = ¦u (φ k) - a¦"
      using hφ2 by simp
    also have "… < ε"
      using hN ‹N ≤ φ k› by simp
    finally show "¦v k - a¦ < ε" .
  qed
  then show "∃N. ∀k≥N. ¦v k - a¦ < ε"
    by auto
qed

(* Demostración *)
lemma
  assumes "convergente u"
          "punto_acumulacion u a"
  shows   "limite u a"
proof -
  obtain b where hb : "limite u b"
    using assms(1) convergente_def by auto
  obtain φ where hφ1 : "extraccion φ" and
                 hφ2 : "limite (u ∘ φ) a"
    using assms(2) punto_acumulacion_def  by auto
  have "limite (u ∘ φ) b"
    using hφ1 hb limite_subsucesion subsucesion_def by blast
  with hφ2 have "a = b"
    by (rule unicidad_limite)
  then show "limite u a"
    using hb by simp
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
