(* La_composicion_de_crecientes_es_creciente.lean
-- La composición de crecientes es creciente
-- José A. Alonso Jiménez
-- Sevilla, 19 de julio de 2021
-- ------------------------------------------------------------------*)

(* ---------------------------------------------------------------------
-- Se dice que una función f de \<real> en \<real> es creciente https://bit.ly/2UShggL
-- si para todo x e y tales que x \<le> y se tiene que f(x) \<le> f(y).
--
-- En Isabelle/HOL que f sea creciente se representa por `mono f`.
--
-- Demostrar que la composición de dos funciones crecientes es una
-- función creciente.
-- ------------------------------------------------------------------ *)

theory La_composicion_de_crecientes_es_creciente
imports Main HOL.Real
begin

(* 1\<ordfeminine> demostración *)
lemma
  fixes f g :: "real \<Rightarrow> real"
  assumes "mono f"
          "mono g"
  shows   "mono (g \<circ> f)"
proof (rule monoI)
  fix x y :: real
  assume "x \<le> y"
  have "(g \<circ> f) x = g (f x)" 
    by (simp only: o_apply)
  also have "\<dots> \<le> g (f y)"
    using assms \<open>x \<le> y\<close>
    by (simp only: monoD)
  also have "\<dots> = (g \<circ> f) y"
    by (simp only: o_apply)
  finally show "(g \<circ> f) x \<le> (g \<circ> f) y" 
    by this
qed

(* 2\<ordfeminine> demostración *)
lemma
  fixes f g :: "real \<Rightarrow> real"
  assumes "mono f"
          "mono g"
  shows   "mono (g \<circ> f)"
proof (rule monoI)
  fix x y :: real
  assume "x \<le> y"
  have "(g \<circ> f) x = g (f x)"    by simp
  also have "\<dots> \<le> g (f y)"     by (simp add: \<open>x \<le> y\<close> assms monoD)
  also have "\<dots> = (g \<circ> f) y"    by simp
  finally show "(g \<circ> f) x \<le> (g \<circ> f) y" .
qed

(* 3\<ordfeminine> demostración *)
lemma
  assumes "mono f"
          "mono g"
  shows   "mono (g \<circ> f)"
  by (metis assms comp_def mono_def)

end
