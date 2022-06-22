(* Si_gf_es_inyectiva_entonces_f_es_inyectiva.thy
-- Si g\<sqdot>f es inyectiva, entonces f es inyectiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 22-junio-2022
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si g\<sqdot>f es inyectiva, entonces f es inyectiva.
-- ------------------------------------------------------------------ *)

theory Si_gf_es_inyectiva_entonces_f_es_inyectiva
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma
  assumes "inj (g \<circ> f)"
  shows   "inj f"
proof (rule injI)
  fix x y
  assume "f  x = f y"
  then have "g (f x) = g (f y)"
    by (simp only: ext)
  then have "(g \<circ> f) x = (g \<circ> f) y"
    by (simp only: o_apply)
  then show "x = y"
    using assms(1) by (simp only: injD)
qed

(* \<ordfeminine> demostración *)

lemma
  assumes "inj (g \<circ> f)"
  shows   "inj f"
proof (rule injI)
  fix x y
  assume "f  x = f y"
  then have "g (f x) = g (f y)"
    by simp
  then have "(g \<circ> f) x = (g \<circ> f) y"
    by simp
  then show "x = y"
    using assms(1) by (simp add: injD)
qed

(* 3\<ordfeminine> demostración *)

lemma
  assumes "inj (g \<circ> f)"
  shows   "inj f"
using assms inj_on_imageI2 by auto
