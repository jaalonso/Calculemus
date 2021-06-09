(* Monotonia_de_la_imagen_inversa.thy
   Monotonía de la imagen inversa
   José A. Alonso Jiménez
   Sevilla, 13 de junio de 2021
   ---------------------------------------------------------------------
*)

text \<open>------------------------------------------------------------------
   Demostrar que si u \<subseteq> v, entonces
      f -` u \<subseteq> f -` v
  ---------------------------------------------------------------------\<close>

theory Monotonia_de_la_imagen_inversa
imports Main
begin

section \<open>1\<ordfeminine> demostración\<close>

lemma
  assumes "u \<subseteq> v"
  shows "f -` u \<subseteq> f -` v"
proof (rule subsetI)
  fix x
  assume "x \<in> f -` u"
  then have "f x \<in> u"
    by (rule vimageD)
  then have "f x \<in> v"
    using \<open>u \<subseteq> v\<close> by (rule set_rev_mp)
  then show "x \<in> f -` v" 
    by (simp only: vimage_eq)
qed

section \<open>2\<ordfeminine> demostración\<close>

lemma
  assumes "u \<subseteq> v"
  shows "f -` u \<subseteq> f -` v"
proof
  fix x
  assume "x \<in> f -` u"
  then have "f x \<in> u"
    by simp
  then have "f x \<in> v"
    using \<open>u \<subseteq> v\<close> by (rule set_rev_mp)
  then show "x \<in> f -` v" 
    by simp
qed

section \<open>3\<ordfeminine> demostración\<close>

lemma
  assumes "u \<subseteq> v"
  shows "f -` u \<subseteq> f -` v"
  using assms
  by (simp only: vimage_mono)

section \<open>4\<ordfeminine> demostración\<close>

lemma
  assumes "u \<subseteq> v"
  shows "f -` u \<subseteq> f -` v"
  using assms
  by blast

end


