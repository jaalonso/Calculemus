(* Imagen_de_imagen_inversa_de_aplicaciones_suprayectivas.thy
   Imagen de imagen inversa de aplicaciones suprayectivas
   José A. Alonso Jiménez
   Sevilla, 11 de junio de 2021
   ---------------------------------------------------------------------
*)

text \<open>------------------------------------------------------------------
   Demostrar que si f es suprayectiva, entonces
      u \<subseteq> f ` (f -` u)
  ---------------------------------------------------------------------\<close>

theory Imagen_de_imagen_inversa_de_aplicaciones_suprayectivas
imports Main
begin

section \<open>1\<ordfeminine> demostración\<close>

lemma 
  assumes "surj f"
  shows "u \<subseteq> f ` (f -` u)"
proof (rule subsetI)
  fix y
  assume "y \<in> u"
  have "\<exists>x. y = f x"
    using \<open>surj f\<close> by (rule surjD)
  then obtain x where "y = f x"
    by (rule exE)
  then have "f x \<in> u" 
    using \<open>y \<in> u\<close> by (rule subst)
  then have "x \<in> f -` u" 
    by (simp only: vimage_eq)
  then have "f x \<in> f ` (f -` u)" 
    by (rule imageI)
  with \<open>y = f x\<close> show "y \<in> f ` (f -` u)" 
    by (rule ssubst)
qed

section \<open>2\<ordfeminine> demostración\<close>

lemma 
  assumes "surj f"
  shows "u \<subseteq> f ` (f -` u)"
proof 
  fix y
  assume "y \<in> u"
  have "\<exists>x. y = f x"
    using \<open>surj f\<close> by (rule surjD)
  then obtain x where "y = f x"
    by (rule exE)
  then have "f x \<in> u" 
    using \<open>y \<in> u\<close> by simp
  then have "x \<in> f -` u" 
    by simp
  then have "f x \<in> f ` (f -` u)" 
    by simp
  with \<open>y = f x\<close> show "y \<in> f ` (f -` u)" 
    by simp
qed

section \<open>3\<ordfeminine> demostración\<close>

lemma 
  assumes "surj f"
  shows "u \<subseteq> f ` (f -` u)"
  using assms
  by (simp only: surj_image_vimage_eq)

section \<open>4\<ordfeminine> demostración\<close>

lemma 
  assumes "surj f"
  shows "u \<subseteq> f ` (f -` u)"
  using assms
  unfolding surj_def
  by auto

section \<open>5\<ordfeminine> demostración\<close>

lemma 
  assumes "surj f"
  shows "u \<subseteq> f ` (f -` u)"
  using assms
  by auto

end
