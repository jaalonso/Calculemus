(* Imagen_inversa_de_la_imagen_de_aplicaciones_inyectivas.thy
   Imagen inversa de la imagen de aplicaciones inyectivas
   José A. Alonso Jiménez
   Sevilla, 9 de junio de 2021
   ---------------------------------------------------------------------
*)

text \<open>------------------------------------------------------------------
   Demostrar que si f es inyectiva, entonces
      f⁻¹[f[s]] \<subseteq> s
  ---------------------------------------------------------------------\<close>

theory Imagen_inversa_de_la_imagen_de_aplicaciones_inyectivas
imports Main
begin

section \<open>?\<ordfeminine> demostración\<close>

lemma
  assumes "inj f"
  shows "f -` (f ` s) \<subseteq> s"
proof (rule subsetI)
  fix x
  assume "x \<in> f -` (f ` s)"
  then have "f x \<in> f ` s" 
    by (rule vimageD)
  then show "x \<in> s" 
  proof (rule imageE)
    fix y
    assume "f x = f y"
    assume "y \<in> s"
    have "x = y" 
      using \<open>inj f\<close> \<open>f x = f y\<close> by (rule injD)
    then show "x \<in> s"
      using \<open>y \<in> s\<close>  by (rule ssubst)
  qed
qed

section \<open>2\<ordfeminine> demostración\<close>

lemma
  assumes "inj f"
  shows "f -` (f ` s) \<subseteq> s"
proof
  fix x
  assume "x \<in> f -` (f ` s)"
  then have "f x \<in> f ` s" 
    by simp
  then show "x \<in> s" 
  proof
    fix y
    assume "f x = f y"
    assume "y \<in> s"
    have "x = y" 
      using \<open>inj f\<close> \<open>f x = f y\<close> by (rule injD)
    then show "x \<in> s"
      using \<open>y \<in> s\<close>  by simp
  qed
qed

section \<open>3\<ordfeminine> demostración\<close>

lemma
  assumes "inj f"
  shows "f -` (f ` s) \<subseteq> s"
  using assms
  unfolding inj_def
  by auto

section \<open>4\<ordfeminine> demostración\<close>

lemma
  assumes "inj f"
  shows "f -` (f ` s) \<subseteq> s"
  using assms
  by (simp only: inj_vimage_image_eq)

end
