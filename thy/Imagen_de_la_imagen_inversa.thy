(* Imagen_de_la_imagen_inversa.thy
   Imagen de la imagen inversa
   José A. Alonso Jiménez
   Sevilla, 10 de junio de 2021
   ---------------------------------------------------------------------
*)

text \<open>------------------------------------------------------------------
   Demostrar que
      f ` (f -` u) \<subseteq> u
  ---------------------------------------------------------------------\<close>

theory Imagen_de_la_imagen_inversa
imports Main
begin

section \<open>1\<ordfeminine> demostración\<close>

lemma "f ` (f -` u) \<subseteq> u"
proof (rule subsetI)
  fix y
  assume "y \<in> f ` (f -` u)"
  then show "y \<in> u" 
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x \<in> f -` u"
    then have "f x \<in> u" 
      by (rule vimageD)
    with \<open>y = f x\<close> show "y \<in> u" 
      by (rule ssubst)
  qed
qed
  
section \<open>2\<ordfeminine> demostración\<close>

lemma "f ` (f -` u) \<subseteq> u"
proof
  fix y
  assume "y \<in> f ` (f -` u)"
  then show "y \<in> u" 
  proof
    fix x
    assume "y = f x"
    assume "x \<in> f -` u"
    then have "f x \<in> u" 
      by simp
    with \<open>y = f x\<close> show "y \<in> u" 
      by simp
  qed
qed
  
section \<open>3\<ordfeminine> demostración\<close>

lemma "f ` (f -` u) \<subseteq> u"
  by (simp only: image_vimage_subset)

section \<open>4\<ordfeminine> demostración\<close>

lemma "f ` (f -` u) \<subseteq> u"
  by auto

end
