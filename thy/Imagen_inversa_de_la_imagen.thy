(* Imagen_inversa_de_la_imagen.thy
   Imagen inversa de la imagen
   José A. Alonso Jiménez
   Sevilla, 7 de junio de 2021
   ---------------------------------------------------------------------
*)

text \<open>------------------------------------------------------------------
   Demostrar que si s es un subconjunto del dominio de la función f,
   entonces s está contenido en la [imagen inversa](https://bit.ly/3ckseBL)
   de la [imagen de s por f](https://bit.ly/3x2Jxij); es decir,
      s \<subseteq> f⁻¹[f[s]]
  ---------------------------------------------------------------------\<close>

theory Imagen_inversa_de_la_imagen
imports Main
begin

section \<open>1\<ordfeminine> demostración\<close>

lemma "s \<subseteq> f -` (f ` s)"
proof (rule subsetI)
  fix x
  assume "x \<in> s"
  then have "f x \<in> f ` s" 
    by (simp only: imageI)
  then show "x \<in> f -` (f ` s)"  
    by (simp only: vimageI)
qed

section \<open>2\<ordfeminine> demostración\<close>

lemma "s \<subseteq> f -` (f ` s)"
proof
  fix x
  assume "x \<in> s"
  then have "f x \<in> f ` s" by simp
  then show "x \<in> f -` (f ` s)" by simp
qed

section \<open>3\<ordfeminine> demostración\<close>

lemma "s \<subseteq> f -` (f ` s)"
  by auto

end
