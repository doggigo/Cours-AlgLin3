#import "@local/doc_fac:0.1.0": *
#import "@local/utils:0.1.0": *

#show: doc_fac.with(title: "Notes de TD - 05/05/2026")


= TD 3

_Exos 7,8,13,15_

== Exo 7

+ La matrice $A$ est symétrique donc diagonalisable en base orthonormée
+ Rappel : $P$ orthogonale si $transp(P) P = I_n$, soit $transp(P) = P^(-1)$, Ainsi, on aurait bien $transp(P)A P = P^(-1)A P$, et pour avoir $P^(-1)A P$ diagonale, on doit avoir les colonnes de $P$ qui sont des vecteurs propres de $A$. Or, les vecteurs propres d'une matrice symétrique sont orthogonaux, et on peut les orthonormaliser pour obtenir une base orthonormée de vecteurs propres. Ainsi, il existe une matrice orthogonale $P$ telle que $P^(-1)A P$ est diagonale.

  Si $P = mat(C_1, C_2, C_3)$ et $P^(-1)A P = mat(d_1,0,0;0,d_2,0;0,0,d_3)$, alors :
  $
    A P = P mat(d_1,0,0;0,d_2,0;0,0,d_3) "et donc" A C_1 = A P vec(1,0,0) = P mat(d_1,0,0;0,d_2,0;0,0,d_3) vec(1,0,0) = d_1 C_1
  $

  On a bien $C_1$ une vecteur propre de $A$, de même pour $C_2$ et $C_3$
  - Pour avoir $P$ inversible, on doit avoir $c_1,dots,c_n$ base de vecteurs propres pour $A$.
  - Pour avoir $P$ orthogonale, on doit avoir $c_1,dots,c_n$ base orthonormée de vecteurs propres pour $A$.

  Dans l'exo 7, on cherche donc à calculer une base orthonormée de vecteurs propres.

=== Calcul de cette base ?
+ Calcul du polynôme caractéristique et des valeurs propres, disons $lambda_1,lambda_2,lambda_3$ 
  
  _Ici : $3,3,-3$_
+ Calcul des espaces propres $E_(lambda_i) = Ker(A-lambda_i I_n)$ 
  
  _Ici : $E_(-3) = Vect((1,1,1)), E_3 = Vect((1,-1,0),(0,1,-1))$_
+ Choix d'une base de chaque $E_(lambda_i)(A)$ et orthonormalisation de cette base.

_Rappel : $E = E_(lambda_1) operp2 E_(lambda_2) operp2 E_(lambda_3)$ car $A$ est symétrique, donc on peut orthonormaliser dans chaque $E_(lambda_i)$ plutôt que dans $E$_


Remarque : L'endomorphisme naturellement associé à une matrice $A in M_n (KK)$ est $f_a : application(KK^n,KK^n,X, A X)$. Le produit scalaire sur $KK^n$ qui fait correspondre $f_p$ orthogonal à $P$ orthogonal (i.e. $transp(P)P = I_n$) est le produit scalaire canonique sur $KK^n$ : $scal2(vec(x_1,vdots,x_n),vec(y_1,vdots,y_n)) := sum_(i=1)^n x_i y_i$

== Exo 8

+ remarquer que $u(P)(X) = ((X^2 -1)(P^' (X)))^'$ puis faire une IPP.
+ Penser à un théorème du cours puis montrer que $u$ est symétrique pour le produit scalaire $phi$.
  
  Soient $A$ vecteur propre associé à $lambda$, $B$ associé à $mu$, montrer que $phi(A,B) = 0$ en partant de $phi(u(A),B)$
+ On peut utiliser qu'il existe une base orthonormale de vecteurs propres pour $phi$, on cherche donc des vecteurs propres directement.

  C'est-à-dire que l'on part de l'équation $u(P) = lambda P$ et que on cherche les solutions de cette équation avec $P = a X^3 + b X^2 + c X + d$.

== Exo 13

+ Par le théorème spectral, l'endomorphisme symétrique $u$ est diagonalisable en BON.

  Soit $(e_1,dots,e_n)$ une telle base, il faut calculer $scal2(u(e_1+ ... + e_n),e_1 + dots + e_n)$

+ Remarquer que si $BBB = (x,f_2,dots,f_n)$ base de $E$, alors 
  $
  (scal2(u(x),x)) = Mat_((1)) (scal2(u(x),x)) = transp(Mat_BBB (u))Mat_BBB (scal2(.,.)) Mat_BBB (x) = transp((Mat_BBB (u) Mat_BBB (x))) (scal2(.,.)) Mat_BBB (x) 
  $
  ssi $BBB$ BON, alors $Mat_BBB (scal2(.,.)) = I_n$ donc $(scal2(u(x),x)) = transp(vec(1,0,vdots,0))transp(Mat_BBB (u)) I_n vec(1,0,vdots,0) = Mat_BBB (u)$

  Puis faire une récurrence en utilisant la question 1.

  Rappel : Si $(e_1,dots,e_n)$ est une BON pour $scal2(.,.)$, alors $Tr(u) = sum_(i=1)^n scal2(u(e_i),e_i)$