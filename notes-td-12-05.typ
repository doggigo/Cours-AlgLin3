#import "@local/doc_fac:0.1.0": *
#import "@local/utils:0.1.0": *

#show: doc_fac.with(title: "Notes de TD - 12/05/2026")

= TD 3
== Exo 15
+ C'est la définition d'un endomorphisme symetrique défini positif.
+ La matrice $M$ est symétrique donc diagonalisable en BON. On cherche à diagonaliser de sorte qu'il existe $P in GL_2 (RR)$ et $D = diag(d_1,d_2,d_3)$

  Si les $d_i >= 0$, alors une racine carrée de $M$ est donnée par $P diag(sqrt(d_1),sqrt(d_2),sqrt(d_3)) P^(-1)$

  (Le context idéal est $M$ symétrique positive car le théoreme spectral donne une strategie)

  #underline[*Dans les grandes lignes :*]
  + Calcul du polynôme caractéristique
    $
    P_M (X) = ... = X^2 - 6X + 1
    $

  + Racines de $P_M$ : $P_M = (X - (3-2sqrt(2)))(X-(3+2sqrt(2)))$
  + Vecteurs et espace propres
  On calcule $E_(3 - 2sqrt(2))$ et $E_(3 + 2sqrt(2))$

  Finalement $D = mat(3-2sqrt(2),0;0,3+2sqrt(2)) = mat(sqrt(3-2sqrt(2)),0;0,sqrt(3+2sqrt(2)))^2$
  
  D'où $sqrt(M) = P sqrt(D) P^(-1)$

+ Remarque : Si $f = o s$, alors $f^* f = (o s)^* o s = s^* o^* o s = s^2$

  Cherchons une racine carrée de $f^* f$ :

  $
  transp(A)A = ... = mat(10,0,0;0,36,0;0,0,10) = mat(sqrt(10), 0, 0;0,6,0;0,0,sqrt(10))^2
  $
  
  Puis $O = A S^(-1)$

+ $(m) = (sgn(m))(|m|)$, on peut aussi l'interprêter dans $CC$ : $m = rho e^(i theta)$


= TD 4

== Exo 2
$
M = mat(1,2,3;4,5,6;7,8,9) = Mat_(e) (B) = (B(e_i,e_j))_(1<=i,j<=3)
$

On cherche $M^' = Mat_(e^') (B) = (B(e_i^',e_j^'))_(1<=i,j<=3)$

*2 méthodes :*

- On peut ecrire, par ex : $B(e_1^',e_1^') = B(e_1 - e_2, e_1 - e_3) = B(e_1,e_1) - B(e_1,e_2) - B(e_2,e_1) + B(e_2,e_2)$ = 1 - 2 - 4 + 5 = 0, et ainsi de suite pour les autres éléments de la matrice.

- D'après le cours, avec la matrice de passage de $(e)$ à $(e^')$, on a : $M^' = transp(P)M P$

== Exo 4

+ Rappel : $Vect(e_1,e_2)^(perp_b) = {e_1,e_2}^(perp_b) = e_1^(perp_b) inter e_2^(perp_b)$ ou $e_1^(perp_b) = {x in E | b(e_i,x) = 0}$
+ On a :
  
  $F^(perp_b) = Vect((1,0,0),(1,0,1))^(perp_b) = (1,0,0)^(perp_b) inter (1,0,1)^(perp_b)$ 
  
  avec $(1,0,0)^(perp_b) = {vec(x,y,z) in RR^3 | mat(1,0,0)mat(1,1,1;1,2,3;1,3,5) vec(x,y,z) = (0)} = {vec(x,y,z) in RR^3 | mat(1,1,1)vec(x,y,z) = (0)} = {vec(x,y,z) in RR^3 | x + y + z = 0}$

*#underline[Rappel :]* Soient $b$ forme bilinéaire sur $E$, $x,y in E$. Soient $e(1,dots,e_n)$ base de $E$, $M = Mat_(e_i)(b), X = Mat_(e_i) (x), Y = Mat_(e_i)(y)$ Alors $(b(x,y) = transp(X)M Y)$

