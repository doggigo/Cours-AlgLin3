#import "@local/doc_fac:0.1.0": *
#import "@local/utils:0.1.0": *

#show: doc_fac.with(title: "Notes de TD - 21/04/2026")

= Notes sur le DM
- La notation en anglais est plutôt : $A^T$, tandis que celle en français est plutôt :$transp(A)$

- Si $(E,scal2)$, il est facile de choisir une base orthomormée en choisissant $e_1$ de norme $1$, puis $e_2 in e_1^perp$, $e_3 in Vect(e_1, e_2)^perp, ..., e_n in Vect(e_1, ..., e_(n-1))^perp$. L'algorithme de Gram-Schmidt permet d'obtenir une base de $E$ et l'orthonormalsier mais il faut avoir une base de départ.

= Notes sur le CC2
#set enum(numbering: "1.a)")
- "Entraînez-vous sur Gram-Schimdt !"
- *Barême :*
  - Exo 1
    + 2
    + 2
    + 4
  - Exo 2
    +
      + 1
      + 2
      + 2
    +
      + 2
      + 3
      + 3
  
#pagebreak()

= TD

== Exo 2
- On a $det(s_1 compose s_2 = det(s_1)det(s_2)) = (-1)(-1) = 1$
- $s_1,s_2 in O_3(RR)$ donc $s_1 compose s_2 in O_3(RR)$

Par la classification des éléments de $O_3 (RR)$, on a $s_1 compose s_2 = Id$ ou $s_1 compose s_2$ une rotation d'angle $equiv.not 0 mod(2 pi)$

- #underline[Caractéristiques d'une rotation]:
  - L'axe
  - L'angle

*Axe* :

Les vecteurs de $P_1,P_2$ sont respectivement fixes par $s_2,s_1$

Donc les vecteurs de $P_1 inter P_2$ sont fixes par $s_1 compose s_2$

$(x,y,z) in P_1 inter P_2 <==> cases(x+y+z = 0, z+2y-z = 0) <==> (x,y,z) in Vect(vec(3, -2, -1))$

*Angle* :

#underline[Remarque]: Dans $RR^2$, si $R(theta) = mat(cos(theta), -sin(theta); sin(theta), cos(theta))$, alors $R(theta)vec(1, 0) = vec(cos(theta), sin(theta))$ et donc $scal2(R(theta)vec(1, 0), vec(1, 0)) = cos(theta)$

- Si $u$ un autre vecteur unitaire de plan $RR^2$, alors il existe $tau in RR$ tel que $u = R(tau)vec(1, 0)$. Ainsi :
  $
    scal2(R(theta)u, u) = scal2(R(theta)R(tau)vec(1, 0), R(tau)vec(1, 0)) = scal2(R(tau)(R(theta)vec(1, 0)), R(tau)vec(1, 0)) =^(R(tau) in O_2 (RR)) scal2(R(theta)vec(1, 0), vec(1, 0)) = cos(theta)
  $

Finalement, on trouve l'angle non-orienté de $s_1 compose s_2$ en prenant un vecteur du plan de la rotation et en calculant :
$
  scal2((s_1 compose s_2)(u/norm(u)), u/norm(u)) = cos(theta)
$

Notons $P$ le plan de la rotation. On a :
$P = (P_1 inter P_2)^perp$
_$P_1 inter P_2$ étant l'axe de la rotation_

On remarque que $P_1 = {(x,y,z) in RR^3 | scal2((x,y,z), (1,1,1)) = 0} = {(1,1,1)}^perp$

Ainsi $(1,1,1)$ est orthogonal à tous les vecteurs de $P_1$ et donc à tous les vecteurs de $P_1 inter P_2$. De même, $(1,2,-1)$ est orthogonal à tous les vecteurs de $P_2$, donc à tous les vecteurs de $P_1 inter P_2$.

Finalement le plan (car les vecteurs sont non-colineaires) $(Vect((1,1,1), (1,2,-1)))$ est le plan de la rotation.

Choisissons $u = v_2$, de sorte que $s_2(v_2) = -v_2$ est facile à calculer

Ensuite :
$s_1(x) = x - 2 scal2(x, v_1)/norm(v_1)^2 v_1$

On en déduit $ (s_1 compose s_2)(v_2) &= s_1(-v_2) = -s_1 (v_2) = -(v_2 - 2 scal2(v_2, v_1)/norm(v_1)^2 v_1) = -((1,2,-1) - (2(1+2-1))/3 (1,1,1)) \
&= -(1/3,2/3,-7/3) = 1/3 (1,-2,7) $

On obtient :
$
cos(theta) = scal2((s_1 compose s_2)(v_2/norm(v_2)), v_2/norm(v_2)) = scal2(1/sqrt(6) 1/3 (1,-2,7), 1/sqrt(6) (1,2,-1)) = 1/18 (1-3-7) = -10/18 = -5/9
$

Pour connaître l'angle orienté, on doit fixer une base (une orientation) et calculer $sin(theta)$.

On peut choisir la base $(v_2, (s_1 compose s_2)(v_2), vec(3,-2,-1))$ 

(la base = base du plan de rotation $union$ vecteur directeur de l'axe de rotation)

#underline[Remarque :] $vec(1,0,0) and vec(cos(theta),sin(theta),0) = (0,0,sin(theta))$

Donc $v_2 and ((s_1 compose s_2)(v_2)) = sin(theta)vec(3,-2,-1)/norm((3,-2,-1))$

En fait, connaître le signe de $sin(theta)$ suffit car on sait que $theta = +- arccos(-5/9)$

$vec(1,2,-1) and 1/3 vec(1,-2,7)= 1/3 vec(12,-8,-4) = 4/3 vec(3,-2,-1)$

Le signe est positif, donc avec l'orientation choisie, on a $boxed(theta = arccos(-5/9))$

== Exo 4
$f$ est orthogonal ($f in O(E)$) si :
$
forall x,y in E, scal2(f(x),f(y)) = scal2(x,y)
$

(
  En particulier, si $x perp y$, alors $f(x) perp f(y)$, càd $scal2(x,y) = 0$

  Le nom est "orthogonal" car il préserve l'orthogonalité. Cependant, il préserve aussi la norme.

  Contre-exemple : $2 Id_E$ préserve l'orthogonalité mais pas les normes.
)

Remarque : $forall x in E, norm(f(x))^2 = norm(x)^2 => norm(f(x + y))^2 = norm(x + y)$

Donc $f$ préserve les normes $==> f$ préserve l'orthogonalité.

Ainsi, appelons un endomorphisme orthogonal une isométrie (vectorielle) !

=== Indications

+
+ On doit trouver $alpha = 0$ ou $alpha = -2/norm(u)^2$


=== Devoirs pour dans 2 semaines
- finir l'exo 4
- faire l'exo 7
  - Indications :
    - diagonalisation + orthogonalisation de la base de vecteurs propres.

