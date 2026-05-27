#import "@local/doc_fac:0.1.0": *
#import "@local/utils:0.1.0": *

#show: doc_fac.with(title: "Notes de TD - 26/05/2026")

= TD 4

== Exo 13

Pour les termes rectangulaires $x_i x_j$, on voudra éliminer les deux variables dans une expression de la forme :
$
  x_i x_j + x_i cdot alpha + x_j cdot beta
$
avec $alpha,beta$ des formes linéaires

Dans ce cas, on écrit :
$
x_i x_j + x_i cdot alpha x_j cdot beta = (x_i + beta)(x_j + alpha) - alpha beta
$

Puis on utilise l'identité remarquable $(B) : a b = 1/4 (a+b)^2 - 1/4 (a-b)^2$

Pour la question 5, on utilise la base $q$-orthogonale pour faire une combinaison linéaire de vecteurs qui font 0 et ne sont pas dans $Ker q$

_Note pour le CC de la part du prof : regarder les derniers exos qui aborderaient peut-être des notions pas vues en TD_