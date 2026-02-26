#import "@local/doc_cours_nb:0.1.0" : *

#show: doc_fac.with(title: "Test")

#theorem("Inégalité de Cauchy-Schwarz")[
  Soit $E$ un espace préhilbertien réel. Alors
  $forall x,y in E :$
  $
    abs(scal2(x, y)) <= norm(x)norm(y)
  $
  avec égalité ssi $(x,y)$ liée.
]

#corollary[
  Hey
]

= Dualité

$KK$ désigne un corps $(KK = RR "ou" CC)$, $E$ sera un $KK-$ev
== Dual

#definition[
  On appelle forme linéaire sur $E$ toute application linéaire de $E$ à valeur dans $KK$.

  On appelle *dual* de $E$, noté $E^*$ (ou $E^checkmark$) le $KK$-ev formé des formes linéaires sur $E$, $E = Lin(E, KK)$.
]
