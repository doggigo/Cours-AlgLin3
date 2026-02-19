#import "@local/doc_fac:0.1.0": *
#import "@local/utils:0.1.0": *

#let only-thms = false

#show: doc_fac.with(
  title: "Cours AlgLin3",
  numbering: "I. 1. 1. a) i)",
  show-examples: not only-thms,
  show-exercises: not only-thms,
  show-proofs: not only-thms,
)

#outline()

= Dualité

$KK$ désigne un corps $(KK = RR "ou" CC)$, $E$ sera un $KK-$ev
== Dual

#definition[
  On appelle forme linéaire sur $E$ toute applicatio linéaire de $E$ à valeur dans $KK$.

  On appelle *dual* de $E$, noté $E^*$ (ou $E^checkmark$) le $KK$-ev formé des formes linéaires sur $E$, $E = Lin(E, KK)$.
]

#example[
  + L'application nulle : $0 : application(E, KK, x, 0)$
  + $ application(RR^3, RR, (x,y,z), 3x-u+2z) $ est une fome linéaire sur $RR^3$
  + L'évaluation d'un polynôme en $a in KK$ :
    $ e v_a : application(KK[X], KK, P, P(a)) $ est une forme linéaire sur $KK[X]$
  + Pour $E = C^0([0,1],RR)$, $application(E, RR, f, integral_0^1 f(t) d t)$ est une forme linéaire dans $E$.
  + $E = {(u_n) in KK^NN | (u_n) --> l in KK}$, alors
  $application(E, KK, (u_n)_(n in NN), lim_(n -> + infinity) u_n)$ est une forme linéaire
]

#remark[
  Toute forme linéaire sur $RR^3$ est de la forme $a x + b y + c z$ avec $(a,b,c) in RR^3$

  Ainsi $(RR^3)^* = {f : (x,y,z) |-> a x + b y + c z | a,b,c in RR}$
]

#proof[
  Soit $(e_1,e_2,e_3)$ la b.c. de $RR^3$, et $(a,b,c) = (f(e_1),f(e_2),f(e_3))$ alors puisque $(x,y,z) = x e_1 + y e_2 + z e_3$, $f(x,y,z) = a x + b y + c z$
]

#property[
  Si $E$ est de dimension finie alors $E^*$ aussi et ils sont de même dimension.
]

#proof[
  $dim(Lin(E, KK) = dim E cdot dim KK = dim E)$
]

== Hyperplans

#definition[
  On appelle hyperplan de $E$ le noyau d'une forme linéaire non-nulle sur $E$. Si $phi in E^* without {0_(E^*)}$, on dira que $H = Ker(phi)$ est l'hyperplan d'équation $phi(x) = 0$
]

#example[
  + $H = {A in M_n (KK) | Tr(A) = 0}$ est un hyperplan de $MMM_n (KK)$. Tr est non-nulle : $Tr(I_n) = n$ par ex
  + $H = {(x,y,z) in RR^3 | 3 x - y + 2 z = 0}$ est un hyperplan.
  + $H = {P in KK[Z] | P(1) = 0}$ est un hyperplan car l'application n'est pas nulle.
]

#property[
  Soit $H$ un sous-espace vectoriel de $E$. Les assertions suivantes sont équivalentes :
  + $H$ est un hyperplan de $E$
  + Il existe une droite vectorielle $D$ telle que $E = D osum H$
  + Si $E$ est de dimension finie, $dim(H) = dim(E)-1$
]

#proof[
  - $underline(a => b)$ :  $H = ker(phi)$ avec $phi in E^* without {t |-> 0}$. Alors $exists u in E. phi(u) != 0$. Posons $D = K u = Vect(u)$ et montrons que $E = H osum D$.
    Si $x in H inter D$. Alors $x = lambda u, lambda in KK$ et $phi(x) = phi(lambda u) = lambda phi(u) = 0$. Donc $lambda = 0$ càd $x = 0$. Maintenant soit $x in E$, notons $alpha = phi(x)/phi(u) in KK$ et posons $h = x - alpha u$. Alors $phi(h) = phi(x) - alpha pi(u) = 0$ donc $h in H$ et $x = h + alpha u$. D'où la somme directe.
  - $underline(b => a)$ : Soit $D = K v = Vect(v), v != 0$ telle que $E = H osum D$.
    $forall x in E, x = underbrace(h_x, in H) + underbrace(lambda_x v, in D), quad lambda_x in KK$
    On pose $phi(x) = lambda x$. $phi : E -> KK$. Il reste à montrer que $phi$ est linéaire. $phi(x)$ est l'unique scalaire tel que $x - phi(x)v in H$.

    Soit $mu in KK$, $(mu x + y) - (mu phi(x) + phi(y))v = mu underbrace((x - phi(x) v), in H) + underbrace((y - phi(y) v), in H)$. Ainsi $(mu x + y) - (mu phi(x) + phi(y)) v in H$. D'où $phi(mu x + y) = mu phi(x) + phi(y)$ et $phi$ est linéaire.
]

== Base duale
Dans ce paragraphe, $E$ est de dimension finie.

Soit $EEE = (e_1, ..., e_n)$ une base d e $E$.

Pour $j in [|1,n|]$, on définit $e_j^* : E -> K$ la forme linéaire définie par $e_j^* (e_i) = delta_(i j)$

#proposition[
  La famille $EEE^* = (e_1^*, dots, e_n^*)$ est une base de $E^*$ appelée base duale de $EEE$.
]

#proof[
  Il suffit de montrer que $EEE^*$ est libre. Soit $(alpha_j)_(1 <= j <= n)$ une une famille de scalaires.

  Alors soit la somme : $sum_(j = 1)^n alpha_j e_j^* = 0$. Pour $i in [|1,n|]$, $(sum_(j = 1)^n alpha_j e_j^*)(e_i) = 0 = alpha_i$ d'où $EEE^*$ libre càd base.
]

#proposition("Changement de bases")[
  Soit $EEE,FFF$ deux bases de $E$, $P = P_EEE^FFF$, alors la matrice de passage de $EEE^*$ à $FFF^*$ est :
  $
    Q = transp(P^(-1))
  $
]

#proof[
  $EEE = (e_1, dots, e_n), FFF = (f_1, dots, f_n), P = [p_(i j)]_(1<=i,j<=n)$.

  $forall k in [|1,n|], f_k = sum_(l=1)^n p_(l k) e_l$.

  Notons $Q = [q_(i j)]_(1 <= i,j <= n) "et" f_j^* = sum_(i = 1)^n q_(i j) e^*_i$ pour tout $j in [|1,n|]$.

  $delta_(j k) = f_j^*(f_k) = sum_(i = 1^n) q_(i j) e_i^* (sum_(l = 1)^n p_(l k) e_l) = sum_(i = 1)^n sum_(l = 1)^n q_(i j) p_(l k) e_i^*(e_p) = sum_(i = 1)^n q_(i j) p_(i k)$.

  Ce terme correspond au coefficient de la $j$-ième ligne, $k$-ième colonne de la matrice $transp(Q)P$.

  Donc $transp(Q)P = I_n$ càd : $Q = transp(P^(-1))$
]

#corollary[
  Toute base de $E^*$ est une base duale. Autrement dit, si $EEE'$ est une base de $E^*$, il existe une base $EEE$ de $E$ telle que $EEE' = EEE^*$ la base duale de $EEE$.

  $EEE$ est appelée base préduale (ou antéduale) de $EEE'$
]

#proof[
  Soit $FFF$ une base de $E$, $FFF^*$ sa base duale. Notons $Q$ la matrice de passage de $FFF^*$ à $EEE'$ et $P = transp(Q^(-1))$. Appelons $EEE$ la base de $E$ telle que $P$ soit la matrice de passage de $FFF$ à $EEE$. La matrice de passage de $FFF^*$ à $EEE^*$ est $transp(P^(-1)) = Q$ (via la prop. précédente) donc $EEE' = EEE^*$
]

#corollary[
  Soit $E$ de dimension $n$.
  + Tout sev de $E$ de dimension $n-p$ avec $1 <= p <= n$ est l'intersection de $p$ hyperplans.
  + soit $(phi_1, dots, phi_p)$ une famille de $p$ formes linéaires non-nulles et $G = biginter_(i = 1)^n Ker(phi_i)$, alors $dim(G) = n - dim(Vect(phi_1, dots, phi_n))$.
]

#proof[
  + Soit $F$ un sev de $E$ de dimension $n - p$ de base $(e_i)_(1<= k <= n-p)$ complétée en $(e_i)_(1 <= k <= n)$ base de $E$. Alors $F = underbrace(biginter_(i = n - p + 1)^n Ker(e_i^*), p "hyperplans")$
  + Supposons d'abord que $(phi_i)_(1<= i <= p)$ est libre. On la complète en une base $(phi_1, dots, phi_p, dots, phi_m)$ de $E^*$ et on note $(e_i)_(1<=i<=n)$ la base antéduale de $(phi_i)$. Alors $G = biginter_(i = 1)^p Ker(phi_i) = biginter_(i = 1)^p Ker(e_i^*) = Vect(e_(p+1), dots, e_n)$ et $dim G = n-p$
  + Si $(phi_1, dots, phi_p)$ est liée, soit $Phi = Vect(phi_1, dots, phi_p), quad d = dim Phi$. Sans perdre de généralités (quitte à renumérotter), on peut supposer que $(phi_1, dots, phi_d)$ est une base de $Phi$.
  Pour $j in [|d+1,p|]$, $phi_j = sum_(i=1)^d lambda_i^j phi_i, quad lambda_i^j in K$.
  $ biginter_(i=1)^d Ker(phi_i) = biginter_(i=1)^p Ker(phi_i) $ et par ce qui précède, $dim(G) = n-d$.
]

== bidual

#definition[
  Pour un $KK$-ev, le dual de $E^*$ est noté $E^(**)$ et appelé bidual de $E$.
]
#proof("de la linéarité")[
  Considérons l'application :
  $Phi : application(E, E^(**), x, Phi(x) : application(E^*, K, phi, Phi(x)(phi)=phi(x)))$

  Montrons que $Phi$ est bien définie, il faut montrer que $Phi(x)$ est linéaire.

  $forall phi,psi in E^*, Phi(x)(lambda phi + psi) = (lambda phi + psi) = lambda phi(x) + psi(x) = lambda Phi(x)(phi) + Phi(x)(psi)$
]

#theorem[
  Si $E$ est #underline([de dimension finie]), $Phi$ est un isomorphisme.
]

#proof[
  + $Phi$ est linéaire : $forall x,y in E, forall lambda in KK, underbrace(Phi(lambda x + y), in E^(**))(phi) = phi(lambda x + y) = lambda phi(x) + phi(y) = lambda Phi(x)(phi) + Phi(y)(phi)$. Donc $Phi(lambda x + y) = lambda phi(x) + phi(y) = (lambda Phi(x) + Phi(y))(psi)$.

  + $Phi$ est bijective : comme $E^(**)$ de dimenion finie, il suffit de montrer que $Phi$ est injective. Soit $x in Ker(Phi)$. Phi(x) est l'application nulle. Donc pour tout $phi in E^*$, $Phi(x)(phi) = phi(x) = 0$ et donc $x = 0_E$. En effet, en notant $x = sum_(i = 1)^n x_i e_i$, $(e_i)$ base de $E$. Par contraposée, supposons $x != 0_E$, i.e. $exists x_(i_0) != 0$ avec $i_0 in [|1,n|]$. Et $x_(i_0) = e_(i_0)^* (x)$ donc $e_(i_0)^* (x) != 0$ et $e_(i_0)^* in E^*$. $Phi(x)(e_(i_0)^*) != 0$.
]

#remark[
  Si $E$ n'est pas de dimension finie, on peut montrer que $Phi$ reste injective, mais n'est plus surjective.
]

#remark("À l'oral")[
  Si $(phi_i)$ base de $(E^(*))$, $(phi_i^*)~> (Phi^(-1)(phi_n^*))$ est la base antéduale de $(phi_i)$
]


= Espaces Euclidiens
Dans ce chapitre, nous travaillerons uniquement sur des $RR$-ev.

== Produit scalaire
#definition("Forme bilinéaire")[
  Soit $E$ un $RR$-ev. On appelle forme bilinéaire sur $E$ une application $f : E^2 -> RR$ linéaire à chaque variable. C'est-à-dire,
  - $forall x, x', y, in E, forall lambda in RR, f(lambda x + x', y) = lambda f(x,y) + f(x',y)$
  - $forall x,y,y' in E, forall mu in RR, f(x,mu y + y') = mu f(x,y) + f(x,y')$
]

#remark[
  Notons $BBB(E)$ l'ensemble des formes bilinéaires sur $E$. $BBB(E)$ est un $RR$
]
-ev
#exercice[
  Le prouver
]

#remark[
  Se donner une forme bilinéaire sur $E$ équivaut à se donner une application linéaire de $E$ sur $E^*$.
]
#proof[
  Considérons
  $
    L : application(BBB(E), Lin(E, E^*), f, L(f) : application(E, E^*, y, L(f)(y) : application(E, RR, x, f(x,y))))
  $
  $L$ est bien définie.
  + $forall y in E, L(f)(y)$ est une forme linéaire :
    $forall x,x' in E, forall lambda in RR, L(f)(y)(lambda x+x') = f(lambda x + x',y) = lambda f(x,y) + f(x',y) = lambda L(f)(y)(x) + L(f)(y)(x')$
  + $L(f)$ est linéaire :

    $
      forall y,y' in E, forall lambda in RR, forall x in E : underbrace(L(f)(lambda y + y'), in E)(x)= f(x,lambda y + y') \
      = lambda f(x,y) + f(x,y') = lambda L(f)(y)(x) + L(f)(y')(x)
    $
]

#theorem[
  $
    L : application(BBB(E), Lin(E, E^*), f, L(f) : application(E, E^*, y, L(f)(y) : application(E, RR, x, f(x,y))))
  $
  Est un isomorphisme.
]
#proof[
  - $L$ est linéaire, $forall f,g in BBB(E), forall lambda in RR, forall x,y in E$ :
    $
      L(lambda f + g)(y)(x) = (lambda f + g)(x,y) = lambda f(x,y) + g(x,y) = lambda L(f)(y)(x) + L(g)(y)(x)
    $
  - $L$ est bijective. Considérons
    $
      psi : application(Lin(E, E^*), BBB(E), h, psi(h):application(E^2, RR, (x,y), psi(h)(x,y) = h(y)(x)))
    $
    $psi$ est l'application réciproque de $L$ :

    Montrons que $L compose psi = Id_(Lin(E, E^*))$ et $psi compose L = Id_(BBB(E))$

    (#underline("Remarque :") $psi(h)$ est bien une forme bilinéaire sur $E$)

    $
      forall h in LL(E, E^*), forall x,y in E, [L compose psi(h)](y) = L(psi(h))(y)(x) = psi(h)(x,y) = h(y)(x)
    $

    Ainsi : $[L compose psi](h) = h$

    Pour l'autre côté :
    $
      forall f in BBB(E), forall x,y in E
      [psi compose L](f)(x,y) = L(f)(y)(x) = f(x,y)
    $
    D'où $[psi compose L](f) = f$. $phi$ est bien inversible donc un isomorphisme.
]

#definition("Produit scalaire")[
  Une *forme bilinéaire* $f : application(E^2, RR, (x,y), f(x,y))$ est un produit scalaire sur $E$ si :
  - $f$ est *symétrique* : $forall x,y in E : f(x,y) = f(y,x)$
  - $f$ est *définie positive* : $forall x in E$, $f(x,x) >= 0$ et $f(x,x) = 0 <==> x = 0$
]

#notation[
  si $f$ est un produit scalaire sur $E$, on notera $f(x,y) = scal2(x, y)$
]

#definition("Espaces Euclidiens, Préhilbertiens")[
  Un $RR$-ev muni d'un produit scalaire est dit espace Préhilbertien réel. Si, de plus, il est de dimension finie, on dit que c'est un *espace Euclidien*
]

#example[
  + $RR^n$ muni du produit scalaire usuel
    $
      scal2(., .) : (vec(x_1, vdots, x_n),vec(y_1, vdots, y_n)) |-> sum_(i = 1)^n x_i y_i
    $
    est un espace Euclidien car
    c'est bien une forme bilinéaire symétrique définie positive

  + $C^0([0,1],RR)$ est un espace Préhilbertien réel pour le produit scalaire $ scal2(., .) : (f,g) |-> integral_0^1 f(x)g(x)d x $
    C'est une forme bilinéaire symétrique définie positive (par positivité de l'intégrale et critère de nullité)
  + $MM_n (RR)$ muni du produit scalaire usuel $ scal2(., .) : (A,B) |-> Tr(transp(A)B) $
    C'est bien une forme bilinéaire symétrique. Montrons que c'est défini positif :
    Soit $A = (a_(i,j))_(1<=i,j<=n), B = (b_(i,j))_(1<=i,j<=n), transp(A)B = (c_(i,j))_(1<=i,j<=n)$,
    Alors $c_(i,j) = sum_(k = 1)^n a_(k i) b_(k j)$

    Donc $Tr(transp(A)B) = sum_(i = 1)^n c_(i i) = sum_(i = 1)^n sun_(j = 1)^n a_(k i)b_(k i) = sum_(1<=i,j<=n)a_(k i) b_(k i)$

    Ainsi $scal2(A, A) = Tr(transp(A)A) = sum_(i,k=1)^n a_(k i)^2 >= 0$ et $scal2(A, A) = 0 <==> forall i,k in [|1,n|] : a_(k,i)^2 = 0 <==> A = 0$
]

Puisque pour tout $x in E$, $scal2(x, x) >= 0$, on note $norm(x) = sqrt(scal2(x, x))$

#remark[
  - $norm(x) = 0 <==> x = 0_E$
  - $forall lambda in RR, norm(lambda x) = sqrt(scal2(lambda x, lambda x)) = sqrt(lambda^2 scal2(x, x)) = |lambda|norm(x)$
]

#proposition("Formules de polarisation")[
  $forall x,y in E :$
  $
    scal2(x, y) & = 1/2 (norm(x + y)^2 - norm(x)^2 - norm(y)^2) \
    & = 1/4 (norm(x + y)^2 - norm(x - y)^2)
  $

  On a donc une relation entre la norme et le produit scalaire
]

#proof[
  + $
  norm(x + y) = scal2(x+y,x+y) = scal2(x,x+y) + scal2(y,x+y) = scal2(x,x) + scal2(x,y) + scal2(y,x) + scal2(y,y) = norm(x)^2 + 2scal2(x,y) + norm(y)^2
  $
  ce qui donne la première formule en isolant $scal2(x,y)$

  + $
    cases(norm(x + y) = norm(x)^2 + 2 scal2(x,y) + norm(y), norm(x-y) = norm(x)^2 - 2 scal2(x,y) + norm(y)^2)
    $
    On a donc le résultat en sommant et isolant $scal2(x,y)$
]

#corollary("Identité du parallélogramme")[
  $forall x,y in E$ : $norm(x + y)^2 + norm(x-y)^2 = 2 (norm(x)^2 + norm(y)^2)$
]

#theorem("Inégalité de Cauchy-Schwarz")[
  Soit $E$ un espace préhilbertien réel. Alors
  $forall x,y in E :$
  $
  abs(scal2(x,y)) <= norm(x)norm(y)
  $
  avec égalité ssi $(x,y)$ liée.
]

#proof[
  Si $x = 0$ ou $y = lambda x$, on a égalité :
  $scal2(x,lambda x) = lambda norm(x)^2$

  Supposons maintenant $(x,y)$ libre. Soit $lambda in RR$.

  $norm(x + lambda y)^2 = scal2(x+lambda y,x+lambda y) = scal2(x,x+lambda y) + lambda scal2(y,x+lambda y) = scal2(x,x) + lambda scal2(x, y) + lambda^2 scal2(y,y) + lambda scal2(x,y) = norm(x)^2 + 2lambda scal2(x,y) + norm(y)^2$
  C'est un polynôme de degré 2 en lambda qui ne s'annule pas, car à coefficients positifs. Ainsi son déterminant est $<= 0$. Donc :
  $Delta = 4 scal2(x,y)^2 - 4 norm(x)norm(y) <= 0 <=> abs(scal2(x,y)) <= norm(x)norm(y)$

  D'où l'inégalité.
  Montrons que si l'on a égalité, $y = lambda x$.

  Supposons $abs(scal2(x,y)) = norm(x)norm(y)$. Posons $alpha = scal2(x,y)/norm(x)^2$ (on suppose que $x !=0$ donc $norm(x) != 0$)

  Ainsi :
  $
  scal2(y-alpha x, y - alpha x) = norm(y - alpha x)^2 = norm(y)^2 - 2alpha scal2(x,y) + alpha^2 norm(x) = norm(y)^2- 2 scal2(x,y)^2/norm(x^2) + scal2(x,y)^2/norm(x)^2 = norm(y)^2 - scal2(x,y)^2/norm(x)^2$.
  Or par hypothèse : $norm(y)^2 = scal2(x,y)^2/norm(x)^2$ donc $norm(y - alpha x) = 0$ càd $y = alpha x$
]

#corollary("Inégalité de Minkowski")[
  Soit $E$ un espace préhilbertien réel.

  Pour tout $x,y in E$ : $norm(x + y) <= norm(x) + norm(y)$

  avec égalité ssi $x,y$ sont positivement liés i.e. $x = 0$ ou $x = lambda y$ avec $lambda in RR^+$
]
#proof[
  $norm(x + y)^2 = norm(x)^2 + 2 scal2(x,y) + norm(y)^2 <=^"C-S" norm(x^2) + norm(y)^2 + 2 norm(x)norm(y) = (norm(x)+norm(y))^2$

  Par positivité de la norme :
  $
  norm(x + y) <= norm(x) + norm(y)
  $

  Si x = 0, facile
  Si $y = lambda x$ avec $lambda in RR$ :
  $norm(x+y) = (lambda+1) norm(x)$ d'où l'égalité.
  
  Réciproquement, si on a égalité, on a le cas d'égalité de Cauchy-Schwarz + $abs(scal2(x,y)) = scal2(x,y)$. D'où la liaison positive.
]

#corollary[
  L'application $norm(.) : E -> RR$ est une norme, dite euclidienne, sur E.

  On appelle Espace de Hilbert réel tout Espace Préhilbertien complet pour sa norme euclidienne.
]

#remark("Rappel sur la complétude")[
  $(F,norm(.))$ est complet si toute suite convergente y est de cauchy pour $norm(.)$.
]

#remark[
  Si $x,y$ deux vecteurs non-nuls de $E$, l'inégalité de Cauchy-Schwarz donne :
  $
  abs(scal2(x,y))/(norm(x)norm(y)) <= 1
  $
  Donc $exists! theta in [0,pi]$ tel que $cos theta = scal2(x,y)/(norm(x)norm(y))$. $theta$ est dit angle (non-orienté) entre les vecteurs $x$ et $y$.
]
