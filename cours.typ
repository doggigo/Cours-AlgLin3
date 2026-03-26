#import "@local/utils:0.1.0": *
#import "@local/doc_fac:0.1.0" as theme_colors
#import "@local/doc_cours_nb:0.1.0" as theme_nb

#let theme_default = "colors"

#let theme_name = sys.inputs.at("theme", default: theme_default)


#let theme = if theme_name == "colors" { theme_colors } else { theme_nb }

#let theorem = theme.theorem
#let corollary = theme.corollary
#let lemma = theme.lemma
#let property = theme.property
#let proposition = theme.proposition
#let exercice = theme.exercice
#let example = theme.example
#let notation = theme.notation
#let remark = theme.remark
#let method = theme.method
#let definition = theme.definition
#let vocabulary = theme.vocabulary
#let proof = theme.proof

#let only-thms = sys.inputs.at("only-thms", default: "false") == "true"

#show: theme.doc_fac.with(
  title: "Cours AlgLin3",
  numbering: "I. 1. 1. a) i)",
  show-examples: not only-thms,
  show-exercises: not only-thms,
  show-proofs: not only-thms,
  page-numbering: "1",
)

#outline()

= Dualité

$KK$ désigne un corps $(KK = RR "ou" CC)$, $E$ sera un $KK-$ev
== Dual

#definition[
  On appelle forme linéaire sur $E$ toute application linéaire de $E$ à valeur dans $KK$.

  On appelle *dual* de $E$, noté $E^*$ (ou $E^checkmark$) le $KK$-ev formé des formes linéaires sur $E$, $E = Lin(E, KK)$.
]

#example[
  + L'application nulle : $0 : application(E, KK, x, 0)$
  + $ application(RR^3, RR, (x,y,z), 3x-y+2z) $ est une fome linéaire sur $RR^3$
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
  + $H = {A in M_n (KK) | Tr(A) = 0}$ est un hyperplan de $M_n (KK)$. Tr est non-nulle : $Tr(I_n) = n$ par ex
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

#method("Trouver une base duale/antéduale")[
  En connaissant la base duale de la base canonique, on peut calculer la base duale de $(f_i)$ en prenant $M^* = transp(M^(-1))$ avec $M = Mat_((f_i),"b.c")(Id)$

  #v(.5em)

  De même, pour trouver la base antéduale de $f_i^*$, on peut prendre la transposée de $Mat_((f_i^*),"b.c.")(Id)$
]

#method("2nde méthode")[
  On a : $ e_i^*(x) = 1/det(M) det(e_1, dots, e_(i-1), x, e_(i+1), dots, e_n) $

  qui est bien une application et vaut $delta_(i j)$ c'est-à-dire $cases(1 "si" x = e_i, 0 "sinon")$
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
      norm(x + y) = scal2(x+y, x+y) & = scal2(x, x+y) + scal2(y, x+y)
                                      = scal2(x, x) + scal2(x, y) + scal2(y, x) + scal2(y, y) \
                                    & = norm(x)^2 + 2scal2(x, y) + norm(y)^2
    $
  ce qui donne la première formule en isolant $scal2(x, y)$

  + $
      cases(norm(x + y) = norm(x)^2 + 2 scal2(x, y) + norm(y), norm(x-y) = norm(x)^2 - 2 scal2(x, y) + norm(y)^2)
    $
    On a donc le résultat en sommant et isolant $scal2(x, y)$
]

#corollary("Identité du parallélogramme")[
  $forall x,y in E$ : $norm(x + y)^2 + norm(x-y)^2 = 2 (norm(x)^2 + norm(y)^2)$
]

#theorem("Inégalité de Cauchy-Schwarz")[
  Soit $E$ un espace préhilbertien réel. Alors
  $forall x,y in E :$
  $
    abs(scal2(x, y)) <= norm(x)norm(y)
  $
  avec égalité ssi $(x,y)$ liée.
]

#proof[
  Si $x = 0$ ou $y = lambda x$, on a égalité :
  $scal2(x, lambda x) = lambda norm(x)^2$

  Supposons maintenant $(x,y)$ libre. Soit $lambda in RR$.

  $norm(x + lambda y)^2 = scal2(x+lambda y, x+lambda y) = scal2(x, x+lambda y) + lambda scal2(y, x+lambda y) = scal2(x, x) + lambda scal2(x, y) + lambda^2 scal2(y, y) + lambda scal2(x, y) = norm(x)^2 + 2lambda scal2(x, y) + norm(y)^2$
  C'est un polynôme de degré 2 en lambda qui ne s'annule pas, car à coefficients positifs. Ainsi son déterminant est $<= 0$. Donc :
  $Delta = 4 scal2(x, y)^2 - 4 norm(x)norm(y) <= 0 <=> abs(scal2(x, y)) <= norm(x)norm(y)$

  D'où l'inégalité.
  Montrons que si l'on a égalité, $y = lambda x$.

  Supposons $abs(scal2(x, y)) = norm(x)norm(y)$. Posons $alpha = scal2(x, y)/norm(x)^2$ (on suppose que $x !=0$ donc $norm(x) != 0$)

  Ainsi :
  $scal2(y-alpha x, y - alpha x) = norm(y - alpha x)^2 = norm(y)^2 - 2alpha scal2(x, y) + alpha^2 norm(x) = norm(y)^2- 2 scal2(x, y)^2/norm(x^2) + scal2(x, y)^2/norm(x)^2 = norm(y)^2 - scal2(x, y)^2/norm(x)^2$.
  Or par hypothèse : $norm(y)^2 = scal2(x, y)^2/norm(x)^2$ donc $norm(y - alpha x) = 0$ càd $y = alpha x$
]

#corollary("Inégalité de Minkowski")[
  Soit $E$ un espace préhilbertien réel.

  Pour tout $x,y in E$ : $norm(x + y) <= norm(x) + norm(y)$

  avec égalité ssi $x,y$ sont positivement liés i.e. $x = 0$ ou $x = lambda y$ avec $lambda in RR^+$
]
#proof[
  $norm(x + y)^2 = norm(x)^2 + 2 scal2(x, y) + norm(y)^2 <=^"C-S" norm(x^2) + norm(y)^2 + 2 norm(x)norm(y) = (norm(x)+norm(y))^2$

  Par positivité de la norme :
  $
    norm(x + y) <= norm(x) + norm(y)
  $

  Si $x = 0$, facile
  Si $y = lambda x$ avec $lambda in RR$ :
  $norm(x+y) = (lambda+1) norm(x)$ d'où l'égalité.

  Réciproquement, si on a égalité, on a le cas d'égalité de Cauchy-Schwarz + $abs(scal2(x, y)) = scal2(x, y)$. D'où la liaison positive.
]

#corollary[
  L'application $norm(.) : E -> RR$ est une norme, dite euclidienne, sur E.

  On appelle Espace de Hilbert réel tout Espace Préhilbertien complet pour sa norme euclidienne.
]

#remark("Rappel sur la complétude")[
  $(F,norm(.))$ est complet si toute suite convergente y est de Cauchy pour $norm(.)$.
]

#remark[
  Si $x,y$ deux vecteurs non-nuls de $E$, l'inégalité de Cauchy-Schwarz donne :
  $
    abs(scal2(x, y))/(norm(x)norm(y)) <= 1
  $
  Donc $exists! theta in [0,pi]$ tel que $cos theta = scal2(x, y)/(norm(x)norm(y))$. $theta$ est dit angle (non-orienté) entre les vecteurs $x$ et $y$.
]

#pagebreak()

= Réduction de Gauss
Donnons-nous un $RR$-ev muni d'une base $(e_1,dots,e_n)$. Soient $x = sum_(i = 1)^n x_i e_i, y = sum_(i = 1)^n y_i e_i$

Soit $f$ une forme #underline("bilinéaire") sur $E$.

Alors :
$
  f(x,y) = f(sum_(i=1)^n x_i e_i,sum_(i=1)^n y_i e_i) = sum_(i=1)^n x_i f(e_i, sum_(j=1)^n y_j e_j) = sum_(i=1)^n sum_(j=1)^n x_i y_j f(e_i,e_j)
$

Si on note $a_(i j) = f(e_i,e_j)$ :
$
  f(x,y) = sum_(i,j=1)^n a_(i j)x_i y_j
$

Maintenant, si $f$ est symétrique :
$
  a_(i j) = f(e_i, e_j) = f(e_j, e_i) = a_(j i)
$
Donc $f(x,x) = underbrace([sum_(i = 1)^n a_(i i)x_i^2], "terme carré") + underbrace([2 sum_(1 <= i < j <= n) a_(i j) x_i x_j], "terme rectangle")$

Donc se donner une norme euclidienne revient à se donner un polynôme homogène de degré 2 en les $x_i$, $i = 1 ... n$ (pourvu que $f$ soit définie positive).

En particulier, $norm(lambda x)^2 = lambda^2 norm(x)^2 quad forall lambda in RR$

#method("Polarisation")[
  La forme polaire $(f(x,y))$ d'une forme bilinéaire symétrique s'obtient à partir de la forme quadratique en #underline(["polarisant les monômes"]).
  + Les termes carrés $a_(i i) x_i^2$ deviennent $a_(i i)x_i y_i$
  + Les termes rectangles $a_(i j)x_i x_j$ deviennent $1/2 (a_(i j) x_i y_j + a_(j i) x_j y_i)$

]

#example[
  $E = RR^3, thick f(x,x) = x_1^2 + 2x_2^2 + 3x_3^2 + 4 x_1 x_2 + x_1 x_3$

  Soit $x = (x_1,x_2,x_3)$, $y = (y_1,y_2,y_3)$

  $
    f(x,y) & = x_1 y_1 + 2 x_2y_2 + 3x_3y_3 + 1/2 ( 4 (x_1 y_2 + x_2 y_1) + (x_1y_3 + x_3y_1)) \
           & = x_1 y_1 + 2 x_2y_2 + 3x_3y_3 + 2 (x_1y_2 + x_2 y_1) + 1/2 (x_1 y_3 + x_3 y_1)
  $
]

La réduction de Gauss est un algorithme permettant de décomposer tout polynôme homogène de degré $2$ en somme de carrés de formes linéaires indépendantes. Elle repose sur les identités :
$
  cases(
    a^2 + 2a b = (a+b)^2 - b^2 quad & (A),
    a b = 1/4 (a+b)^2 - 1/4 (a-b)^2 quad & (B)
  )
$

On utilisera, dans ce chapitre, majoritairement $(A)$. $(B)$ servira surtout plus tard.

Il faut choisir en priorité les termes carrés, et si possible de coefficient $+-1$. Voir les exemples

#example[
  $E = RR^3, thick (e_1,e_2,e_3) "la b.c."$, et $ f(x,x) = x_1^2 + 2 x_2^2 + 5 x_3^2 + 2x_1x_2 - 4x_2x_3 $

  Choisissons le terme $x_1^2$

  Alors $ f(x,x) & = (x_1^2 + 2x_1x_2) + 2x_2^2 + 5 x_3^2 - 4x_2x_3 \
         & =^((A)) [(x_1+x_2)^2 - x_2^2] + 2x_2^2 + 5x_3^2 - 4x_2x_3 \
         & = (x_1+x_2)^2 + x_2^2 + 5x_3^2 - 4x_2x_3 $
  Choisissons le terme $x_2^2$
  Alors $ f(x,x) & = (x_1 + x_2)^2 + (x_2^2 - 4 x_2 x_3) + 5 x_3^2 \
         & =^((A)) (x_1 + x_2)^2 + [(x_2-2x_3)^2 - 4x_3^2] + 5x_3^2 \
         & = (x_1 + x_2)^2 + (x_2 - 2x_3)^2 + x_3^2 >= 0 $

  $f(x,x) = 0 <==> cases(x_1 + x_2 = 0, x_2 - 2x_3 = 0, x_3 = 0) <==> x = (0,0,0)$

  $f$ est un produit scalaire sur $RR^3$.

  On n'aura pas besoin de prouver que $f(x,x) = 0 => x = 0$ par véracité de l'algorithme.


  Les formes linéaires obtenues sont indépendantes. Posons $ l_1(x) = x_1 + x_2, & "soit" l_1 = e_1^* + e_2^* \
  l_2(x) = x_2 - 2x_3 & "soit" l_2 = e_2^* - 2e_3^* \
         l_3(x) = x_3 & "soit" l_3 = e_3^* $

  $(l_1,l_2,l_3)$ est libre car $det(l_1, l_2, l_3) = 1 != 0$, d'où $(l_1,l_2,l_3)$ base de $(RR^3)^*$
]

#example[
  $E = RR^3, x = (x_1,x_2, x_3), quad f(x,x) = x_1 x_2 + x_1 x_3 + x_2 x_3$

  Choisissons le terme $x_1 x_2$

  Alors $ f(x,x) & = underbrace((x_1 + x_3), a)underbrace((x_2+x_3), b) - x_3^2 \
         & =^((B))1/4 (x_1 + x_2 + 3x_3)^2 - 1/4 (x_1 + x_2 + 2x_3)^2 - 1/4 (x_1 - x_2)^2 - x_3^2 $
  n'est pas positive, $f((-2,0,1),(-2,0,1)) = -1-1 = -2 < 0$ donc $f$ n'est pas un produit scalaire.

  Si on pose $l_1 = e_1^* + e_2^*, l_2 = e_1^* - e_2^*, l_3 = e_3^*$, alors $(l_1,l_2,l_3)$ est libre.
]

#example[
  $E = RR^3, quad x = (x_1,x_2,x_3)$

  $
    f(x,x) & = underbracket(x_1^2) + 5x_2^2 + 2x_3^2 + 4x_1x_2 - 2x_1x_3 - 2x_2x_3 \
           & = (x_1^2 + 4x_1x_2 - 2x_1x_3) + 5x_2^2 + 2x_3^2 - 2x_2x_3 \
           & = [x_1 + 2x_1(2x_2 - x_3)] + 5x_2^2 + 2x_3^2 - 2x_2x_3 \
           & =^((A)) [(x_1 + 2x_2 - x_3)^2 - (2x_2 - x_3)^2] + 5x_2_2x_3^2 - 2x_2x_3 \
           & = (x_1 + 2x_2 - x_3)^2 + x_2^2 + x_3^2 + 2 x_2 x_3 \
           & = (x_1 + 2x_2 - x_3)^2 + (x_2 + x_3)^2 >= 0
  $

  Si on pose $l_1 = e_1^* + 2e_2^* - e_3^*, l_2 = e_2^* + e_3^*$.
  $(l_1, l_2)$ est libre, mais ne forme pas une base de $E^*$, c'est-à-dire que $f(x,x) = 0$ est une équation à 3 inconnues et 2 équations, donc admet une infinité de solutions (Cramer etc..), ainsi $f$ n'est pas un produit scalaire.
]

#proposition("Réduction de Gauss")[
  Soit $E$ un $KK$-ev de dimension finie,
  alors il existe un algorithme permettant de décomposer toute forme quadratique sur $E$ en une combinaison linéaire de carrés de formes linéaires.
]

#method("Réduction de Gauss")[
  Soit $E$ un $KK$-ev, $f in BBB(E)$. L'algorithme de Gauss s'effectue de cette manière :
  + Se ramener à $f(x,x) = sum_(i = 1)^n a_(i i)x_i^2 + 2 sum_(1 <= i < j <= n) a_(i j) x_i x_j$ avec $a_(i,j) = f(e_i,e_j)$
  + Choisir un terme, de préférence carré s'il existe, sinon rectangle.
    - Si le terme est un carré $a x_i^2$ rassembler tous les $x_i$ sous la forme : $ a x_i^2 + 2 x_i L(x_1,dots,x_(i-1),x_(i+1),x_n) = a[x_i^2 + (2x_i L)/a] $
      avec $L$ forme linéaire ne dépendant pas de $x_i$, $q$ forme bilinéaire n'en dépendant pas non plus.

      Puis remarquer l'identité $(A)$ :
      $ a[x_i^2 + (2x_i L)/a] = a[(x_i + L/a)^2 - (L/a)^2] = a(x_i+L/a)^2 - L^2/a $ et enfin, développer la partie négative

    - Si le terme est un rectangle $x_i x_j$, utiliser l'identité (B) : $x_i x_j = 1/4 (x_i + x_j)^2 - 1/4 (x_i - x_j)^2$ puis développer la partie négative et continuer
  + Répéter sur les termes qui ne sont pas isolés.

]

#proof([Pt. 1 : Énonciation de la récurrence et cas avec terme carré])[
  La démonstration se fait par récurrence sur $n = dim E$.

  On suppose que $f$ est une forme bilinéaire symétrique non-nulle.
  + Si $n = 1, f(x,x) = a x^2, a in RR^*$, rien à dire.
  + Supposons que pour tout $p < n$, on ait un algorithme permettant de décomposer tout polynôme de degré 2 sur un espace de dimension $p$ en une combinaison linéaire de carrés de formes linéaires indépendantes.

    Soit $E$ de dimension $n$, muni d'une base $(e_i)_(1<=i<=n)$ et d'une forme bilinéaire symétrique non-nulle. Soit $x = sum_(i = 1)^n x_i e_i$

    + Supposons que $f(x,x)$ possède un terme carré que l'on peut supposer être $a x_1^2, a in RR^*$
      $f(x,x) = a x_1^2 + x_1 L(x_2, dots, x_n) + f_1 (x_2, dots, x_n)$ où $L$ est une forme linéaire en $x_2, dots, x_n$ et $f_1$ est un polynôme homogène de degré 2 en $x_2, dots x_n$.

      $
        f(x,x) & = a[x_1^2 + 2x_1 L(x_2,dots,x_n)/(2a)] + f_1 (x_2,dots,x_n) \
               & =^((A)) a[(x_1 + L(x_1, dots, x_n)/(2a)) - L(x_2, dots,x_n)^2/(4 a^2)] + f_1(x_2,dots,x_n) \
               & = a(x_1 + L(x_2, dots,x_n)/(2a))^2 + q(x_2, dots, x_n) quad "où" q(x_1,dots,x_n) \
               & = -L(x_2,dots,x_n)^2/(4 a) + f(x_2,dots,x_n)
      $
      c'est un polynôme de degré 2 où n'apparaît pas $x_1$

      On applique l'hypothèse de récurrence à $Vect(e_2, dots, e_n)$ muni de $q$ si $q != 0$. Rq : si $q = 0$, on a fini.

      On a : $q(x_2, dots, x_n) = sum_(i =2)^r a_i l_i^2 (x_2,dots,x_n)$ où $(l_2, dots,l_r)$ est une famille libre de $Vect(e_2, dots, e_n)^*$.

      Si $x = sum_(i = 1)^n x_i e_i in E$, notons $phi_j(x_1,dots,x_n) = phi_j (x_1,dots,x_n) = phi_j (x_2,dots,x_n)$, pour $j = 2,...,r$ et $phi_1 (x_1,dots,x_n) = x_1 + L(x_2, dots, x_n)/(2 a)$

      $f(x,x) = a phi_1^2(x_1, dots, x_n) + sum_(j = 2)^r a_j phi_j (x_1,dots,x_n)^2$. Il reste à montrer que $(phi_1, dots, phi_r)$ est libre dans $E^*$. Soit l'équation $sum_(i = 1)^r lambda_i phi_i = 0$. En particulier $sum_(i=1)^r lambda_i phi_i (e_1) = lambda_1 phi_1(e_1) = lambda_1 = 0$.

      Pour $j = 2, dots, r, sum_(i = 1)^r lambda_i phi_i (e_j) = sum_(i = 2)^r lambda_i phi_i (e_j) = 0$, alors $lambda_i = 0 forall i in [|2,r|]$ car $(phi_2, dots, phi_r)$ libre.
]

#proof([Cas où aucun terme carré (on travaille avec les termes rectangles)])[

  Si $f$ ne contient  aucun terme carré, donnons-nous une forme rectangle, par exemple $a x_1 x_2, a in RR^*$
  $
    f(x,x) = a x_1 x_2 + x_1 L(x_3, dots, x_n) + x_2 L_2 (x_3, dots, x_n) + f_2(x_3,dots,x_n)
  $
  où $L_1,L_2$ sont des formes linéaires en $x_3,dots,x_n$ et $f_2$ un polynôme homogène en $x_3, dots, x_n$.
  $
    f(x,x) &= a[x_1x_2 + X_1 L_1(x_3, dots, x_n)/a + x_2 L_2 (x_3, dots, x_n)/a] + f_2 (x_3, dots, x_n \
    &= a[(x_1 + (L_2(x_3, dots, x_n))/a)(x_2 + (L_1(x_3,dots,x_n))/a) - (L_1 (x_3,dots,x_n)L_2(x_3,dots,x_n))/a^2] + f_2 (x_3,dots,x_n) \
    &=^((B)) a[1/4 (x_1 + x_2 + (L_1(x_3,dots,x_n))/a + (L_2(x_3,dots,x_n))/a)^2 - 1/4 (x_1-x_2+ ((L_2(x_3,dots,x_n)-L_1(x_3,dots,_n))/a)^2 )] \
    &- (L_1(x_3,dots,x_n)L_2(x_3,dots,x_n))/a + f_2 (x_3,dots,x_n)
  $

  $q(x_3,dots,x_n) = - (L_1(x_3,dots,x_n)L_2(x_3,dots,x_n))/a + f_2 (x_3,dots,x_n)$ est un polynôme homogène de degré $2$ sur $Vect(e_3, dots, e_n)$.

  Si $q = 0$, c'est fini, si $q != 0$, on applique l'hypothèse de récurrence à $q$ sur $Vect(e_3, dots, e_n)$.

  $q(x_3,dots,x_n) = sum_( i = 3)^s a_i l_i (x_3,dots,x_n)^2$ avec $(l_3,dots,l_s)$ libre dans $Vect(e_3, dots, e_n)^*$

  Posons $ phi_1(x_1,dots,x_n) = x_1 + x_2 + (L_1(x_3,dots,x_n) + L_2(x_3,dots,x_n))/a \
  phi_2(x_1,dots,x_n) = x_1 + x_2 + (L_2(x_3,dots,x_n) - L_1(x_3,dots,x_n))/a \
  forall i = 3,dots,s,phi_i(x_1,dots,x_n) = l_i (x_3,dots,x_n) $

  Il reste à montrer que $phi_1,dots,phi_s$ est libre dans $E^*$

  Soit l'équation $sum_(i = 1)^n phi_i = 0$

  En particulier
  $
    sum_(i = 1)^s lambda_i phi_i (e_i) lambda_1 phi_1(e_i) + lambda_2 phi_2(e_1) = lambda_1 + lambda_2 = 0 \
    sum_(i = 1)^s lambda_i phi_i (e_2) = lambda_1 phi_1(e_2) + lambda_2 phi_2 (e_2) = lambda_1 - lambda_2 = 0
  $
  d'où $cases(lambda_1 + lambda_2 = 0, lambda_1 - lambda_2 = 0) => lambda_1 = lambda_2 = 0$

  On termine comme dans le premier cas pour déduire les autres coefficients.
]

#remark[
  L'algorithme de réduction de Gauss n'est pas unique mais il permet d'obtenir une famille libre sur $E^*$.
]

#theorem[
  Soit $f$ une forme bilinéaire symétrique sur un $RR$-ev de dimension finie $n$. Alors :

  $f$ est définie positive (i.e. produit scalaire) sur $E$ si, et seulement si la réduction de Gauss de $f$ est une combinaison linéaire de $n$ carrés de formes linéaires (indépendantes) à coefficients strictement positifs.
]

#proof[
  Notons qu'il est nécessaire d'avoir un terme carré à chaque étape de la réduction pour que $f$ soit positive. Si la réduction de Gauss donne une combinaison linéaire de $n$ carrés à coefficients strictement positifs, $f$ sera positive et $f(x,x) = 0$ donne un système homogène de $n$ équations à $n$ inconnues qui est échelonné (puisqu'on enlève une variable à chaque étape). Ce système admet une unique solution qui va être nulle. Donc $f$ est définie.

  Réciproquement :
  Si la réduction de Gauss contient strictement moins de $n$ carrés, le système donné par $f(x,x) = 0$ admettra des solutions non-nulles car il y a moins d'équations indépendantes que d'inconnues. (rq : $f in Lin(RR^n, RR^p), p < n$ n'est jamais injective)
]

#pagebreak()

= Représentation matricielle d'une forme bilinéaire

Soit $E$ un $RR$-ev de dimension $n$, $B in BBB(E)$, $(e_1,dots,e_n)$ une base de $E$.

Prenons $x = sum_(i = 1)^n x_i e_i$, $y = sum_(j = 1^n)y_j e_j$

Par bilinearité, $B(x,y) = sum_(i,j=1)^n x_i y_j B(e_i,e_j)$
Si on pose $a_(i j) = B(e_i,e_j)$, $A = (a_(i j))_(1<=i,j<=n) in M_n (RR)$ est appelée matrice de la forme bilinéaire $B$ dans la base $(e_1,dots,e_n)$.

Maintenant si $X = vec(x_1, vdots, x_n)$, $Y = vec(y_1, vdots, y_n)$, alors :
$
  B(x,y) = transp(X)A Y
$

#example[
  $B(x,y) = 5x_1y_1 - 2x_2y_2 + 4x_3y_3 + 7x_1y_2 + 6x_1y_3 + 6x_3y_1 + 7x_2y_1$

  dans $RR^3, quad x = (x_1,x_2,x_3), y = (y_1,y_2,y_3)$.

  Dans la base canonique de $RR^3$, la matrice de $B$ est :
  $
    A = mat(
      5, 7, 6;
      7, -2, 0;
      6, 0, 4
    )
  $
]

#remark[
  Si $B$ est symétrique, $A$ est symétrique : $forall i,j in [|1,n|] : a_(i j) = B(e_i,e_j) = B(e_j,e_i) = a_(j i)$
]

#theorem("Changement de base")[
  Si $EEE,EEE'$ sont deux bases de $E$, notons $P$ la matrice de passage de $EEE$ à $EEE'$, $A$ la matrice d'une forme bilinéaire $B in BBB(E)$ dans la base $EEE$.

  Alors la matrice de $B$ dans la base $EEE'$ est $transp(P)A P$
]

#remark[
  Attention, il ne faut pas confondre avec le changement de base d'un endomorphisme ($P^(-1) A P$).

  En particulier, $det(transp(P)A P) = det(P)^2 det(A)$ donc on ne peut pas parler de "déterminant d'une application bilinéaire".
]

#proof[
  Notons $A'$ la matrice de $B$ dans la base $EEE' = (f_1,dots,f_n)$ et $EEE = (e_1,dots,e_n)$, si $x = sum_(i = 1)^n x_i e_i = sum_(i = 1)^n x^'_i f_i$ et $y = sum_(j = 1)^n y_j e_j = sum_(j = 1)^n y^'_j f_j$
  $
    X = vec(x_1, vdots, x_n) quad X^' = vec(x^'_1, vdots, x^'_n) quad Y = vec(y_1, vdots, y_n) quad Y^' = vec(y^'_1, vdots, y^'_n)
  $

  On a $X = P X^'$ et $Y = P Y^'$
  $
    forall X,Y in M_n (RR) \
    B(x,y) = transp(X)A Y = transp(P X')A transp(P Y') = transp(X')transp(P)A P Y' = transp(X') A' Y'\
    "Donc "A' = transp(P)A P
  $

  Cette dernière égalité a lieu car l'égalité est vraie pour tout $(x,y) in E^2$. En effet :

  Si : $forall X in RR^n, thick M X = 0$ alors $M = 0$

  $
    (forall X,Y in RR^n, transp(x) M)Y = 0 <==> transp(X) M = 0 <==> transp(transp(X)M) = X transp(M) = 0 \
    <==> transp(M) = 0 = M \
    M = transp(P)A P - A^'
  $
]

#pagebreak()

= Orthogonalité
Soit $(E,scal2(., .))$ un espace euclidien.

#definition[
  Soit $A subset E$ quelconque, on pose :
  $A^ortho = {x in E | scal2(x, y) = 0 forall y in A}$

  $A^ortho$ est un sous-espace vectoriel de $E$ (même si $A$ ne l'est pas) appelé "orthogonal de $A$"
]

#proof[
  Soient $x,x' in A^ortho, lambda in RR$. ALors pour tout $y in A$ :
  $scal2(lambda x + x', y) = lambda scal2(x, y) + scal2(x', y) = 0$

  D'où $lambda x + x' in A^ortho$
]

#proposition[
  Pour tout #underline([sous-espace vectoriel $F$]) de $E$, on a :
  + $dim F + dim F^ortho = dim E$
  + $E = F operp2 F^ortho$
  + $(F^ortho)^ortho = F$
]

#proof[
  On se donne $(v_1,dots,v_p)$ une base de $F$, on la complète en une base $(v_1,dots,v_n)$ de $E$. Si On note $A = (a_(i j))_(1<=i,j<=n)$ la matrice de $scal2(., .)$ dans cette base.

  Si $x = sum_(i = 1)^n x_i v_i, y = sum_(j = 1)^n y_j v_j$. Alors : $scal2(x, y) = sum_(i,j=1)^n a_(i,j) x_i y_j$

  $x in F^ortho <==>^"exo" forall j in [|1,p|] , underbrace(scal2(x, v_j), =transp(X)A V_j) = 0$

  $
    cases(scal2(v_1, x) = 0, vdots, scal2(v_p, x) = 0) <==> cases(sum_(j = 1)a_(1 j) x_j = 0, vdots, sum_(j=1)^n a_(p j) x_j = 0) <==> cases(a_(1 1)x_1 + dots + a_(1 n) x_n = 0, vdots, a_(p 1) x_1 + dots + a_(p n) x+n = 0)
  $

  Ainsi $x in F^ortho$ ssi ses coordonnées $(x_1,dots,x_n)$ sont solutions de ce système à $p$ équations, $n$ inconnues.

  Ces équations sont linéairement indépendantes, car $det(A) != 0$ (on a un produit scalaire). En effet, si $A X = 0, transp(X)A X = scal2(X, X) = 0 ==>^(scal2(., .) "défini") X = 0$

  Le rang du système est $p$ donc l'ensemble des solutions est  l'intersection de $p$ hyperplans linéairement indépendants et est donc de dimension $n-p$. Donc $dim(F^ortho) = n-p$ d'où la première partie.

  Pour la 2nde, Il suffit de montrer que $F inter F^ortho = {0_E}$. Soit $x in F inter F^ortho$, $scal2(x, x) = 0$. Par définition de $scal2(., .)$, $x = 0$.

  Pour la 3e, on a $F subset (F^ortho)^ortho$ car si $x in F$, alors $scal2(x, y) = 0 forall y in F^ortho$. Alors $x in (F^ortho)^ortho$
  et on a :
  $
    dim((F^ortho)^ortho) = dim(E) - dim(F^ortho) = dim(E) - dim(E) + dim(F) = dim(F)
  $
  d'où l'égalité.
]

#example[
  Soit $SSS$ (resp $AAA$) le sev de $M_n (RR)$ formé des matrices symétriques (resp. antisymétriques). On sait que $M_n (RR)$ formé des matrices symétriques (resp. antisymétriques).

  On sait que $M_n (RR) = SSS osum AAA$ ($M = 1/2 underbrace((transp(M) - M), in SSS) + 1/2 underbrace((M - transp(P)), in AAA)$). De plus, $AAA = SSS^ortho$ pour le produit scalaire standard de $MM_n (RR)$ :
  $
    scal2(M, N) = Tr(transp(M)M)
  $
  Prenons $M in SSS, N in AAA$ :
  $
    scal2(M, N) = Tr(transp(M)N) = Tr(M N) = Tr(N M)= Tr(-transp(N) M) = - Tr(transp(N)M) = - scal2(M, N)
  $
  Donc $scal2(M, N) = 0$.
]

#property[
  Soient $F,G$ deux sous-espaces vectoriels d'un espace euclidien $E$.
  + $F subset G ==> F^ortho supset G^ortho$
  + $(F + G)^ortho = F^ortho inter G^ortho$
  + $(F inter G)^ortho = F^ortho + G^ortho$
]

#proof[
  + Soit $y in G, scal2(y, x) = 0 forall x in G supset F$, donc $scal2(y, x) forall x in F, y in F^ortho$.
  + $F subset F + G$ donc $(F + G)^ortho subset F^ortho$ et $G subset F + G$ donc $(F + G)^ortho subset G^ortho$

    Soit : $(F + G)^ortho subset F^ortho inter G^ortho$

    Pour l'inclusion inverse : soient $x in F^ortho inter G^ortho$, $y + z in F + G$.
    $
      scal2(x, y+z) = underbrace(scal2(x, y), x in F^ortho) + underbrace(scal2(x, z), x in G^ortho) = 0
    $
    donc $x in (F+G)^ortho$
  + On applique la 2nde à $F^ortho$ et $G^ortho$. $(F^ortho + G^ortho)^ortho = F^(perp perp) inter G^(perp perp) = F inter G$ et $(F inter G)^ortho = (F^ortho + G^ortho)^(perp perp)$
]

#theorem("De Pythagore")[
  Soit $E$ un espace espace préhilbertien réel.

  Les vecteurs $x,y$ de $E$ sont orthogonaux si, et seulement si, $norm(x + y)^2 = norm(x)^2 + norm(y)^2$
]

#proof[
  $norm(x + y)^2 = norm(x)^2 + norm(y)^2 + 2 scal2(x, y) <==> norm(x + y)^2 = norm(x)^2 + norm(y)^2$
]

#pagebreak()

= Bases orthonormales


#definition[
  Une base $(e_1,dots,e_n)$ d'un espace euclidien $E$ est dite orthogonale si :
  $
    forall i,j in [|1,n|] quad i != j => scal2(e_i, e_j) = 0
  $
  On dit, de plus, qu'elle est orthonormale si :
  $
    forall i,j in [|1,n|] quad scal2(e_i, e_j) = delta_(i,j)
  $
]

#remark("Orale")[
  Dans le cours, on utilisera beaucoup les bases orthonormales, mais le processus d'orthonormalisation étant long, les exercices de TD n'appliqueront généralement que des bases orthogonales.
]

#remark[
  + La matrice d'un produit scalaire dans une base orthogonale est diagonale, et est $I_n$ dans une base orthonormale.
  + Si $(e_1,dots,e_n)$ est une base orthogonale de $E$, alors $(e_1/norm(e_1),dots,e_n/norm(e_n))$ est une base orthonormale de $E$.
  + Toute famille orthogonale formée de vecteurs non-nuls est libre.
] <rq3>

#proof("De la 3e")[
  Soit $(v_1,dots,v_p)$ orthogonale de vecteurs non-nulles.
  Considérons l'équation $sum_(i = 1)^p lambda_i v_i = 0$.

  Alors $forall j in [|1,p|] : scal2(sum_(i = 1)^p lambda_i v_i, v_j) = sum_(i = 1)^p lambda_i scal2(v_i, v_j) = lambda_j scal2(v_j, v_j) = lambda_j norm(v_j)^2 => lambda_j = 0$

  d'où la liberté.
]

#v(3em)

#example[
  La base canonique de $RR^n$ est orthogonale pour le produit scalaire standard.
]

#example[
  Considérons $E = C^0([0,2 pi],RR)$. On munit $E$ du produit scalaire $scal2(f, g) = 1/pi integral_0^(2pi) f(t)g(t)d t$.

  Notons $f_k : x |-> sin(k x)$ pour $k in NN^*$

  La famille $(f_k)_(k in NN^*)$ est orthonormale :

  $
    scal2(f_k, f_l) = 1/pi integral_0^(2 pi) sin(k t)sin (l t) d t = 1/(2 pi) integral_0^(2 pi) cos((k-l) t) - cos((k+l)t)d t
  $

  Si $k != l$, $scal2(f_k, f_l) = 0$.
  Si $k = l$ :
  $
    scal2(f_k, f_k) = norm(f_k)^2 = 1/pi integral_0^(2pi)sin^2(k t) d t = 1/(2pi) integral_0^(2pi) 1-cos(2k t) d t = 1
  $

]

#example[
  conséquences du premier exemple :
  La base canonique $(E_(i j))_(1<=i,j<=n)$ de $M_n (RR)$ (formée par les matrices élémentaires) est orthogonale pour le produit scalaire standard $scal2(M, N) = Tr(transp(M)N)$.

  On rappelle que $E_(i j) = (delta_(i r) delta_(j s))_(1<=r,s<=n)$.
  $
    scal2(E_(i j), E_(k l)) = Tr(E_(j i) E_(k l)) = delta_(i k) delta_(k l)
  $

  Donc non-nul et vaut 1 ssi $(i,j) = (k,l)$ càd $(E_(i j))$ orthonormale.
]

#theorem[
  Un espace euclidien admet toujours une base orthonormale.
]

#proof[
  Il suffit de construire une base orthogonale (cf @rq3). Montrons que tout espace euclidien non-trivial $E$ admet une base orthogonale par récurrence sur $dim(E) = n$.

  + $n = 1$, rien à dire.

  + Supposons le théorème vérifié pour tout ev de dimension $n-1$.

    Soient $E$ de dimension $n$ et $v != 0 in E$, ainsi $dim(Vect(v))^ortho = n-1$

    Par hypothèse de récurrence, $Vect(v)^ortho$ admet une base $(EEE_1,dots,EEE_(n-1))$ orthogonale, $v != Vect(v)^ortho$, donc $(EEE_1,dots,EEE_(n-1),v)$ est une base orthogonale de $E$.


  D'après le théorème de récurrence, la propriété est vérifiée pour tout ev de dimension $n >= 1$
]

#theorem("Procéde d'orthonormalisation de Gram-Schmidt")[
  Soit $(f_i)_(1<=i<=d)$ une famille libre d'un espace euclidien $(E,scal2(., .))$

  Posons $e_1 = f_1$ et pour tout $k = 1,...,d-1$, $e_(k+1) = f_(k+1) - sum_(i=1)^k scal2(e_i, f_(k+1))/norm(e_i)^2 e_i$

  La famille $(e_i)_(1<=i<=d)$ est orthogonale et pour $k = 1,...,d$, $Vect(e_1, dots, e_k) = Vect(f_1, dots, f_k)$
]

#proof[
  Par récurrence sur $d$ :
  + $d = 1$ : Rien à faire
  + Supposons la construction des $e_1,dots,e_k$ effectuée

    Comme $Vect(e_1, dots, e_k) = Vect(f_1, dots, f_k)$, on a $norm(e_i)^2 = scal2(e_i, e_i) != 0$ pour $i = 1,dots,k$
    et $e_(k+1)$ est bien défini.

    Pour $j = 1,dots,k$ :
    $
      scal2(e_i, e_(k+1)) &= scal2(e_i, f_(k+1)-sum_(j=1)^n scal2(e_j, f_(k+1))/norm(e_j)^2 e_j) = scal2(e_i, f_(k+1)) - sum_(j=1)^k scal2(e_j, f_(k+1))/norm(e_j)^2 scal2(e_i, e_j)\
      &= scal2(e_i, f_(k+1)) - scal2(e_i, f_(k+1))/norm(e_i)^2scal2(e_i, e_i) = 0
    $
    $(e_1,dots,e_(k+1))$ est une famille orthogonale.
    $e_(k+1)in Vect(f_(k+1), e_1, dots, e_k) = Vect(f_(k+1), f_i, dots, f_k)$

    Ainsi $Vect(e_1, dots, e_(k+1)) subset Vect(f_1, dots, f_(k+1))$ et donc l'égalité.
]

#example[
  dans $RR^4$ :
  $v_1 = (1,1,0,0) quad v_2 = (1,0,-1,1),v_3 = (0,1,1,1)$

  $Delta_(1,1) = matdet(1, 0, 0; 0, -1, 1; 1, 1, 1) = -2 != 0$ d'où la liberté

  Posons $e_1 = v_1$ et $norm(v_1) = sqrt(2)$

  $
    e_2 & = v_2 - scal2(v_2, e_1)/norm(e_1)^2 e_1 quad scal2(v_2, e_1) = 1 \
        & = v_2 - 1/2 e_1 = (1,0,-1,1) - 1/2 (1,1,0,0) \
        & = (1/2,-1/2,-1,1)
  $

  #underline([Remarques :])
  + On peut prendre $e_2 = (1,-1,-2,2) = 2 e_2$.
    Si $scal2(u, e_2) = 0$, alors $forall lambda in RR, scal2(u, lambda e_2) = 0$
  + On pose $e_2 = v_2 + lambda e_1$ et on écrit $scal2(e_2, e_1) = 0$. On a :

    $scal2(e_2, e_1) = scal2(e_1, v_2) + lambda scal2(e_1, e_1) = 0$ donc $lambda = - scal2(e_1, v_2)/norm(e_1)^2$

  On pose $e_3 = v_3 - scal2(v_3, e_1)/norm(e_1)^2 e_1 - scal2(v_3, e^'_2)/norm(e_2)^2 e^'_2$

  $scal2(v_3, e_1) = 1, quad norm(e^'_2)^2 = 10, quad scal2(v_3, e^'_2) = -1$

  Donc :
  $
    e_3 = (0,1,1,1) - 1/2 (1,1,0,0) + 1/10 (1,-1,-2,2) = 1/10 (-4,4,8,12) = 1/5 (-2,2,4,6) \
    "(On peut prendre" e^'_3 = (-1,1,2,3) " mais ça ne sera pas orthonormal)"
  $
  Posons $ epsilon_1 = e_1 / norm(e_1) = 1/sqrt(2) (1,1,0,0) \ epsilon_2 = e^'_2/norm(e^'_2) = 1/sqrt(10)(1,-1,-2,2) \ epsilon_3 = e^'_3/norm(e^'_3) = 1/sqrt(15)(-1,1,2,3) $ alors $(epsilon_1,epsilon_2,epsilon_3)$ est une famille orthonormale.

  #underline("Remarque"): On peut poser $e_3 = v_3 + lambda e_1 + mu e^'_2$ et on écrit $cases(scal2(e_3, e_1) = 0, scal2(e_3, e^'_2) = 0)$ qu'on peut résoudre pour retrouver la formule (qu'il faut apprendre, de toute façon.)
]

#remark[
  Ce procédé redémontre le fait que tout espace euclidien possède des bases orthonormées.
]

= Projections et symétries orthogonales

#theorem[
  Soient $(E,scal2(., .))$ un espace euclidien, $x in E$, $F$ un sev de $E$. Il existe un unique vecteur de $F$ noté $p_F (x)$ tel que $x - p_F (x) in F^ortho$. On a de plus :
  + Dans une base $(e_1,dots,e_p)$ *orthonormale* de $F$ :
    $
      p_F (x) = sum_(i=1)^p scal2(x, e_i)e_i
    $
  + L'application $p_F : application(E, F, x, p_F (x))$ est linéaire
  + $norm(x-p_F (x)) = min { norm(x-z), z in F}$
]

#definition[
  - Le vecteur $p_F (x)$ est appelé *projeté orthogonal* de $x$ sur $F$
  - L'application linéaire $p_F$ est la *projection orthogonale* sur $F$
  - On appelle *distance* de $x$ à $F$ le scalaire $norm(x-p_F (x))$ noté $d(x,F)$
]

#remark[
  +$E = F oortho F^ortho$

  $x = p_F (x) + (x-p_F (x))$

  Le théorème de Pythagore donne $norm(x)^2 - norm(p_F (x))^2 + norm(x-p_F (x))^2$

  d'où $d(x,F)^2 = norm(x)^2 - norm(p_F (x))^2$

  + Si $(f_1,dots,f_p)$ est une base orthogonale de $F$ :
    $ p_F = sum_(i=1)^p scal2(x, f_i)/norm(f_i)^2 f_i $

    Dans le procédé d'orthogonalisation de Schmidt, $(f_1,dots,f_p)$ est libre,

    $
          e_1 & = f_i \
          e_2 & = f_2 - p_(Vect(e_1)) in Vect(e_1)^ortho \
        vdots \
      e_(k+1) & = f_(k+1) - p_(Vect(e_1, dots, e_k)) (f_(k+1))
    $
    C'est-à-dire que le procédé n'est qu'une projection échelonnée.
]

#proof("du théorème")[
  + Soit $y = sum_(i=1)^p y_i e_i in F$

    Écrire que $x-y in F^perp$ est équivalent à écrire $scal2(x-y, e_i) = 0, forall i in [|1,p|]$

    ou encore $scal2(x, e_i) = scal2(y, e_i), forall i in [|1,p|]$
    $
      scal2(y, e_i) = scal2(sum_(j=1)^p y_j e_j, e_i) = sum_(j=1)^p y_j scal2(e_j, e_i)
    $
    $(e_1,dots,e_p)$ est orthonormale, $scal2(y, e_i) = y_i scal2(e_i, e_i) = y_i$

    Donc $y = sum_(i=1)^p scal2(x, e_i)e_i$ d'où l'unicité et l'existence de $p_F (x)$ et la première formule.
  + La linéarité de $p_F$ découle de la bilinéarité du produit scalaire dans la formule
  + Soit $z in F$. $ norm(x-z)^2 = norm(x-p_F (x) + (p_F (x) - z))^2 = norm(x-p_F (x))^2 + norm(p_F (x) - z)^2 >= norm(x-p_F (x))^2 $ par le théorème de Pythagore.

    avec égalité ssi $z = p_F (x)$
]

#property[
  Avec les mêmes notations :
  + $p_F compose p_F = p_F$, $Im(p_F) = F$, $Ker(p_F) = F^perp$
  + $p_F + p_(F^ortho) = Id_E$, $p_F compose p_(F^ortho) = p_(F^ortho) compose p_F = 0_(Lin(E))$
  + $forall x in E, norm(p_F (x)) <= norm(x)$
]

#proof[
  + $(p_F compose p_F)(x) = sum_(i = 1)^p scal2(p_F (x), e_i)e_i$ où $(e_1,dots,e_p)$ est une base orthonormale de $F$.

    Or $scal2(p_F (x), e_i) = scal2(sum_(j=1)^p scal2(x, e_j)e_j, e_i) = sum_(j=1)^p scal2(x, e_j) underbrace(scal2(e_j, e_i), delta_(i j)) = scal2(x, e_i)$

    Donc $(p_F compose p_F)(x) = sum_(i=1)^p scal2(x, e_i)e_i = p_F (x)$

    Si $x in Ker p_F$, càd $p_F (x) = 0_E$ alors $x - p_F (x) = x in F^perp$. La réciproque est triviale : $Ker p_F = F^perp$

    Enfin si $x in F, x = p_F (x)$.
    $x = sum_(i=1)^p x_i e_i = sum_(i=1)^p scal2(x, e_i)e_i$

    $scal2(x, e_j) = x_j thick forall j in [|1,p|]$. Donc $Im p_F = F$
  + $E = F operp2 F^perp = F^perp operp (F^perp)^perp$

    $x = p_F (x) + (x-p_F (x)) = p_(F^perp)(x) + underbrace((x - p_(F^perp)(x)), in (F^perp)^perp = F)$

    Donc $x - p_(F^perp)(x) = p_F (x)$ et $x - p_F (x) = p_(F^perp) (x)$ et $p_F + p_(F^perp) = Id_E$

    $p_F (x-p_(F^perp)(x)) = p_F (x) - (p_F compose p_(F^perp))(x)$

    Mais $x - p_(F^perp)(x) = p_F (x)$ car on vient de voir que $p_F + p_(F^perp) = Id_E$.

    $p_F (x-p_(F^perp)(x)) = p_(F)(p_(F)(x)) = p_(F)(x)$ d'où $p_F compose p_(F^perp) = 0$

    De même pour $p_(F^perp) compose p_F$
  + Si $x in E$, $scal2(x-p_(F)(x), p_(F)(x)) = 0$

    Donc $scal2(x, p_(F)(x)) = scal2(p_F (x), p_F (x)) = norm(p_F (x))^2$

    Ainsi $ 0 <= norm(x-p_F (x))^2 = scal2(x-p_(F)(x), x-p_(F)(x)) =^pi norm(x)^2 - norm(p_F (x))^2 \
    <==> norm(x)^2 >= norm(p_F (x))^2 $
]

#definition[
  Soit $F$ un sev d'un espace euclidien $(E,scal2(., .))$.

  On appelle *symétrie orthogonale* par rapport à $F$ l'application linéaire :
  $s_F = p_F - p_(F^perp) = 2 p_F - Id_E = Id_E - 2 p_(F^perp)$
]

#property[
  + $x in F <==> s_F (x) = x quad x in F^perp <==> s_F (x) = -x$
  + $s_F compose s_F = Id_E$
  + $s_F + s_(F^perp) = 0, s_F compose s_(F^perp) = s_(F^perp) compose s_F = -Id_E$
]
#proof[
  Découlent des pptés de $p_F$
]

#example[
  $F = R v = Vect(v)$, $v != 0 in RR^n$

  $p_F (x) = scal2(x, v)/norm(v)^2 v$

  $p_(F^perp)(x) = x - scal2(x, v)/norm(v)^2 v$

  $s_F (x) = 2 p_F (x) - Id_E(x) = 2scal2(x, v)/norm(v)^2v-x$
]

#remark[
  Lorsque $F$ est un hyperplan, $p_(F^perp)$ est une droite, c'est facile en utilisant $s_F = Id_E - S_(F^perp)$.
]

= Morphismes adjoints

Soit $(E,scal2(., .))$ un espace euclidien.

Notons $j : application(E, E^*, y, j(y) : application(E, RR, x, scal2(x, y)))$

$j$ est bien définie : $forall y in E, j(y)$ est linéaire car $scal2(., .)$ est bilinéaire.

#theorem("de représentation de Riesz")[
  Soit $(E,scal2(., .))$ un espace euclidien, l'application $j$ ci-dessus est  un isomorphisme.
]

#proof[
  $j$ est linéaire (déjà vu) car le produit scalaire est bilinéaire. Comme $dim(E) = dim(E^*)$, il suffit de montrer que $j$ est injective.

  Soit $y in E$ tel que $j(y) = 0_(Lin(E, RR))$

  $forall x in E, j(y)(x) = scal2(x, y) = 0$

  En particulier pour $x = y$ : $scal2(x, y) = 0$ càd $y = 0$.

  Donc $Ker(j) = {0}$ càd $j$ injective donc bijective.
]

#corollary[
  Si $EEE = (e_1,dots,e_n)$ est une base *orthonormale* d'un espace euclidien $(E,scal2(., .))$

  La base duale de $EEE$ est $EEE^* = (scal2(., e_1),dots,scal2(., e_n))$ et :

  $forall x in E, x = sum_(i = 1)^n scal2(x, e_i)e_i$

  $forall phi in E^*$, $phi = sum_(i=1)^n phi(e_i) scal2(., e_i)$
]

#corollary[
  Si $u : E --> F$ est une application linéaire entre 2 espaces euclidiens,
  il existe une *unique* application linéaire $u^* : F --> E$ telle que :
  $
    forall (x,y) in E times F, quad scal2(u(x), y)_F = scal2(x, u^*(y))_E
  $
  où $scal2(., .)_F$ (resp. $scal2(., .)_E$) désigne le produit scalaire sur $F$ (resp. E)
]
#proof[
  Soit $y in F$, l'application $x in E |--> scal2(u(x), y)_F in RR$ est une forme linéaire, elle appartient à $E^*$, mais par le théorème de représentation de Riesz, il existe un unique vecteur de $E$, notons-le $u^*(y)$, tel que :
  $
    scal2(u(x), y)_F = j(u^*(y))(x) = scal2(x, u^*(y))_E
  $
  Cela donne l'existence et l'unicité de l'application $u^* : F --> E$, il reste à montrer qu'elle est linéaire.

  $forall y,z im F, forall lambda in RR, forall x in E$ :
  $
    scal2(x, u^*(lambda y + z))_E = scal2(u(x), lambda y + z)_F = lambda scal2(u(x), y)_F + scal2(u(x), z)_F = lambda scal2(x, u^*(y))_E + scal2(x, u^*(y))_E
  $
  d'où :
  $
    forall x in E, quad scal2(x, u^*(lambda y + z) - (lambda u^*(y) + u^*(z)))_E = 0
  $

  ainsi $u^*(lambda y + z) - (lambda u^*(y) + u^*(z)) in E^ortho = {0}$ d'où $u^*(lambda y + z) - (lambda u^*(y) + u^*(z)) = 0$
]

#definition[
  L'application définie ci-dessus est appelé (morphisme) *adjoint* de $u$.
]

_Remarque : dans le cours, on prendra généralement $E = F$_

#example[
  Soit l'espace euclidien E = $MMM_n (RR)$ muni de son produit scalaire standard $scal2(M, N) = Tr(transp(M)N)$

  Donnons-nous $A in E, A != 0_E$, considérons l'endomorphisme
  $
    f_A : application(E, E, M, M A)
  $

  $forall M,N in E, quad scal2(f_A (M), N) = scal2(M A, N) = Tr(transp(M A) N) = Tr(transp(A)(transp(M)N)) = Tr(transp(M)(N transp(A))) = scal2(M, N transp(A)) = scal2(M, f_transp(A)(N))$

  Par *unicité* de l'adjoint : $f_A^* = f_(transp(A))$
]

#property("De l'adjoint")[
  Soient $E,F,G$ des espaces euclidiens
  + $Id_E^* = Id_E$ et si $u in Lin(E, F)$, $u^** = u$
  + $u |-> u^*$ est un isomorphisme entre $Lin(E, F)$ et $Lin(F, E)$
  + $forall u in Lin(E, F), v in Lin(F, G)$, $(v compose u)^* = u^* compose v^*$.

    Et si $u$ est inversible, $u^*$ aussi. Et $(u^*)^(-1) = (u^(-1))^*$
  + Si $u in Lin(E, F)$, $Ker(u^*) = (Im u)^ortho$ et $Im(u^*) = (Ker u)^perp$
  + Si $EEE$ est une base *orthonormale*, $u in Lin(E)$, la matrice de $u^*$ dans $EEE$ est la transposée de la matrice de $u$ dans la base $EEE$.
]

#proof[
  + $forall x,y in E, scal2(Id_E (x), y)_E = scal2(x, y)_E = scal2(x, Id_E (y))_E$. Par unicité de l'adjoint, $Id_E^* = Id_E$

    $forall (x,y) in E times F, scal2(y, u(x))_F = scal2(u^*(y), x)_E = scal2(y, u^(**)(x))_F$ donc $u^(**) = u$.

  + $u |-> u^*$ est linéaire. Soient $u,v in Lin(E, F)$.
    $forall (x,y) in E times F, forall lambda in RR$ :
    $
      scal2(x, (lambda u + v)^*(y))_E & = scal2((lambda u + v)(x), y)_F = lambda scal2(u(x), y)_F + scal2(v(x), y)_F \
                                      & = lambda scal2(x, u^*(y))_E + scal2(x, v^*(y))_E \
                                      & = scal2(x, (lambda u^* + v^*)(y))
    $

    donc $(lambda u + v)^* = lambda u^* + v^*$. Et c'est un isomorphisme puisque $u^(**) = u$
  + $x in E, z in G$ :
    $
      scal2((v compose u)(x), z)_G = scal2(v(u(x)), z)_G = scal2(u(x), v^*(z))_F = scal2(x, u^*(z))_E = scal2(x, (u^* compose v^*)(z))
    $

    On a : $u compose u^(-1) = Id_F$ donc $(u compose u^(-1))^* = (u^(-1))^* compose u^* = Id_F^* = Id_F$

    soit $(u^(-1))^* compose u^* = Id_F$

    $u^(-1) compose u = Id_E$ donnc $u^* compose (u^(-1))^* = Id_E$

    Ainsi $u$ est inversible et $(u^*)^(-1) = (u^(-1))^*$
  + $Ker u^* subset F, y in Ker(u^*)$ :
    $forall x in E, scal2(u^*(y), x)_E = 0 = scal2(y, u(x))_F$

    $y$ est orthogonal à tous les $u(x)$ quand $x$ varie dans $E$ : $y in (Im u)^perp$ et $Ker(u^*) subset (Im u)^perp$

    Soit $y in Im(u)^perp$, alors $forall x in E, scal2(y, u(x))_F = 0 = scal2(u^*(y), x)$ donc $u^*(y) = 0_E$
    et $y in Ker(u^*)$.

    Pour l'autre égalité, on aplique la première égaliteéà $u^*$.
  + Notons $A = Mat_EEE (u), A^* = Mat_EEE (u^*)$

    $scal2(u(x), y)_E = scal2(x, u^*(y))_E$

    Si $EEE = (e_1,dots,e_n)$, $x = sum_(i = 1)^n x_i e_i, y = sum_(i = 1)^n y_j e_j, X = vec(x_1, vdots, x_n), Y = vec(y_1, vdots, y_n)$

    Matriciellement : $scal2(u(x), y) = transp((A X)) I_n Y$

    ($I_n$ matrie du produit scalaire  dans une base orthonormale)

    $scal2(x, u^*(y))_E = transp(X)A^*Y$ d'où $A^* = transp(A)$

    $⚠️$ si $EEE$ n'est plus orthonormale, notons $M$ la matrice du produit scalaire sur $E$.

    On a : $scal2(u(x), y) = transp((A X)) M Y = transp(X)transp(A)M Y$

    et $scal2(x, u^*(y))_E = transp(X)M A^*Y$ donc $transp(A M) = M A^*$.
    $M$ est inversible et $A^* = M^(-1)transp(A)M$

]


#remark[
  La dernière assertion permet de voir qe $u$ et $u^*$ ont même trace, même déterminant, même polynôme caractéristique...

]

#proposition[
  Si $F$ est un sous-espace vectoriel d'un espace euclidien $E$ stable par un endomorphisme de $E$ ($u(F) subset F$)

  Alors $F^perp$ est stable par $u^*$ ($u^*(F^perp) subset F^perp$)
]

#proof[
  Soit $x in F^perp$, $y in F$.

  $scal2(x, y) = 0$. On doit montrer $u^*(x) in F^perp$.

  $scal2(u^*(x), y) = scal2(underbrace(x, in F^perp), underbrace(u(y), in F)) = 0$ et $u^*(x) in F^perp$
]

#definition[
  Soit $u$ un endomorphisme d'un espace euclidien $E$. On dit que $u$ est :
  + *auto-adjoint* (ou *symétrique*) si $u^* = u$
  + *orthogonal* (ou *isométrie*) si $u in G L(E)$ (càd $u$ bijectif) et $u^* = u^(-1)$
  + *normal* si $u$ et $u^*$ commutent, c'est-à-dire $u^* compose u = u compose u^*$
]

#remark[
  Si $u$ est auto-adjoint ou orthogonal, $u$ est normal.
]

= Endomorphismes des espaces euclidiens
== Isométries d'un espace euclidien
On note $O(E)$ l'ensemble des endomorphismes orthogonaux (isométries) d'un espace euclidien $E$. $(O(E),compose)$ est le groupe orthogonal :

Si $u,v,w in O(E)$
+ stabilité par $compose$ : $u compose v in O(E), (u compose v)^* = v^* compose u^* = v^(-1) compose u^(-1) = (u compose v)^(-1)$
+ associativité : $(u compose v) compose w = u compose (v compose w)$
+ élément neutre : $Id_E in O(E), Id_E^* = Id_E = Id_E^(-1)$
+ stabilite par passage à l'inverse : Si $u in O(E), u^(-1) in O(E), (u^(-1))^* = (u^*)^(-1) = (u^(-1))^(-1) = u$

#proposition[
  Soit $u$ un endomorphisme d'un espace euclidien $(E,scal2(., .))$ de dimension $n$. Les assertions suivantes sont équivalentes :
  + $u$ est une isométrie ($u in O(E)$)
  + $forall x in E, norm(u(x)) = norm(x)$
  + $forall x,y in E, scal2(u(x), u(y)) = scal2(x, y)$
  + $u$ transforme toute base orthonormale en une base orthonormale :

    Si $(e_1,dots,e_n)$ est orthonormale alors $(u(e_1),dots,u(e_n))$ aussi
  + Il existe une base orthonormale telle que si $A$ est la matrice de $u$ dans cette base : $ transp(A)A = A transp(A) = I_n $
]
_Rermarque : On utilise plutôt les deux dernières_

#proof[

  $(a) => (b)$ :

  $norm(u(x))^2 = scal2(u(x), u(x)) = scal2(x, (u^* compose u)x) = scal2(x, (u^(-1)compose u) x) = norm(x)^2$

  $(b) => (c)$ :

  on utilise une formule de polarisation :
  $
    4 scal2(u(x), u(y)) & = norm(u(x) + u(y))^2 - norm(u(x) - u(y))^2 \
                        & = norm(u(x + y))^2 - norm(u(x-y))^2 =^((b)) norm(x+y)^2-norm(x-y)^2 \
                        & =^"Polarisation" 4scal2(x, y)
  $

  $(c) => (d)$ :

  $(e_1,dots,e_n)$ base ortonormale de $E$ : $scal2(e_i, e_j) = delta_(i,j), quad forall i,j in [|1,n|]^2$

  d'aprês $(c)$ : $scal2(u(e_i), u(e_j)) = delta_(i,j)$
  càd $(u(e_1),dots,u(e_n))$ est orthonormale.

  $(d) => (e)$ :
  $A = (a_(i j))$ la matrice de $u$ dans une base orthonormale $(e_1,dots,e_n)$. D'après $(d)$ : $(u(e_1),dots,u(e_n))$ est orthonormale.

  $delta_(i j) = scal2(u(e_i), u(e_j)) = transp(A e_i)(A e_j)$ (avec $e_i$ vecteur colonne qui vaut $(delta_(i j))_(1 <= j <= n)$)

  $delta_(i j) = transp(e_i)transp(A)A e_j$

  $scal2(e_i, e_j)=transp(e_i) e_j$ d'où $transp(A)A = I_n$

  $(e) => (a)$ :
  $A^(-1) = transp(A)$ donc $A$ est inversible, donc $u$ aussi.

  Dans la base orthonormale donnée par $(e)$, $underbrace(transp(A), "matrice de "u^*) = underbrace(A^(-1), "matrice de "u^(-1))$. Et donc $u^* = u^(-1)$
]

#proposition[
  Si $u in O(E)$, alors $det(u) = +- 1$

  $⚠️$ la réciproque est fausse.
]
#example[
  $A = mat(2, 5; 1, 3)$
  $det(A) = 1$
  $A transp(A) != I_n$ (la base canonique de $RR^2$) est orthonormale pour le produit scalaire standard.
]

#proof[
  $det(u compose u^*) = det(u)det(u^*) <==> det(I_n) = det(u)^2$
  d'où $det(u) = +-1$
]

#definition[
  Le groupe spécial orthogonal (ou groupe des rotations vectorielles de $E$) est le groupe :
  $S O(E) = {u in O(E) | det(u) = 1}$
]
#proposition[
  Soit $F$ un sous-espace vectoriel d'un espace euclidien $E$.

  La symétrie orthogonale $s_F$ par rapport à $F$ est une isométrie (auto-adjointe également).

]

#proof[
  Une projection orthogonale $p_F$ est auto-adjointe $(p_F^* = p_F)$

  $forall x,y in E, scal2(p_F (x),y) = scal2(p_(F)(x),y-p_(F)(y) + p_(F)(y)) = scal2(p_(F)(x),y-p_F (y)) + scal2(p_F (x),p_F (y)) = scal2(p_F (x),p_F (y))$

  De la même façon: 
  $
  scal2(x,p_F (y)) = scal2(x-p_F (x) + p_F(x),p_F(y)) = ... = scal2(p_F (x),p_F (y)) 
  $

  Donc $forall x,y in E$ : $scal2(p_F (x),y) = scal2(x,p_F (y))$ et $p_F^* = p_F$
  - $s_F$ est autoadjointe : $s_F = 2p_F - Id_E, s_F^* = 2p_F - Id^*_E = 2p_F - Id_E = s_F$
  - $s_F$ est une isométrie : $s_F^* compose s_F = s_F compose s_F = Id_E = s_F compose s_F^*$ donc $s_F^* = s_F^(-1)$
]

#definition[
  Une symétrie orthogonale par rapport à un hyperplan est appelée *réflexion*.

  (Une symétrie orthogonale par rapport à une droite est appelée *demi-tour* ou *retournement*)
]

#remark[
  Si $H$ est un hyperplan, $e$ un vecteur unitaire base de $H^perp$.

  $
  forall x in E, s_H (x) = x - 2p_(H^perp)(x) = x-2scal2(x,e)e
  $
]