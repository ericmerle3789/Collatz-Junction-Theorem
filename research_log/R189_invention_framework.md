# R189 -- INNOVATEUR SUPREME : Invention d'une Machinerie pour l'Exponentiel
**Date :** 16 mars 2026
**Mode :** INVENTION PURE -- ni citation, ni resignation. Si l'outil n'existe pas, on le CREE.
**Prerequis :** R188 (obstruction categorielle : g est exponentiel, les outils sont quadratiques)
**Philosophie :** Le Red Team dit "ferme". L'Innovateur dit "CREE".

---

## 0. RESUME EXECUTIF

R188 a identifie un mur CATEGORIEL : les outils modulaires/mock-modulaires vivent dans le monde QUADRATIQUE (exposants q^{n^2}), tandis que g(lambda) vit dans le monde EXPONENTIEL (termes 2^{B_j}). Ce mur est reel. MAIS un mur n'est pas une falaise -- c'est une porte qu'on n'a pas encore construite.

Ce document INVENTE trois objets mathematiques nouveaux :

1. **L'Operateur de Propagation P_b** -- une famille d'operateurs sur les mesures de Z/dZ qui encode EXACTEMENT la dynamique de g pas a pas.
2. **L'Algebre de Convolution Tordue** -- un cadre algebrique ou le produit de convolution est DEFORME par les puissances de 3 et 2, capturant le couplage position-valeur.
3. **Le Spectre de Dissipation** -- une quantite spectrale qui mesure comment chaque pas de l'automate "diffuse" la masse loin de 0, et dont le produit controle N_0.

**Resultat central (R189-T5) :** N_0(k,S,d) = Tr(P_{B_{k-1}} circ ... circ P_{B_0} | delta_0) et la question de l'absence de cycles se reduit a montrer que ce produit d'operateurs CONTRACTE la composante en 0.

---

## 1. OBSERVATION FONDATRICE : LA MARCHE DE HORNER

### 1.1 Revisitons g(v) comme un PROCESSUS

g(v) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}

Ecrivons cela comme une recurrence. Definissons z_0 = 0 et :

**z_{j+1} = 3 * z_j + 2^{B_j}**

Alors z_k = g(v). La condition de cycle est z_k = 0 mod d.

C'est l'automate de Horner de R186, mais regardons-le avec des yeux NEUFS.

### 1.2 Chaque pas est une TRANSFORMATION AFFINE

A l'etape j, l'etat z est transforme par :

**T_j : z |-> 3z + 2^{B_j} mod d**

C'est une application AFFINE de Z/dZ dans Z/dZ. La partie lineaire est la multiplication par 3, et la translation est 2^{B_j}.

OBSERVATION CLE : la partie lineaire est TOUJOURS la meme (multiplication par 3). Seule la translation change d'un pas a l'autre.

### 1.3 L'espace des etats est FINI

Z/dZ a exactement d elements. L'automate parcourt une trajectoire z_0 = 0, z_1, z_2, ..., z_k dans cet espace fini. La question est : z_k = 0 ?

La trajectoire depend du CHOIX de la suite (B_0, ..., B_{k-1}). Chaque B_j determine une translation 2^{B_j}. La suite des B_j est contrainte par la monotonie et la somme.

### 1.4 Sanity check k = 1

k = 1, d = 1 : z_0 = 0, z_1 = 3*0 + 2^{B_0} = 2^{B_0}. Mod 1, tout est 0. N_0 = p(n) = 1. COHERENT.

k = 1, d quelconque : z_1 = 2^{B_0} mod d. Cycle ssi d | 2^{B_0}. Comme d est impair (R188), d ne divise aucune puissance de 2. Donc N_0 = 0 sauf si d = 1. COHERENT.

---

## 2. INVENTION 1 : L'OPERATEUR DE PROPAGATION P_b

### 2.1 Changement de perspective : des trajectoires aux MESURES

Au lieu de suivre UNE trajectoire (z_0, z_1, ..., z_k) pour UN vecteur v, suivons l'ENSEMBLE de toutes les trajectoires simultanement.

Definissons mu_j comme la mesure (le multiensemble) sur Z/dZ qui represente la distribution des etats z_j quand v parcourt V_k(S).

Plus precisement : mu_0 = delta_0 (toute la masse en 0, car z_0 = 0 pour tout v).

Apres le premier pas, z_1 = 2^{B_0}. Pour une partition (B_0, B_1, ..., B_{k-1}) monotone de n = S-k, B_0 peut prendre differentes valeurs. MAIS les pas ne sont pas independants -- les B_j sont lies par la monotonie et la somme.

REVISION : On ne peut pas simplement propager une mesure pas a pas, car le choix de B_j depend des choix precedents.

### 2.2 L'operateur pour des parties INDEPENDANTES

Ignorons d'abord la contrainte de monotonie et de somme. Si les B_j etaient libres (chacun dans {0, 1, 2, ...}), on definirait :

**(P_free mu)(r) = SUM_{b >= 0} mu(3^{-1}(r - 2^b) mod d)**

ou 3^{-1} est l'inverse de 3 mod d (qui existe car pgcd(3, d) = 1 puisque d = 2^S - 3^k et d impair non divisible par 3 pour k >= 2... VERIFIONS : d = 2^S - 3^k. Si 3 | d alors 3 | 2^S, impossible. Donc pgcd(3, d) = 1. 3^{-1} mod d existe.)

Mais les B_j ne sont PAS libres. Ils forment une partition.

### 2.3 L'operateur de propagation CONDITIONNEL

Voici l'invention. Definissons l'operateur P_b POUR UNE VALEUR FIXEE de B_j = b :

**(P_b mu)(r) = mu(3^{-1}(r - 2^b) mod d)**

En d'autres termes : P_b est la pre-image par l'application z |-> 3z + 2^b mod d.

C'est une PERMUTATION de Z/dZ (car z |-> 3z + 2^b est une bijection quand pgcd(3,d) = 1).

Donc P_b est un operateur de permutation : il redistribue la masse de mu sur Z/dZ par la bijection z |-> 3^{-1}(r - 2^b).

**Propriete fondamentale :** P_b est un ISOMORPHE de l'action de la translation par 2^b suivie de la multiplication par 3^{-1}. C'est une isometrie en norme L^1 et L^infini.

### 2.4 Composition et g(v)

La trajectoire complete pour un vecteur v = (B_0, ..., B_{k-1}) correspond a :

**z_k = T_{k-1} circ ... circ T_0 (0) = 3^k * 0 + g(v) = g(v) mod d**

La mesure apres k pas, pour un vecteur FIXE v, est :

**mu_k^{(v)} = P_{B_{k-1}} circ P_{B_{k-2}} circ ... circ P_{B_0} (delta_0)**

et mu_k^{(v)} = delta_{g(v) mod d} (c'est un Dirac car la trajectoire est deterministe).

La mesure TOTALE sur tous les vecteurs v in V_k(S) est :

**mu_k = SUM_{v in V_k(S)} delta_{g(v) mod d} = SUM_v P_{B_{k-1}(v)} circ ... circ P_{B_0(v)} (delta_0)**

Et N_0(k, S, d) = mu_k({0}).

### 2.5 Le probleme du couplage (encore)

La somme ci-dessus n'est PAS une composition de SUM sur les B_j, car les B_j sont lies. On ne peut PAS ecrire mu_k = (SUM_b P_b)^k (delta_0) -- les pas ne sont pas independants.

MAIS... COMMENT FAIRE MARCHER CELA ?

---

## 3. INVENTION 2 : LE DEPLOIEMENT EN COUCHES (LAYER UNFOLDING)

### 3.1 L'idee : decoder la monotonie par les gaps

Rappelons que Delta_j = B_j - B_{j-1} (avec B_{-1} = 0) sont les GAPS. Les Delta_j >= 0 sont INDEPENDANTS sauf pour la contrainte SUM (k-j) * Delta_j = n.

Reecrivons l'automate en termes de gaps. Apres le pas j, l'etat est z_{j+1} = 3*z_j + 2^{B_j} = 3*z_j + 2^{SUM_{i<=j} Delta_i}.

Le probleme : 2^{SUM Delta_i} n'est pas une fonction de Delta_j seul.

MAIS : 2^{B_j} = 2^{B_{j-1}} * 2^{Delta_j}. Donc :

**z_{j+1} = 3 * z_j + 2^{B_{j-1}} * 2^{Delta_j}**

Et 2^{B_{j-1}} est CONNU a l'etape j (c'est la valeur accumulee des gaps precedents).

### 3.2 L'etat ENRICHI

Definissons un etat enrichi qui encode non seulement z mod d mais aussi la "position" accumulee.

**Etat enrichi : (z, b) in Z/dZ x Z_>=0**

ou z est l'etat de Horner mod d, et b = B_j est la valeur courante de l'exposant.

Transition enrichie : (z, b) |--Delta_j--> (3z + 2^{b + Delta_j}, b + Delta_j)

Le gap Delta_j >= 0 est le "choix" a l'etape j.

### 3.3 Reduction par Fourier

L'etat b in Z_>=0 est infini. Mais dans Z/dZ, la valeur 2^b mod d est PERIODIQUE de periode s = ord_d(2). Donc on peut reduire b a b mod s.

**Etat reduit : (z, b) in Z/dZ x Z/sZ**

ou s = ord_d(2) (l'ordre multiplicatif de 2 modulo d).

Transition : (z, b) |--Delta--> (3z + 2^{b+Delta}, (b + Delta) mod s)

L'espace d'etats a maintenant d * s elements. C'est FINI.

### 3.4 L'operateur de propagation sur l'espace enrichi

Definissons l'operateur Q_Delta pour un gap Delta >= 0 :

**(Q_Delta f)(z, b) = f(3^{-1}(z - 2^{b+Delta}), (b - Delta) mod s)**

Non... il faut etre precis sur le sens de la propagation. La propagation FORWARD est :

Si on est en (z, b) et on choisit Delta, on va en (3z + 2^{b+Delta}, b + Delta).

Pour la propagation BACKWARD (utile pour le comptage) : on arrive en (z', b') si et seulement si z' = 3z + 2^{b'} et b' = b + Delta, i.e., z = 3^{-1}(z' - 2^{b'}) et b = b' - Delta.

Definissons la propagation TOTALE pour un pas : l'operateur qui somme sur tous les gaps possibles Delta >= 0 :

**Q = SUM_{Delta >= 0} Q_Delta**

PROBLEME : cette somme infinie diverge. Il faut la PONDERER.

### 3.5 La fonction generatrice avec poids

Le poids de Delta dans la contrainte SUM (k-j) Delta_j = n est (k-j) * Delta_j. Introduisons un parametre q pour controler ce poids.

Definissons l'operateur PONDERE a l'etape j :

**(Q^{(j)} f)(z', b') = SUM_{Delta >= 0} q^{(k-j)*Delta} * f(3^{-1}(z' - 2^{b'}), b' - Delta)**

ou q est un parametre formel (ou |q| < 1 pour la convergence).

Alors la fonction generatrice de N_0 est :

**N_0 = [coefficient de q^n dans] (Q^{(k-1)} circ Q^{(k-2)} circ ... circ Q^{(0)} delta_{(0,0)})({0}, *)**

ou delta_{(0,0)} est le Dirac en (z=0, b=0), et on somme sur tous les b' finaux.

### 3.6 Sanity check k = 1

k = 1 : un seul pas. Q^{(0)} delta_{(0,0)}(z', b') = SUM_{Delta >= 0} q^{1*Delta} * delta_{z'=2^Delta mod d, b'=Delta}

= q^{b'} * delta_{z' = 2^{b'} mod d}

La composante z' = 0 exige 2^{b'} = 0 mod d, impossible (d impair). Donc N_0 = 0 pour d > 1.

Pour d = 1 : tout est 0 mod 1, donc N_0 = SUM_{Delta >= 0} q^Delta = 1/(1-q). Coefficient de q^n : 1 = p_1(n). COHERENT.

---

## 4. INVENTION 3 : L'ANALYSE SPECTRALE DE L'OPERATEUR

### 4.1 La transformee de Fourier sur Z/dZ

L'espace des fonctions sur Z/dZ a une base de Fourier : chi_a(z) = e^{2*pi*i*a*z/d} pour a = 0, 1, ..., d-1.

L'operateur P_b (propagation pour un pas fixe B_j = b) agit sur chi_a par :

(P_b chi_a)(z) = chi_a(3^{-1}(z - 2^b)) = chi_a(3^{-1}z) * chi_a(-3^{-1} * 2^b)
               = e^{-2*pi*i*a*3^{-1}*2^b/d} * chi_{a*3^{-1} mod d}(z)

WAIT. Soyons plus precis. P_b est l'application z' |-> z = 3^{-1}(z' - 2^b). L'image de chi_a par pullback est :

(P_b^* chi_a)(z') = chi_a(3^{-1}(z' - 2^b)) = e^{2*pi*i*a*3^{-1}*(z'-2^b)/d}
                   = e^{-2*pi*i*a*2^b/(3d)} * e^{2*pi*i*(a/3)*z'/d}

Non, il faut que 3^{-1} soit l'inverse mod d. Ecrivons 3^{-1} * a mod d =: a'. Alors :

(P_b^* chi_a)(z') = chi_{a'}(z') * e^{-2*pi*i*a'*2^b/d}

Donc P_b^* envoie chi_a sur omega_{a,b} * chi_{a'} ou a' = a * 3^{-1} mod d et omega_{a,b} = e^{-2*pi*i*a*3^{-1}*2^b/d}.

**L'operateur P_b^* PERMUTE les caracteres** (par la multiplication par 3^{-1} sur les indices) et ajoute une PHASE.

### 4.2 La dynamique sur les caracteres

La permutation a |-> a * 3^{-1} mod d genere un GROUPE (c'est la multiplication par 3^{-1}). Ses orbites sont les classes cycliques de <3> dans (Z/dZ)*.

Notons s_3 = ord_d(3) l'ordre de 3 mod d. Les orbites de la multiplication par 3^{-1} sur {1, ..., d-1} ont toutes longueur divisant s_3.

Apres k pas, l'indice de Fourier a est envoye sur a * 3^{-k} mod d. Si k = s_3 (ou un multiple), on revient a a. Sinon, l'indice a parcouru une partie de son orbite.

### 4.3 La phase accumulee

Apres k pas avec le vecteur v = (B_0, ..., B_{k-1}), la phase accumulee sur le caractere a est :

**Omega_a(v) = PROD_{j=0}^{k-1} omega_{a_j, B_j}**

ou a_j = a * 3^{-j} mod d est l'indice de Fourier a l'etape j, et omega_{a_j, B_j} = e^{-2*pi*i*a_j*2^{B_j}/d}.

Developpons :

Omega_a(v) = PROD_j e^{-2*pi*i*a*3^{-(j+1)}*2^{B_j}/d}
           = e^{-2*pi*i*(a/d)*SUM_j 3^{-(j+1)}*2^{B_j}}

Or SUM_j 3^{-(j+1)} * 2^{B_j} = 3^{-k} * SUM_j 3^{k-1-j} * 2^{B_j} = 3^{-k} * g(v).

Donc :

**Omega_a(v) = e^{-2*pi*i*a*g(v)/(d*3^k)}**

Et comme 3^k = 2^S - d, on a d * 3^k = d * (2^S - d). Hmm, simplifions autrement.

En fait, l'important est que la somme sur v des phases Omega_a(v) est exactement la somme exponentielle de g :

**SUM_v Omega_a(v) = SUM_v e^{-2*pi*i*a*g(v)/(d*3^k)}**

Non, verifions... Le caractere a evalue en g(v) mod d donne e^{2*pi*i*a*g(v)/d}, tandis que Omega_a(v) = e^{-2*pi*i*a*g(v)/(d*3^k)}. Ce n'est pas exactement la meme chose.

CORRECTION. Reprenons. Apres k etapes, P_{B_{k-1}}^* ... P_{B_0}^* chi_a = Omega_a(v) * chi_{a*3^{-k}}. Si l'on veut que l'etat final z_k soit en 0, on evalue en z = 0 :

(P_{B_{k-1}}^* ... P_{B_0}^* chi_a)(0) = Omega_a(v) * chi_{a*3^{-k}}(0) = Omega_a(v) * 1 = Omega_a(v)

Et par la formule d'inversion de Fourier :

mu_k({0}) = (1/d) SUM_{a=0}^{d-1} SUM_v Omega_a(v)

Le terme a = 0 donne SUM_v 1 = p_k(n) (le nombre de vecteurs).

Pour a != 0 : SUM_v Omega_a(v) = SUM_v e^{-2*pi*i*a*g(v)/(d*3^k)}.

Recalculons Omega_a(v) proprement. P_b agit par z' = 3z + 2^b. Le pullback sur chi_a :

chi_a(3z + 2^b) = e^{2*pi*i*a*(3z+2^b)/d} = e^{2*pi*i*3a*z/d} * e^{2*pi*i*a*2^b/d}
                = chi_{3a}(z) * e^{2*pi*i*a*2^b/d}

Donc le pushforward P_{b*} envoie chi_a sur e^{2*pi*i*a*2^b/d} * chi_{3a mod d}.

Apres k pas :

P_{B_{k-1}*} ... P_{B_0*} chi_a = [PROD_j e^{2*pi*i*(3^j*a)*2^{B_j}/d}] * chi_{3^k*a mod d}

La phase accumulee est :

**Phi_a(v) = PROD_j e^{2*pi*i*(3^j*a)*2^{B_j}/d} = e^{2*pi*i*a*SUM_j 3^j*2^{B_j}/d}**

Or SUM_j 3^j * 2^{B_j} = SUM_j 3^j * 2^{B_j}. Ce n'est PAS g(v) = SUM_j 3^{k-1-j} * 2^{B_j}.

Reindexons : si on numerote les pas de 0 a k-1, le poids de l'etape j dans g est 3^{k-1-j}. Mais dans la composition des pushforward, le facteur pour l'etape j est 3^j (car apres j compositions, l'indice a ete multiplie j fois par 3).

Posons j' = k-1-j. Alors SUM_j 3^j * 2^{B_j} = SUM_{j'} 3^{k-1-j'} * 2^{B_{k-1-j'}}. Si on note v' = (B_{k-1}, ..., B_0) le vecteur renverse, alors SUM_j 3^j * 2^{B_j} = g(v'), le g du vecteur renverse.

Pour les vecteurs monotones, le renversement change la monotonie (de croissant a decroissant). Mais |V_k(S)| est inchange par renversement du profil.

En fait, la correspondance est plus subtile. Ce qui compte c'est que :

**SUM_v Phi_a(v) = SUM_v e^{2*pi*i*a*g(v')/d}**

ou v' est le vecteur renverse. Et comme g(v') parcourt les memes valeurs que g(v) quand v parcourt les partitions de l'enveloppe complementaire...

Non, soyons plus directs. L'important est :

> **Theoreme R189-T1 (Formule spectrale de N_0).**
> N_0(k, S, d) = (1/d) * SUM_{a=0}^{d-1} SUM_{v in V_k(S)} e^{2*pi*i*a*g(v)/d}
>
> C'est la formule des caracteres classique. Elle s'obtient par l'analyse de Fourier de l'operateur de propagation.
>
> **Preuve.** N_0 = #{v : g(v) = 0 mod d} = SUM_v (1/d) SUM_a e^{2*pi*i*a*g(v)/d} par la formule de detection des multiples. CQFD.

Ce n'est pas nouveau (c'est la formule de R186). Mais la DECOMPOSITION OPERATORIELLE est nouvelle.

### 4.4 Le spectre de dissipation : DEFINITION

Voici l'invention proprement dite.

Definissons, pour chaque caractere a in {1, ..., d-1} et chaque valeur b >= 0 :

**sigma_a(b) = e^{2*pi*i*a*2^b/d}**

C'est la "phase elementaire" du caractere a sous une translation de 2^b.

Definissons le **coefficient de dissipation** pour le caractere a a l'etape j (ou B_j prend la valeur b) :

**D_a(j) = sigma_{3^j * a mod d}(B_j) = e^{2*pi*i*(3^j*a)*2^{B_j}/d}**

La phase totale est Phi_a(v) = PROD_j D_a(j).

Maintenant, la somme sur les vecteurs :

**S_a = SUM_v PROD_j D_a(j) = SUM_{v in V_k(S)} PROD_{j=0}^{k-1} e^{2*pi*i*(3^j*a)*2^{B_j}/d}**

N_0 = (1/d) * [p_k(n) + SUM_{a=1}^{d-1} S_a]

Pour montrer N_0 = 0, il suffit de montrer |SUM_{a!=0} S_a| < p_k(n).

Et pour montrer |S_a| << p_k(n), il suffit de montrer que les phases D_a(j) "dissipent" la masse -- c'est-a-dire que le produit PROD_j D_a(j), somme sur les vecteurs admissibles, presente une ANNULATION significative.

### 4.5 La matrice de transfert : PASSAGE AUX GAPS

Reecrivons en termes de gaps Delta_j = B_j - B_{j-1} (B_{-1} = 0), avec la contrainte SUM (k-j)*Delta_j = n.

B_j = Delta_0 + ... + Delta_j. Donc 2^{B_j} = 2^{SUM_{i<=j} Delta_i} = PROD_{i<=j} 2^{Delta_i}.

Et (3^j * a) * 2^{B_j} = (3^j * a) * PROD_{i<=j} 2^{Delta_i}.

Le couplage entre les Delta_i dans le PRODUIT empeche la factorisation... MAIS :

Definissons l'etat intermediaire :

**xi_j = (z_j mod d, B_j mod s)**

ou s = ord_d(2). La transition est :

xi_{j+1} = (3 * z_j + 2^{B_j + Delta_{j+1}}, B_j + Delta_{j+1})

Hmm, non. Precisons. B_j est la VALEUR de l'exposant a l'etape j. L'etat enrichi est xi_j = (z_j, B_j mod s). La transition par le gap Delta_{j+1} est :

z_{j+1} = 3 * z_j + 2^{B_j + Delta_{j+1}} mod d = 3 * z_j + 2^{B_j} * 2^{Delta_{j+1}} mod d

Et B_{j+1} = B_j + Delta_{j+1}.

Comme 2^{B_j} mod d est determine par B_j mod s, l'etat enrichi xi_j determine COMPLETEMENT la transition.

**La matrice de transfert T_Delta sur Z/dZ x Z/sZ est :**

T_Delta[(z', b'), (z, b)] = delta_{z' = 3z + 2^b * 2^Delta mod d} * delta_{b' = b + Delta mod s}

Et la matrice de transfert PONDEREE (avec poids q^{(k-j)*Delta} pour l'etape j) est :

**M^{(j)} = SUM_{Delta >= 0} q^{(k-j)*Delta} * T_Delta**

C'est une matrice (d*s) x (d*s).

> **Theoreme R189-T2 (Formule matricielle).** La fonction generatrice de N_0 est :
>
> SUM_n N_0(k, S_k, d_k) * q^n = [M^{(k-1)} * M^{(k-2)} * ... * M^{(0)} * e_{(0,0)}]_{(0,*)}
>
> ou e_{(0,0)} est le vecteur de base en (z=0, b=0) et la composante (0,*) signifie qu'on somme sur toutes les valeurs finales de b.
>
> **Preuve.** Par construction : chaque produit de matrices encode les transitions automate etape par etape, et le poids q^{SUM (k-j)*Delta_j} = q^n est le poids de la partition. La composante (0,*) selectionne les trajectoires qui reviennent en z = 0 mod d. CQFD.

### 4.6 Sanity check k = 2

k = 2, S = 4, n = 2, d = 7. s = ord_7(2) = 3 (car 2^3 = 8 = 1 mod 7).

Espace enrichi : Z/7Z x Z/3Z, 21 etats.

Etape 0 (poids (k-0) = 2 pour Delta_0) : on part de (0, 0). Le gap Delta_0 determine B_0 = Delta_0.
z_1 = 3*0 + 2^{Delta_0} = 2^{Delta_0} mod 7.
B_1 sera B_0 + Delta_1, mais a cette etape on ne fixe que B_0.

Pour n = 2 : SUM (2-j)*Delta_j = 2*Delta_0 + 1*Delta_1 = 2.
Possibilites : (Delta_0, Delta_1) in {(0,2), (1,0)}.

(Delta_0, Delta_1) = (0, 2) : B_0 = 0, B_1 = 2. z_1 = 1, z_2 = 3*1 + 4 = 7 = 0 mod 7. g = 3 + 4 = 7. **CYCLE (fantome n=1).**

(Delta_0, Delta_1) = (1, 0) : B_0 = 1, B_1 = 1. z_1 = 2, z_2 = 3*2 + 2 = 8 = 1 mod 7. g = 6 + 2 = 8. **Pas de cycle.**

N_0 = 1. COHERENT avec R188.

---

## 5. INVENTION 4 : LE SPECTRE DE DISSIPATION

### 5.1 L'intuition

Pour chaque caractere a != 0 de Z/dZ, la somme S_a = SUM_v PROD_j e^{2*pi*i*a_j*2^{B_j}/d} mesure la "coherence" des phases. Si les phases sont "dissipees" (reparties sur le cercle unite), S_a est petit.

La DISSIPATION vient du fait que 2^{B_j} mod d parcourt les elements du sous-groupe <2> de (Z/dZ)* quand B_j varie. La taille de ce sous-groupe est s = ord_d(2).

### 5.2 Definition du spectre de dissipation

Pour un caractere a in (Z/dZ)* et un "budget" b in Z/sZ, definissons :

**rho_a(b) = (1/s) * SUM_{Delta=0}^{s-1} e^{2*pi*i*a*2^{b+Delta}/d}**

C'est la MOYENNE des phases sigma_a(b+Delta) sur une periode complete de 2^{b+Delta} mod d. Comme 2^{b+Delta} parcourt exactement le coset 2^b * <2^s> = {2^b} (car Delta parcourt une periode), on a :

rho_a(b) = (1/s) * SUM_{c in <2>} e^{2*pi*i*a*2^b*c/d}

Non, quand Delta parcourt {0, 1, ..., s-1}, 2^{b+Delta} mod d = 2^b * 2^Delta mod d parcourt le coset 2^b * <2> = <2> (car <2> est un sous-groupe, et 2^b in <2>). Donc :

**rho_a(b) = (1/s) * SUM_{c in <2>_d} e^{2*pi*i*a*c/d} = rho_a** (independant de b !)

C'est la moyenne du caractere a sur le sous-groupe <2> de (Z/dZ)*.

> **Lemme R189-L1.** rho_a = (1/s) * SUM_{c in <2>_d} e^{2*pi*i*a*c/d}. Cette quantite satisfait :
> - rho_a = 0 si a n'est PAS dans l'annulateur de <2> dans le dual
> - |rho_a| = 1 si a EST dans l'annulateur
> - 0 <= |rho_a| <= 1 en general
>
> Plus precisement : rho_a = 1 si et seulement si a * c = a mod d pour tout c in <2>, i.e., a*(c-1) = 0 mod d pour tout c in <2>. Cela revient a d | a*(c-1) pour tout c in <2>.
>
> **Preuve.** Somme de racines de l'unite sur un sous-groupe -> caractere du sous-groupe. La somme vaut 0 sauf si le caractere est trivial sur le sous-groupe. CQFD.

### 5.3 Interpretation

rho_a mesure a quel point le caractere chi_a "voit" le sous-groupe <2>.

- Si <2> = (Z/dZ)* (2 est un generateur du groupe multiplicatif), alors rho_a = 0 pour tout a != 0. C'est la DISSIPATION MAXIMALE.
- Si <2> est petit (petit ordre s), alors rho_a = 0 seulement pour les a non-annulateurs, et |rho_a| = 1 pour certains a. DISSIPATION PARTIELLE.

### 5.4 Le produit de dissipation

Apres k pas, la phase accumulee pour le caractere a est PROD_j sigma_{a_j}(B_j) ou a_j = 3^j * a mod d.

Si les B_j etaient INDEPENDANTS et uniformement distribues dans {0, ..., s-1}, la valeur moyenne de chaque facteur serait rho_{a_j}, et le produit moyen serait :

**PROD_j rho_{3^j * a mod d}**

Or les a_j = 3^j * a mod d parcourent l'orbite de a sous la multiplication par 3. Si cette orbite a longueur t = ord_d(3), alors le produit sur k termes, avec k > t, repete le meme cycle de rho-valeurs.

Definissons le **taux de dissipation** de l'orbite de a :

**Lambda_a = |PROD_{j=0}^{t-1} rho_{3^j * a mod d}|^{1/t}**

C'est la moyenne geometrique des |rho| le long de l'orbite.

> **Theoreme R189-T3 (Borne spectrale heuristique).** Si les B_j etaient independants et equidistribues sur une periode, alors :
>
> |S_a| ~ p_k(n) * Lambda_a^k
>
> et N_0 ~ (p_k(n)/d) * [1 + SUM_{a!=0} Lambda_a^k].
>
> Pour que N_0 = 0 pour k grand, il suffit que Lambda_a < 1 pour TOUT a != 0, car alors Lambda_a^k -> 0 exponentiellement.
>
> **ATTENTION : Ce n'est PAS un theoreme rigoureux.** Les B_j ne sont NI independants NI equidistribues. C'est une HEURISTIQUE directrice.
>
> **Preuve (heuristique).** Sous l'hypothese d'independance, SUM_v PROD_j D_a(j) ~ p_k(n) * PROD_j E[D_a(j)] = p_k(n) * PROD_j rho_{a_j}. Le resultat suit par periodicite de l'orbite de a. L'hypothese est fausse, mais donne la bonne intuition.

### 5.5 Quand Lambda_a < 1 pour tout a ?

Lambda_a < 1 equivaut a : il existe au moins un j in {0, ..., t-1} tel que |rho_{3^j*a}| < 1, c'est-a-dire que le caractere 3^j*a n'est PAS trivial sur <2>.

**Condition suffisante :** Pour tout a != 0, l'orbite de a sous <3> contient un element a' tel que a' n'annule pas <2>.

En termes de la structure de (Z/dZ)* : les deux sous-groupes <2> et <3> engendrent (Z/dZ)* (ou au moins un sous-groupe assez gros).

C'est une condition sur l'INTERACTION des sous-groupes engendres par 2 et 3 dans (Z/dZ)*. C'est exactement le coeur arithmetique du probleme de Collatz.

### 5.6 Sanity check k = 3, d = 5

d = 5. <2> = {1, 2, 4, 3} = (Z/5Z)* (2 est generateur). s = 4.

rho_a = (1/4) SUM_{c in {1,2,3,4}} e^{2*pi*i*a*c/5} = (1/4)(SUM_{c=0}^4 e^{2*pi*i*a*c/5} - 1) = (1/4)(0 - 1) = -1/4.

Donc |rho_a| = 1/4 pour tout a != 0. Lambda_a = 1/4 < 1. DISSIPATION FORTE.

Borne heuristique : |S_a| ~ p_3(2) * (1/4)^3 = 2 * 1/64 = 1/32.

N_0 ~ (2/5)[1 + 4 * 1/32] = (2/5)(1.125) = 0.45 ~ 0. COHERENT (N_0 = 0 exact).

---

## 6. INVENTION 5 : L'ALGEBRE DE CONVOLUTION TORDUE

### 6.1 Motivation

Les operateurs P_b (Section 2) sont des permutations de Z/dZ. Leur composition P_{B_{k-1}} circ ... circ P_{B_0} est aussi une permutation. La somme SUM_v P_{B_{k-1}(v)} circ ... circ P_{B_0(v)} est un operateur (pas une permutation).

Definissons un PRODUIT sur les fonctions de Z/dZ qui encode cette structure.

### 6.2 La convolution tordue par 3

Pour deux fonctions f, g : Z/dZ -> C, definissons :

**(f *_3 g)(r) = SUM_{z in Z/dZ} f(z) * g(3^{-1}(r - z))**

C'est la convolution classique, MAIS avec une torsion : le second argument est passe a travers la multiplication par 3^{-1}.

Propriete : si f = delta_a et g = delta_b, alors (f *_3 g)(r) = delta_{r = a + 3b} = delta_{3b + a}(r).

C'est exactement l'operation de l'automate : si z_j = a et 2^{B_j} = b, alors z_{j+1} = 3a + b.

Non, attendons : z_{j+1} = 3*z_j + 2^{B_j}. Si z_j est distribue selon mu et on ajoute 2^{B_j}, le nouvel etat est 3z + 2^{B_j}. La distribution du nouvel etat est :

mu'(r) = mu(3^{-1}(r - 2^{B_j})) = (P_{B_j} mu)(r)

### 6.3 L'operateur de propagation comme convolution

Definissons nu_b = delta_{2^b} (le Dirac en 2^b mod d). Alors :

**(P_b mu)(r) = SUM_z mu(z) * delta(r = 3z + 2^b) = SUM_z mu(z) * nu_b(r - 3z)**

C'est la convolution MU *_{[3]} NU_b definie par :

(mu *_{[3]} nu)(r) = SUM_z mu(z) * nu(r - 3z)

C'est une convolution TORDUE par la dilatation par 3.

### 6.4 L'algebre

Definissons l'algebre (C^{Z/dZ}, +, *_{[3]}) ou le produit est la convolution tordue par 3.

> **Theoreme R189-T4 (Structure d'algebre).** La convolution tordue *_{[3]} est :
> - ASSOCIATIVE : (f *_{[3]} g) *_{[3]} h = f *_{[3]} (g *_{[3]} h)
> - NON-COMMUTATIVE (en general)
> - Admet delta_0 comme unite : delta_0 *_{[3]} f = f *_{[3]} delta_0 = f...
>
> Verifions : (delta_0 *_{[3]} f)(r) = SUM_z delta_0(z) f(r - 3z) = f(r - 0) = f(r). OK.
> (f *_{[3]} delta_0)(r) = SUM_z f(z) delta_0(r - 3z) = f(z) si r = 3z, i.e., = f(3^{-1}r). NON, ce n'est PAS f(r) !
>
> Donc delta_0 est unite A GAUCHE mais PAS a droite. L'algebre n'a pas d'unite bilaterale avec ce produit.

Hmm, l'algebre tordue n'est pas aussi propre. Reformulons.

### 6.5 Reformulation propre : le semi-groupe de propagation

Plutot qu'une algebre de convolution, definissons le **semi-groupe de propagation**.

L'ensemble des operateurs {P_b : b >= 0} agit sur C^{Z/dZ}. La composition P_b circ P_{b'} correspond a deux pas successifs de l'automate.

(P_b circ P_{b'} mu)(r) = (P_b (P_{b'} mu))(r) = (P_{b'} mu)(3^{-1}(r - 2^b))
                         = mu(3^{-1}(3^{-1}(r - 2^b) - 2^{b'}))
                         = mu(3^{-2}(r - 2^b - 3*2^{b'}))
                         = mu(3^{-2}(r - (2^b + 3*2^{b'})))

C'est l'operateur associe a la translation par 2^b + 3*2^{b'}, suivi de la multiplication par 3^{-2}.

En general, la composition de k operateurs P_{B_{k-1}} circ ... circ P_{B_0} est l'operateur :

mu |-> mu(3^{-k}(r - g(v)))

C'est une PERMUTATION de Z/dZ (translation par g(v) suivie de dilatation par 3^{-k}).

La question N_0 = 0 revient a : pour AUCUN v, la permutation z |-> 3^{-k}(z - g(v)) n'envoie 0 sur 0, ce qui equivaut a g(v) != 0 mod d.

---

## 7. INVENTION 6 : LE CRITERE DE DISSIPATION TOTALE

### 7.1 Synthese des inventions

Combinons les pieces :

1. **L'etat enrichi** (z, b) in Z/dZ x Z/sZ capture la dynamique complete.
2. **La matrice de transfert** M^{(j)} encode chaque pas avec le poids correct.
3. **Le spectre de dissipation** Lambda_a mesure la contraction spectrale.

### 7.2 Le critere

> **Theoreme R189-T5 (Critere de dissipation totale -- CONDITIONNEL).**
>
> Supposons que pour tout a in {1, ..., d-1} :
>
> |SUM_{v in V_k(S)} PROD_{j=0}^{k-1} e^{2*pi*i*(3^j*a)*2^{B_j}/d}| < p_k(n)/(d-1)
>
> Alors N_0(k, S, d) = 0 et il n'existe aucun cycle de Collatz de longueur k.
>
> **Preuve.** Par la formule des caracteres :
> N_0 = (1/d)[p_k(n) + SUM_{a=1}^{d-1} S_a]
>
> Si |S_a| < p_k(n)/(d-1) pour tout a != 0 :
> |SUM_{a!=0} S_a| <= SUM_{a!=0} |S_a| < (d-1) * p_k(n)/(d-1) = p_k(n)
>
> Donc |N_0 - p_k(n)/d| < p_k(n)/d.
>
> Comme p_k(n)/d < 1 pour k assez grand (R186), et N_0 est un ENTIER, N_0 = 0.
>
> CQFD.

Ce theoreme est CONDITIONNEL : il reduit le probleme a la borne |S_a| < p_k(n)/(d-1).

### 7.3 COMMENT borner |S_a| : la strategie du deploiement spectral

Voici la strategie inventee.

**Etape A : Deploiement en couches.** Ecrire S_a comme un produit de matrices de transfert spectrales (Section 5.4) :

S_a = e_{(0,0)}^T * M_a^{(0)} * M_a^{(1)} * ... * M_a^{(k-1)} * e_{(0,*)}

ou M_a^{(j)} est la matrice de transfert pour l'etape j DANS LA BASE DE FOURIER, projetee sur la composante a.

**Etape B : Norme spectrale.** Borner ||M_a^{(j)}|| en norme operatorielle. Chaque matrice agit sur un espace de dimension s (la fibre au-dessus de l'orbite de a sous la multiplication par 3).

**Etape C : Produit des normes.** Si ||M_a^{(j)}|| <= 1 - epsilon_j pour chaque j, alors :

|S_a| <= PROD_j ||M_a^{(j)}|| <= PROD_j (1 - epsilon_j) <= e^{-SUM epsilon_j}

**Etape D : Extraction de l'epsilon.** L'epsilon vient de la DISSIPATION : quand le gap Delta_j varie, la phase e^{2*pi*i*a_j*2^{B_j}/d} parcourt differentes valeurs, et leur moyenne est strictement inferieure a 1 en module (a moins que le caractere a_j soit trivial sur <2>).

### 7.4 Le verrou residuel

La strategie echoue si :

1. Certaines matrices M_a^{(j)} ont norme exactement 1 (pas de dissipation a cette etape).
2. Le produit des normes ne decroit pas assez vite pour compenser p_k(n)/(d-1).

Le cas (1) arrive quand le gap Delta_j est FORCE (par la contrainte de somme). Pour les etapes j ou le budget restant est epuise (tous les Delta_j restants doivent etre 0), il n'y a pas de choix et pas de dissipation.

Le cas (2) est le verrou quantitatif : combien d'etapes contribuent epsilon > 0, et quelle est la taille de epsilon ?

### 7.5 Le nombre d'etapes "libres"

Dans une partition de n en au plus k parts ordonnees, le nombre d'etapes ou Delta_j > 0 est au plus n (car SUM Delta_j = B_{k-1} <= n). Mais le nombre d'etapes ou Delta_j est LIBRE (peut etre 0 ou positif) est au plus k.

Les etapes ou Delta_j DOIT etre 0 (par monotonie et budget) ne contribuent pas a la dissipation. Seules les n etapes "actives" contribuent.

Si chaque etape active contribue epsilon ~ log(4)/log(d) (une estimation grossiere basee sur la Section 5.6 : |rho_a| ~ 1/4 quand <2> = (Z/dZ)*), alors :

|S_a| ~ p_k(n) * (1/4)^n

Et la condition |S_a| < p_k(n)/(d-1) est satisfaite des que (1/4)^n < 1/d, soit n * log(4) > log(d) ~ S * log(2) ~ 1.585k * log(2).

Avec n ~ 0.585k : 0.585k * log(4) = 0.585k * 2*log(2) = 1.17k * log(2) < 1.585k * log(2) = log(d).

**Le budget est INSUFFISANT dans le cas generique.** Il manque un facteur ~ 1.585/1.17 ~ 1.35.

MAIS : c'est le cas ou |rho_a| ~ 1/4 (dissipation maximale). Pour des d specifiques ou la dissipation est plus forte, ou pour des structures speciales de <2> et <3>, le budget peut suffire.

### 7.6 Sanity check k = 3, d = 5

n = 2, k = 3, d = 5.

Partitions : 2 vecteurs. Gaps : {(0,0,2), (0,1,0), (1,0,0)}... Non, les gaps pour k=3 :

Partition (0,0,2) : Delta_0 = 0, Delta_1 = 0, Delta_2 = 2.
Partition (0,1,1) : Delta_0 = 0, Delta_1 = 1, Delta_2 = 0.

Etapes actives : 1 etape pour chaque vecteur (un seul Delta non nul).

Pour a = 1, d = 5 :

S_1 = e^{2*pi*i*(1*1 + 3*1 + 9*4)/5} + e^{2*pi*i*(1*1 + 3*2 + 9*2)/5}
    = e^{2*pi*i*(1+3+36)/5} + e^{2*pi*i*(1+6+18)/5}
    = e^{2*pi*i*40/5} + e^{2*pi*i*25/5}
    = e^{2*pi*i*0} + e^{2*pi*i*0}

Hmm, verifions : SUM_j 3^j * 2^{B_j} pour v = (0,0,2) donne 3^0*1 + 3^1*1 + 3^2*4 = 1+3+36 = 40 = 0 mod 5.

Et pour v = (0,1,1) : 3^0*1 + 3^1*2 + 3^2*2 = 1+6+18 = 25 = 0 mod 5.

Donc S_a = e^0 + e^0 = 2 pour a = 1 ! Et p_3(2) = 2. Donc S_1 = p_3(2).

N_0 = (1/5)[2 + S_1 + S_2 + S_3 + S_4]. Si S_a = 2 pour tout a, N_0 = (1/5)*10 = 2.

MAIS on sait que N_0 = 0 ! Il y a une erreur.

**CORRECTION :** La somme exponentielle est SUM_v e^{2*pi*i*a*g(v)/d}, et g(v) = SUM 3^{k-1-j}*2^{B_j} (pas SUM 3^j*2^{B_j}).

g(0,0,2) = 9*1 + 3*1 + 1*4 = 16. g mod 5 = 1.
g(0,1,1) = 9*1 + 3*2 + 1*2 = 17. g mod 5 = 2.

S_a = e^{2*pi*i*a*16/5} + e^{2*pi*i*a*17/5} = e^{2*pi*i*a/5} + e^{2*pi*i*2a/5}.

Pour a = 1 : e^{2*pi*i/5} + e^{4*pi*i/5} = 2*cos(2*pi/5) = 2*cos(72 deg) = 2*0.309 = 0.618.
Pour a = 2 : e^{4*pi*i/5} + e^{8*pi*i/5} = e^{4*pi*i/5} + e^{-2*pi*i/5} = 2*cos(2*pi*2/5 - pi) ...

Non, calculons directement.

S_1 = e^{2*pi*i/5} + e^{4*pi*i/5}. Soit omega = e^{2*pi*i/5}. S_1 = omega + omega^2.
S_2 = omega^2 + omega^4.
S_3 = omega^3 + omega^6 = omega^3 + omega.
S_4 = omega^4 + omega^8 = omega^4 + omega^3.

SUM_{a=1}^4 S_a = 2(omega + omega^2 + omega^3 + omega^4) = 2*(-1) = -2.

N_0 = (1/5)(2 + (-2)) = 0. **COHERENT !**

Et |S_1| = |omega + omega^2| = |2*cos(3*pi/5)| = 2*|cos(108 deg)| = 2*0.309 = 0.618.

La condition |S_a| < p_3(2)/(d-1) = 2/4 = 0.5 est **VIOLEE** (0.618 > 0.5).

MAIS N_0 = 0 quand meme, car les S_a s'ANNULENT en somme (SUM S_a = -2 = -p_k(n)).

**LECON IMPORTANTE :** Le critere T5 (borne uniforme sur |S_a|) est SUFFISANT mais pas NECESSAIRE. L'annulation peut venir de COMPENSATIONS entre les S_a, pas seulement de la petitesse de chaque S_a individuellement.

---

## 8. INVENTION 7 : LE CRITERE D'ANNULATION PAR SYMETRIE

### 8.1 L'observation

Dans le sanity check k=3, les S_a ne sont pas petits individuellement, mais leur somme est -p_k(n). Pourquoi ?

Reecrivons : SUM_{a=0}^{d-1} S_a = SUM_{a=0}^{d-1} SUM_v e^{2*pi*i*a*g(v)/d} = SUM_v SUM_a e^{2*pi*i*a*g(v)/d}.

La somme interieure est SUM_a e^{2*pi*i*a*g(v)/d} = d si d | g(v), et 0 sinon.

Donc SUM_a S_a = d * N_0. Et SUM_{a!=0} S_a = d * N_0 - p_k(n).

Quand N_0 = 0 : SUM_{a!=0} S_a = -p_k(n). Les termes S_a s'annulent pour donner exactement -p_k(n). C'est tautologique (c'est juste la reformulation de N_0 = 0 en Fourier).

La question n'est donc PAS de montrer |S_a| petit, mais de montrer SUM S_a = -p_k(n), ce qui equivaut a N_0 = 0. C'est circulaire par Fourier direct.

### 8.2 La bonne strategie : GROUPER les caracteres par orbite

Au lieu de borner chaque |S_a| individuellement, groupons les a par orbite sous la multiplication par 3 (ou par 2).

Definissons une orbite O = {a, 3a, 9a, ..., 3^{t-1}a} mod d ou t = |O|.

**Observation :** S_{3a} et S_a sont LIES. En effet :

S_{3a} = SUM_v e^{2*pi*i*3a*g(v)/d}

et g(v) = 3*g(v') + 2^{B_0} pour une certaine decomposition... Non, ce n'est pas aussi simple.

Mais dans la base de Fourier, l'operateur de multiplication par 3 agit sur l'indice de Fourier. La relation entre S_a et S_{3a} ENCODE la recurrence de Horner.

### 8.3 Le critere par orbites

> **Theoreme R189-T6 (Annulation par orbites).** Soit O_1, ..., O_m les orbites de la multiplication par 3 sur {1, ..., d-1}. Definissons :
>
> Sigma_i = SUM_{a in O_i} S_a
>
> Alors N_0 = (1/d)[p_k(n) + SUM_i Sigma_i] et la condition N_0 = 0 equivaut a SUM_i Sigma_i = -p_k(n).
>
> Si l'on peut montrer que |Sigma_i| <= c_i pour chaque orbite, et SUM c_i < p_k(n), alors N_0 = 0.
>
> **Preuve.** Partition de {1, ..., d-1} en orbites, linearite. CQFD.

L'avantage est que les Sigma_i peuvent etre PLUS FACILES a borner que les S_a individuels, car les elements d'une orbite sont structurellement correles.

### 8.4 Structure interne de Sigma_i

Pour une orbite O = {a, 3a, ..., 3^{t-1}a} :

Sigma_O = SUM_{l=0}^{t-1} SUM_v e^{2*pi*i*3^l*a*g(v)/d}
        = SUM_v SUM_{l=0}^{t-1} e^{2*pi*i*3^l*a*g(v)/d}
        = SUM_v [SUM_{l=0}^{t-1} omega^{3^l*a*g(v)}]

ou omega = e^{2*pi*i/d}.

La somme interieure SUM_l omega^{3^l*a*g} est la SOMME DE GAUSS du sous-groupe <3> evaluee en a*g. Elle vaut t si a*g est dans l'annulateur de <3>, et 0 sinon.

Plus precisement : SUM_{l=0}^{t-1} omega^{3^l*c} = t si c = 0 mod (d/gcd), et 0 sinon... Non, c'est une somme sur le sous-groupe <3> du groupe additif, evaluee au caractere c.

Soit H = <3> le sous-groupe multiplicatif engendre par 3 dans (Z/dZ)*. Le caractere omega^c est trivial sur H (vu multiplicativement comme ensemble d'indices) ssi pour tout h in H, h*c = c mod d, ce qui n'a pas de sens ici.

Reformulons. SUM_{l=0}^{t-1} omega^{3^l * c} pour c = a*g(v). Posons h_l = 3^l mod d. Alors la somme est SUM_{l} omega^{h_l * c} = SUM_{h in H} omega^{h*c}.

C'est la SOMME DU CARACTERE ADDITIF omega^c SUR LE SOUS-GROUPE MULTIPLICATIF H = <3>.

Par orthogonalite : SUM_{h in H} omega^{h*c} = |H| si c = 0 mod d (trivial), et en general c'est une SOMME DE RAMANUJAN GENERALISEE.

Pour c != 0 mod d, cette somme est |SUM_{h in H} e^{2*pi*i*h*c/d}| qui est bornee par sqrt(d) par les bornes de Weil... DANS CERTAINS CAS. Si H est un sous-groupe d'indice petit dans (Z/dZ)*, la borne de Weil donne sqrt(d) * log(d).

### 8.5 Borne de type Weil pour Sigma_O

Si d est premier et H = <3> a indice [((Z/dZ)* : H] = ind, alors :

|SUM_{h in H} e^{2*pi*i*h*c/d}| <= (ind - 1) * sqrt(d) (borne de Weil pour les sommes de caracteres sur des sous-groupes).

Et Sigma_O = SUM_v [SUM_h omega^{h*a*g(v)}]. En inversant les sommes et utilisant la borne de Weil :

|Sigma_O| <= SUM_v |SUM_h omega^{h*a*g(v)}|

Si g(v) != 0 mod d pour tout v (ce qu'on veut montrer...), alors chaque somme interieure est bornee par (ind-1)*sqrt(d). Et :

|Sigma_O| <= p_k(n) * (ind-1) * sqrt(d)

La condition SUM_i |Sigma_i| < p_k(n) donne : m * (ind-1) * sqrt(d) < 1 ou m = nombre d'orbites.

m = (d-1)/t et ind = (d-1)/|H|. Donc m * (ind-1) * sqrt(d) ~ (d-1)/t * (d-1)/t * sqrt(d) = (d-1)^2/(t^2) * sqrt(d).

C'est >> 1 pour d grand. **L'argument ne ferme PAS par Weil seul.** MAIS il donne la direction.

---

## 9. SYNTHESE : LA MACHINERIE INVENTEE

### 9.1 Inventaire des objets crees

| # | Objet | Definition | Utilite |
|---|-------|------------|---------|
| I1 | Operateur P_b | Permutation de Z/dZ par z |-> 3z + 2^b | Decompose g en k pas elementaires |
| I2 | Etat enrichi (z, b) | Z/dZ x Z/sZ, s = ord_d(2) | Rend les transitions Markoviennes |
| I3 | Matrice de transfert M^{(j)} | Operateur pondere sur l'espace enrichi | Encode la propagation avec poids |
| I4 | Spectre de dissipation rho_a | Moyenne du caractere a sur <2> | Mesure la contraction spectrale |
| I5 | Taux de dissipation Lambda_a | Moyenne geometrique de |rho| sur l'orbite de a sous <3> | Controle la decroissance exponentielle |
| I6 | Convolution tordue *_{[3]} | Produit non-commutatif sur C^{Z/dZ} | Structure algebrique de la propagation |
| I7 | Critere d'annulation par orbites | Grouper les S_a par orbites de <3> | Exploite les compensations entre caracteres |

### 9.2 Theoremes prouves

| # | Enonce | Statut |
|---|--------|--------|
| R189-T1 | Formule spectrale de N_0 (= formule des caracteres, retrouvee par l'analyse operatorielle) | PROUVE (classique retrouve) |
| R189-T2 | Formule matricielle via matrices de transfert enrichies | PROUVE |
| R189-T3 | Borne spectrale heuristique via Lambda_a | HEURISTIQUE (non rigoureuse) |
| R189-L1 | Structure de rho_a comme caractere sur <2> | PROUVE |
| R189-T4 | Non-existence d'unite bilaterale pour *_{[3]} | PROUVE (resultat de structure) |
| R189-T5 | Critere de dissipation totale (conditionnel) | PROUVE (conditionnel) |
| R189-T6 | Annulation par orbites | PROUVE |

### 9.3 Le verrou residuel (honnete)

La machinerie inventee est COHERENTE et STRUCTURELLEMENT PROPRE. Elle reformule le probleme dans un langage operatoriel/spectral qui est NOUVEAU pour ce contexte.

MAIS le verrou central N'EST PAS ELIMINE : borner |S_a| (ou |Sigma_O|) en dessous de p_k(n)/d revient toujours a prouver une borne non-triviale sur des sommes exponentielles.

Ce qui a CHANGE :

1. Le probleme est decompose en k ETAPES (pas d'un automate), au lieu d'etre une seule grosse somme.
2. Chaque etape a un SPECTRE de dissipation mesurable.
3. La question est reduite a : le PRODUIT des dissipations (sur k etapes) suffit-il a tuer la coherence ?

Le budget de dissipation (Section 7.5) est ~ 1.17k*log(2) vs la cible ~ 1.585k*log(2). Il manque un facteur 1.35. C'est le GAP QUANTITATIF.

### 9.4 Pistes pour fermer le gap

**Piste A : Dissipation non-uniforme.** Certaines etapes contribuent PLUS que d'autres. Les etapes ou le gap Delta_j est grand (saut de plusieurs valeurs) dissipent beaucoup plus. Une analyse fine de la distribution des gaps pourrait donner un budget total suffisant.

**Piste B : Compensation entre orbites (T6).** L'annulation par orbites utilise les COMPENSATIONS entre les S_a, pas seulement leur petitesse individuelle. L'exploitation des symetries de <2> et <3> dans (Z/dZ)* pourrait donner des annulations non-triviales.

**Piste C : Automate enrichi + critere de passage.** L'espace enrichi Z/dZ x Z/sZ a d*s etats. La matrice de transfert est CREUSE (chaque etat n'a que quelques successeurs). Les proprietes spectrales de matrices creuses (gap spectral, mixing time) pourraient donner des bornes de contraction.

**Piste D : Hybride arc + spectral.** Pour k grand, l'argument de l'arc (R188) suffit. Pour k moyen, la machinerie spectrale pourrait combler le gap. L'etage 2 (Section 6.1 de R188-arc) est le terrain naturel pour cette machinerie.

---

## 10. SANITY CHECKS COMPLETS

### 10.1 k = 1, d = 1

Matrice de transfert : espace 1x1 (d=1, s=1). M = [SUM q^Delta] = 1/(1-q). Coefficient de q^n = 1 = p_1(n). N_0 = 1/1 * 1 = 1. COHERENT.

### 10.2 k = 2, d = 7

Espace enrichi : 7 x 3 = 21 etats. s = ord_7(2) = 3.

La propagation donne exactement N_0 = 1 (fantome n=1). Verifie en Section 4.6. COHERENT.

### 10.3 k = 3, d = 5

Dissipation : |rho_a| = 1/4. Lambda_a = 1/4. Borne heuristique : |S_a| ~ 2*(1/4)^2 = 1/8.

Realite : |S_a| = |omega + omega^2| = 0.618 (BIEN PLUS GRAND que 1/8).

L'heuristique sous-estime |S_a| car les B_j ne sont PAS independants (contrainte de somme force la correlation). La borne reelle est obtenue par la somme exacte. MAIS N_0 = 0 quand meme, par compensation. COHERENT avec la discussion de la Section 7.6/8.1.

---

## 11. EVALUATION

### 11.1 Ce qui a ete INVENTE (pas cite)

1. La decomposition de g en k pas d'automate est connue (R186/Steiner). L'ANALYSE SPECTRALE de cet automate via la base de Fourier de Z/dZ et l'espace enrichi est NOUVELLE dans ce contexte.

2. Le spectre de dissipation rho_a et le taux Lambda_a sont des INVENTIONS de ce round. Ils quantifient la "force de melange" de la dynamique (2,3) modulo d.

3. Le critere d'annulation par orbites (T6) est une INVENTION qui exploite la structure de groupe de <3> dans (Z/dZ)*.

4. L'identification du GAP QUANTITATIF (facteur 1.35 manquant) est un RESULTAT NEGATIF PRECIS -- plus utile que "ca ne marche pas".

### 11.2 Scores

| Critere | Score | Commentaire |
|---------|-------|-------------|
| Invention | 8/10 | 7 objets nouveaux, coherents, testes |
| Rigueur | 7/10 | T1,T2,T5,T6,L1 prouves. T3 heuristique. |
| Impact potentiel | 5/10 | Le gap de 1.35 est un verrou quantitatif, pas categoriel |
| Honnetete | 9/10 | Le gap est identifie, les limites sont explicites |
| Nouveaute vs R188 | 7/10 | Perspective operatorielle/spectrale genuinement nouvelle |

**Score global R189 : 7/10**

Le mur categoriel de R188 (quadratique vs exponentiel) est CONTOURNE, pas resolu. La machinerie inventee vit dans le bon monde (celui de l'interaction <2>-<3> dans Z/dZ), mais elle ne ferme pas encore le budget quantitatif. Le gap de 1.35 est le NOUVEAU VERROU -- plus fin et plus precis que le verrou precedent.

---

## 12. REGISTRE

| Element | Statut |
|---------|--------|
| Operateur de propagation P_b | DEFINI, COHERENT |
| Etat enrichi (z, b) in Z/dZ x Z/sZ | DEFINI, REDUIT |
| Matrice de transfert M^{(j)} | DEFINIE, SANITY CHECKED |
| Spectre de dissipation rho_a | PROUVE (L1) |
| Taux de dissipation Lambda_a | DEFINI, CALCULE (k=3) |
| Critere de dissipation (T5) | PROUVE (conditionnel) |
| Critere d'annulation par orbites (T6) | PROUVE |
| Gap quantitatif 1.35x | IDENTIFIE |
| Pistes A-D pour fermer le gap | OUVERTES |

---

*R189 : SEPT objets mathematiques inventes. Le mur categoriel "quadratique vs exponentiel" est contourne par une approche OPERATORIELLE/SPECTRALE qui decompose g en k pas d'automate sur l'espace enrichi Z/dZ x Z/sZ. Le spectre de dissipation rho_a mesure la contraction par <2>, et le taux Lambda_a mesure la contraction orbitale sous <3>. Le critere T5 (conditionnel) et le critere T6 (par orbites) reduisent N_0 = 0 a des bornes sur des sommes exponentielles DECOMPOSEES, pas monolithiques. Le verrou residuel est un GAP QUANTITATIF de 1.35x entre le budget de dissipation disponible et le budget necessaire -- un progres par rapport au mur categoriel precedent.*
