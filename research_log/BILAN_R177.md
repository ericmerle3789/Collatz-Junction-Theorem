# BILAN R177 — PREUVE CAS x=2 (ÉLÉMENTAIRE)
**Date :** 15 mars 2026

---

## RÉSUMÉ EXÉCUTIF

R177 fournit la première preuve COMPLÈTE pour une valeur de x : **pour x=2, N₀(d) = 0 pour tout S ≥ 3.**

La preuve est entièrement élémentaire — un argument de taille en 3 lignes.

---

## THÉORÈME (T180)

**Énoncé :** Pour x = 2, N₀(d) = 0 pour tout S ≥ 3.

**Preuve :**

Pour x = 2 avec e₀ = 0 (wlog, d impair) :
```
g(v) = 3 + 2^Δ,  Δ = e₁ - e₀ ∈ {1, ..., S-2}
```

Bornes :
```
g_max = 3 + 2^{S-2}
d = 2^S - 9 = 4·2^{S-2} - 9
```

Pour **S ≥ 5** :
```
d - g_max = 4·2^{S-2} - 9 - 3 - 2^{S-2} = 3·2^{S-2} - 12
3·2^{S-2} > 12  ⟺  2^{S-2} > 4  ⟺  S > 4  ✓
```
Donc g < d, et puisque g > 0, on a d ∤ g. ∎

**Cas S = 4 :** d = 7, vecteurs apériodiques → g ∈ {5, 11}. 7 ∤ 5 et 7 ∤ 11. ✓
- Note : le vecteur (0,2) donne g = 7 = d, MAIS le vecteur 1010 est PÉRIODIQUE (période 2) → exclu

**Cas S = 3 :** d = 2³ - 9 = -1 < 0 → impossible (pas de cycle)

---

## EXTENSION : ARGUMENT DE TAILLE POUR x ≥ 3

L'argument de taille (g_max < d) a été testé pour x ≥ 3 :
```
g_max = 2^{S-x} · (3^x - 2^x)
d = 2^S - 3^x
```

Le ratio g_max/d croît comme (3/2)^x / (2^x) · ... et pour x ≥ 3, il dépasse 1 rapidement :
- x = 3, S = 5 : g_max/d = 19/5 = 3.8 → ÉCHOUE
- x = 3, S = 7 : g_max/d ≈ 1.49 → ÉCHOUE

**Conclusion :** L'argument de taille est SPÉCIFIQUE à x = 2. Pour x ≥ 3, une méthode structurelle est nécessaire.

→ C'est ce qui a motivé la descente 2-adique de R178.

---

## CONTEXTE

- Cette preuve était déjà implicite dans Steiner (1977) et les travaux ultérieurs
- Notre contribution : preuve isolée et auto-contenue, point de départ pour la suite
- Connexion directe avec R174 (e₀=0 wlog) et R175-R176 (premiers résistants)

## SCRIPT

| Script | Contenu |
|--------|---------|
| R177_x2_proof.py | Preuve complète x=2, vérification exhaustive S=4..19, analyse extension x≥3 |

## THÉORÈME

| ID | Énoncé | Statut |
|----|--------|--------|
| T180 | Pour x=2, N₀(d) = 0 ∀S≥3. Preuve par taille : g_max < d pour S≥5, vérif. S=4 | PROUVÉ ÉLÉMENTAIRE |

---

*Round R177 : 1 script, 1 théorème (T180), preuve élémentaire fondatrice.*
