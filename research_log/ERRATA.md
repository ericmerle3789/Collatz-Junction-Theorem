# ERRATA — Research Logs

**Date** : 26 février 2026
**Auteur** : Bureau d'audit de certification

---

## E-1 : Valeur erronée de γ (MAJEUR)

**Fichiers affectés** :
- `phase10j_dissonance_resonance.md` — lignes 23, 208, 225, 229-231, 405, 448, 464, 544, 558, 724
- `phase10k_estocade.md` — lignes 16, 905
- `phase10l_choc_des_cristaux.md` — lignes 41, 401, 411, 459, 536, 575, 718
- `phase10m_theoreme_fondamental.md` — lignes 118, 277, 611, 669
- `phase11a_obstruction_algebrique.md` — ligne 370
- `phase11b_verification_computationnelle.md` — ligne 237

**Erreur** : Ces fichiers utilisent la valeur γ = 0.0549 (ou 0.054979) calculée via la formule **incorrecte** :
```
γ = ln(3) − h(log₂(3))     ← FAUX
```

Cette formule est doublement erronée :
1. **Mélange d'unités** : `ln(3)` est en nats, `h(log₂(3))` mélange base 2 et base e
2. **Domaine invalide** : `log₂(3) = 1.585 > 1`, hors du domaine [0,1] de l'entropie de Shannon

**Valeur correcte** :
```
γ = 1 − h_bits(1/log₂(3)) = 1 − h_bits(ln(2)/ln(3)) = 0.050044472811669
```
où h_bits(p) = −p·log₂(p) − (1−p)·log₂(1−p) est l'entropie binaire de Shannon.

**Correction** : La phase 12 (`phase12_junction_theorem.md`, ligne 12) corrige explicitement cette erreur. Le preprint final (`paper/preprint.md`, §3.3) utilise la valeur correcte γ = 0.05004447281167.

**Impact** : Les conclusions qualitatives des phases 10-11 restent valides (γ > 0 implique toujours une obstruction entropique), mais les calculs numériques spécifiques utilisant 0.0549 sont faux d'environ 10%.

---

## E-2 : Année de référence Barina (MINEUR)

**Fichiers affectés** :
- `phase12_junction_theorem.md` — lignes 89, 273
- `phase11b_verification_computationnelle.md` — ligne 521
- `phase10k_estocade.md` — ligne 1048
- `phase10m_theoreme_fondamental.md` — ligne 148

**Erreur** : Ces fichiers référencent « Barina (2020) ».

**Correction** : La référence correcte est Barina (2021), *Journal of Supercomputing*, vol. 77, pp. 2681-2688. Le preprint final (`paper/preprint.md`) et le README utilisent la bonne année.

---

*Les logs de recherche sont conservés tels quels comme trace historique du processus de recherche. Consulter le preprint final pour les valeurs définitives.*
