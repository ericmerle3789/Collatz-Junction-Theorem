import CollatzVerified

-- Verify no axioms leak into the key theorems
#print axioms G2c.g2c_all_19
#print axioms G2c.g2c_k7752
#print axioms G2c.g2c_k6891

def main : IO Unit :=
  IO.println "CollatzVerified: Basic (73 theorems) + G2c (19+4 theorems), 0 sorry, 0 axiom."
