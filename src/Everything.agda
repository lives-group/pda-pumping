-- Entry point of the development: every statement of the paper, in order.
-- The library file (pda-pumping.agda-lib) sets --safe for every module, so
-- the whole development is checked without postulates or unsafe pragmas.
module Everything where

-- Section 4: normalization of an arbitrary PDA (Theorem 1)
open import PDA.NormalizePDA using (normalize)

-- Section 5: the geometry of stack profiles
open import PDA.Pumping.IVT using (ivt)
open import PDA.Pumping.LpFp using (stackAt-eq)

-- Section 6: pumping a normal PDA, then an arbitrary one (Theorems 2 and 3)
open import PDA.Pumping.PumpNormal using (pda-pumping-N-at)
open import PDA.Pumping.Bounded using (pumpBound; module Search)
open import PDA.Pumping.Arbitrary using (pda-pumping-N; pumping-pda)

-- The IsNormalPDA⁺ variant, |vy| ≥ 1 by the counting argument
open import PDA.Pumping.Lemma using (pda-pumping)

-- Application: { aⁿ bⁿ cⁿ } is not a PDA language
open import Examples.ABC using (abc-not-PDA)
