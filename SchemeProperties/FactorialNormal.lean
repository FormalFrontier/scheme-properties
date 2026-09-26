module

public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import SchemeProperties.Factorial
public import SchemeProperties.Normal

public section

set_option warningAsError true

/-!
# Factorial schemes are normal

This file records the source-independent implication from factoriality to
normality. It uses the existing theorem that every GCD domain is integrally
closed and the accepted stalkwise definitions of factorial and normal schemes.
-/

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- Every factorial scheme is normal. -/
instance (priority := 900) isNormal_of_isFactorial [IsFactorial X] : IsNormal X := by
  exact isNormal_of_stalk X

#print axioms isNormal_of_isFactorial

end AlgebraicGeometry
