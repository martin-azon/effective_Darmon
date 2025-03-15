PolsQ<x> := PolynomialRing(Rationals()); 

function fieldK(r);
    // **Description:** This function constructs the totally real subfield of the r-th cyclotomic field.
    
    Cycl<zeta> := CyclotomicField(r);
    return sub<Cycl | zeta + 1/zeta>;
end function;


function Minpolw(r); 
    // **Description:** This function computes the minimal polynomial of the element w = zr + zr^(-1), zr is a primitive r-th root of unity.

    _<w> := fieldK(r);
    return MinimalPolynomial(w);
end function;


function pol_ppr(r, A, C, ap, c);
    // **Description:** This function constructs the defining polynomial of the Frey curve of signature (p, p, r).
    // **Input:**
    //   - r: Exponent appearing in the GFE.
    //   - A: First coefficient in the GFE.
    //   - C: Third coefficient in the GFE.
    //   - ap: This would correspond to a^p, where a is the first element of the putative solution (a, b, c).
            // By considering ap instead of a, the polynomial does not depend on p anymore.
    //   - c: Third element of the putative solution (a, b, c).

    h := Minpolw(r);
    return (-(C*c)^2)^(Numerator((r-1)/2))*x*Evaluate(h, 2 - (x/(C*c))^2 ) + 2*(C*c^r - A*a)*C^(r-1);
end function;


function pol_rrp(r, A, B, a, b); 
    // **Description:** This function constructs the defining polynomial of the Frey curve of signature (r, r, p).
    // **Input:**
    //   - r: Exponent appearing in the GFE.
    //   - A: First coefficient in the GFE.
    //   - B: Second coefficient in the GFE.
    //   - a: First element of the putative solution (a, b, c).
    //   - b: Second element of the putative solution (a, b, c).
        
    h := Minpolw(r);
    return (A*B*a*b)^(Numerator((r-1)/2))*x*Evaluate(h, (x^2/(A*B*a*b)) +2) + (B*b^r - A*a^r)*(A*B)^(Numerator((r-1)/2));
end function;


function TracesFrobs_at_conjugates(Crv, Q);
    // **Description:** This function computes the set of Traces of Frobenius of the Jacobian of a curve at the prime ideals in the base field of the curve that are conjugate to Q.
    // **Input:**
    //   - Crv: An hyperelliptic curve defined over a number field.
    //   - Q: A prime ideal living in the ring of integers of such field.

    PolsBase := PolynomialRing(BaseField(Crv));
    Lf := EulerFactor(Crv, Q);
    Lfactors := Factorization(PolsBase ! Reverse(Lf));
    return Set([-Coefficient(f[1],1) : f in Lfactors]); 
end function;

