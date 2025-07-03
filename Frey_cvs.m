////////////////// List of functions/intrinsics //////////////////

/*
intrinsic DefiningPolynomial: DONE + TESTED

function SQ: DONE + TESTED
intrinsic TwistAt_2: DONE + TESTED
intrinsic TwistAt_r: DONE + TESTED
intrinsic TwistParameter: DONE + TESTED

intrinsic FreyCurve: DONE + TO BE TESTED
*/


/////////////////Computing the Frey curve/////////////////

intrinsic DefiningPolynomial(E::GFE, a::RngIntElt, b::RngIntElt, c::RngIntElt) -> RngUPolElt
{Computes the defining polynomial of the Frey hyperelliptic curve attached to a putative solution}

    K<w> := E`fieldK;
    PolsK<x> := PolynomialRing(K);
    A := E`A;
    B := E`B;
    C := E`C;
    r := E`r;
    h := PolsK ! MinimalPolynomial(w);
    
    if E`signature eq "ppr" then 
        ap := a;    //Reminder: when searching for values of a_q(J), ap will range through every value in F_q
                    //One should think about ap as a^p, except that the value of p is not precised.
        if c ne 0 then
            return (-(C*c)^2)^(Numerator((r-1)/2))*x*Evaluate(h, 2 - (x/(C*c))^2) + 2*(C*c^r - 2*A*ap)*C^(r-1);
        else 
            return x^r + 2*(C*c^r - 2*A*ap)*C^(r-1);
        end if;
    else 
        if a*b ne 0 then    
            return (A*B*a*b)^(Numerator((r-1)/2))*x*Evaluate(h, 2 + (x^2/(A*B*a*b))) + (B*b^r - A*a^r)*(A*B)^(Numerator((r-1)/2));
        else 
            return x^r + (B*b^r - A*a^r)*(A*B)^(Numerator((r-1)/2));
        end if;
    end if;
end intrinsic;


function SQ(x);
    // **Description:** Tests if the property SQ holds for the integer x.

        return (x eq 0) or (IsEven(Valuation(x, 2)) and (x mod 4 in [0, 1]));
end function;


intrinsic TwistAt_2(E::GFE, a::RngIntElt, b::RngIntElt, c::RngIntElt) -> FldNumElt 
{Computes the 2-adic contribution of a twisting parameter delta_K}

    H := E`Assumptions;
    if E`signature eq "ppr" then
        ap := a;
        if (E`A*E`B mod 2 eq 0) or H`ab_is_even then 
            return 1;
        elif (Valuation(E`C, 2) ge 4) or H`c_is_even then 
            if SQ(2*E`C^(E`r-1)*(E`C*c^E`r - E`A*ap)) then
                return 1;
            else 
                return -1;
            end if;
        else 
            error "We cannot handle this case.";
        end if;
    else
        if (E`C mod 4 eq 0) or H`c_is_even then
            return 1;
        elif (Valuation(E`A*E`B, 2) ge 4) or H`ab_is_even then 
            if SQ((E`A*E`B)^(Numerator((E`r-1)/2))*(E`B*b^E`r - E`A*a^E`r)) then
                return 1;
            else 
                return -1;
            end if;
        else 
            error "We cannot handle this case.";
        end if;
    end if;
end intrinsic;


intrinsic TwistAt_r(E::GFE, a::RngIntElt, b::RngIntElt, c::RngIntElt) -> FldNumElt 
{Computes the r-adic contribution of a twisting parameter delta_K}

    K<w> := E`fieldK;
    H := E`Assumptions;

    if E`signature eq "ppr" then 
        if H`ab_is_divisible_by_r or (Valuation(E`A*E`B, E`r) gt 2) then
            return w - 2;
        else 
            return 1;
        end if;
    else 
        if H`c_is_divisible_by_r or (Valuation(E`C, E`r) ge 2) then 
            return w - 2;
        else 
            return 1;
        end if;
    end if;
end intrinsic;


intrinsic TwistParameter(E::GFE, a::RngIntElt, b::RngIntElt, c::RngIntElt) -> FldNumElt 
{Computes a twisting parameter delta_K for the equation E and the triple (a, b, c)}

    return TwistAt_2(E, a, b, c)*TwistAt_r(E, a, b, c);
end intrinsic;


intrinsic FreyCurve(E::GFE, a::RngIntElt, b::RngIntElt, c::RngIntElt) -> CrvHyp
{Returns the Frey hyperelliptic curve attached to a putative solution after twisting}

    return QuadraticTwist(HyperellipticCurve(DefiningPolynomial(E, a, b, c)), TwistParameter(E, a, b, c));
end intrinsic;
