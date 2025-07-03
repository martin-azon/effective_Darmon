////////////////// List of functions/intrinsics //////////////////

/*
function ReadBool: DONE + TESTED
function ReadYN: DONE + TESTED

intrinsic Assumptions: DONE + TESTED
intrinsic Print: DONE + TESTED
intrinsic ReadAssumptions: DONE + TESTED

function FieldK: DONE + TESTED
function IsnthPowerFree: DONE + TESTED

intrinsic DefineGFE: DONE + TESTED
intrinsic Print: DONE + TESTED
intrinsic ReadGFE: DONE + TESTED
*/


///////////////////Reading input functions///////////////////

function ReadBool(question);
    //**Description:** Reads the input of the user to a true/false question.

    print question, "[true, false]";
    read input;
    if not (input in ["true", "false"]) then 
        error "Your must input must be one of the strings \"true\" or \"false\".";
    end if;
    return input eq "true";
end function;

intrinsic ReadYN(question) -> BoolElt
{Reads the input of the user to a yes/no question.}

    print question, "[yes, no]";
    read input;
    if not (input in ["yes", "no"]) then 
        error "Your input must be one of the strings \"yes\" or \"no\".";
    end if;
    return input eq "yes";
end intrinsic; 



//////////////////Construct the GFEAssumptions type//////////////////

declare type GFEAssumptions;

declare attributes GFEAssumptions: 
    DoingAssumptions,                //Boolean describing if the user does any assumption on the solutions
                                     //If DoingAssumptions is true, then the following attributes are used
    ab_is_even,                      //Boolean describing if a is even
    c_is_even,                       //Boolean describing if c is even
    ab_is_divisible_by_r,            //Boolean describing if a is divisible by r
    c_is_divisible_by_r,             //Boolean describing if c is divisible by r
    gminus_irreducible;              //Boolean describing if the polynomial gminus is reducible over Qr

intrinsic Assumptions(DoingAssumptions::BoolElt, conditions_at_2::SeqEnum[BoolElt], conditions_at_r::SeqEnum[BoolElt], gminus_irreducible::BoolElt) -> GFEAssumptions
{Create a GFEAssumptions object and attach to it the corresponding attributes}

    if conditions_at_2[1] and conditions_at_2[2] then   
        error "We cannot assume that a*b and c are both even.";
    end if;
    if conditions_at_r[1] and conditions_at_r[2] then   
        error "We cannot assume that a*b and c are both divisible by r.";
    end if;

    H := New(GFEAssumptions);
    H`DoingAssumptions := DoingAssumptions;
    H`ab_is_even := conditions_at_2[1];
    H`c_is_even := conditions_at_2[2];
    H`ab_is_divisible_by_r := conditions_at_r[1];
    H`c_is_divisible_by_r := conditions_at_r[2];
    H`gminus_irreducible := gminus_irreducible;
    return H;
end intrinsic;

intrinsic Print(H::GFEAssumptions)
{Print H}

    if H`DoingAssumptions then 
        print "We assume the following assumptions on a putative solution (a, b, c): \n";
        print "Is ab even?", H`ab_is_even;
        print "Is c even?", H`c_is_even;
        print "Is ab divisible by r?", H`ab_is_divisible_by_r;
        print "Is c divisible by r?", H`c_is_divisible_by_r;
        print "Is the polynomial gminus irreducible over Qr?", H`gminus_irreducible;
    else 
        print "We do not assume any hypothesis on a putative solution (a, b, c).";
    end if;
end intrinsic;

intrinsic ReadAssumptions() -> GFEAssumptions
{Reads the input of the user to initialise a GFEAssumptions object}

    DoingAssumptions := ReadYN("Do you wish to assume certain hypotheses on a putative solution (a, b, c)?");
    if DoingAssumptions then
        ab_is_even := ReadBool("Is a*b even?");
        if ab_is_even then 
            c_is_even := false;
        else
            c_is_even := ReadBool("Is c even?");
        end if;
        ab_is_divisible_by_r := ReadBool("Is a*b divisible by r?");
        if ab_is_divisible_by_r then 
            c_is_divisible_by_r := false;
        else
            c_is_divisible_by_r := ReadBool("Is c divisible by r?");
        end if;
        gminus_irreducible := ReadBool("Is the polynomial gminus irreducible over Qr?");
        return Assumptions(true, [ab_is_even, c_is_even], [ab_is_divisible_by_r, c_is_divisible_by_r], gminus_irreducible);
    else 
        return Assumptions(false, [false, false], [false, false], false);
    end if;
end intrinsic;



/////////////////Arithmetic functions/////////////////

function FieldK(r);
    // **Description:** Constructs the totally real subfield of the r-th cyclotomic field
    
    Cycl<zeta> := CyclotomicField(r);
    return sub<Cycl | zeta + 1/zeta>;
end function;

function IsnthPowerFree(u, n);
    // **Description:** Checks if the integer u is free of n-th powers or not

    if (not IsIntegral(u)) or (not IsIntegral(n)) then
        error "u and n must be integers.";
    end if;
    if u eq 0 then
        return false;
    end if;
    abs_u := Abs(u);
    if abs_u eq 1 then
        return true;
    end if;    

    prime_factors := Factorization(abs_u);
    for factor in prime_factors do
        if factor[2] ge n then
            return false;
        end if;
    end for;
    return true;
end function;



//////////////////Construct the GFE type //////////////////

declare type GFE;

declare attributes GFE:
    signature,                      //signature of the equation: MonStgElt in ["ppr", "rrp"]
    r,                              //exponent r: RngIntElt
    fieldK,                         //field K = Q(zeta_r + zeta_r^(-1)): FldNum 
    A,                              //coefficient A: RngIntElt
    B,                              //coefficient B: RngIntElt
    C,                              //coefficient C: RngIntElt
    Assumptions;                    //Assumptions on the solutions: GFEAssumptions

declare verbose GFE, 3;

intrinsic DefineGFE(signature::MonStgElt, r::RngIntElt, A::RngIntElt, B::RngIntElt, C::RngIntElt, H::GFEAssumptions) -> GFE
{Creates a GFE object from a string signature, integers r, A, B, C, and Assumptions H.}

    if not IsPrime(r) or (r le 3) then 
        error "r must be a prime number greater or equal than 5";
    end if;

    if (A*B*C eq 0) or (Gcd(A, B) ne 1) or (Gcd(A, C) ne 1) or (Gcd(B, C) ne 1) then
        error "The coefficients A, B, C must be non-zero and pairwise coprime.";
    end if;
    if (not IsnthPowerFree(A, r)) or (not IsnthPowerFree(B, r)) or (not IsnthPowerFree(C, r)) then 
        error "The coefficients A, B, C must be free of", r, "-th powers.";
    end if;

    if (A*B mod 2 eq 0) and H`c_is_even then
        error "A*B being even, we cannot assume that c is also even.";
    end if;
    if (C mod 2 eq 0) and H`ab_is_even then 
        error "C being even, we cannot assume that a*b is also even";
    end if;
    if (A*B mod r eq 0) and H`c_is_divisible_by_r then 
        error "A*B being divisible by r, we cannot assume that c is also divisible by r";
    end if;
    if (C mod r eq 0) and H`ab_is_divisible_by_r then
        error "C being divisible by r, we cannot assume that a*b is also divisible by r";
    end if;

    if (signature eq "rrp") and ((A*B)^2 eq 1) then
        H`gminus_irreducible := false;
    end if;
     
    E := New(GFE);
    E`signature := signature;
    E`r := r;
    E`A := A;
    E`B := B;
    E`C := C;
    E`fieldK := FieldK(r);
    E`Assumptions := H;

    return E;
end intrinsic;

intrinsic Print(E::GFE) 
{Print a GFE object}
    
    if E`signature eq "ppr" then
        print E`A, "*x^p +", E`B, "*y^p = ", E`C, "*z^", E`r, "\n";
    else
        print E`A, "*x^",  E`r, " + ", E`B, "*y^",  E`r," = ", E`C, "*z^p \n";
    end if;
    print E`Assumptions;
end intrinsic;

intrinsic ReadGFE() -> GFE
{Reads the input of the user to initialise a GFE object}

    read signature, "Do you want to solve an equation of signature (p, p, r) or (r, r, p)? [ppr, rrp]";
    if signature notin ["ppr", "rrp"] then
        error "You must input one of the strings \"ppr\" or \"rrp\".";
    end if;

    readi r, "Exponent r equals?";
    readi A, "Coefficient A equals?";
    readi B, "Coefficient B equals?";
    readi C, "Coefficient C equals?";
    H := ReadAssumptions();

    return DefineGFE(signature, r, A, B, C, H);
end intrinsic;