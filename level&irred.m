////////////////// List of functions/intrinsics //////////////////

/*
intrinsic ExponentOfTheLevelAt_2: DONE + TESTED
intrinsic ExponentOfTheLevelAt_r: DONE + TESTED
function RadicalWithout_2r: DONE + TESTED 
intrinsic LevelNewforms: : DONE + TESTED
intrinsic HeckeConstituents: TO BE POLISHED

function MultiplicativeOrder: DONE + TESTED
intrinsic CheckIrreducibility: DONE + TESTED
intrinsic ReadArgumentIrred: DONE + TESTED
*/


////////////Computing the level of the corresponding newforms////////////

intrinsic ExponentOfTheLevelAt_2(E :: GFE) -> RngIntElt
{Computes the exponent of the level of the newforms at 2}

    H := E`Assumptions;
    if E`signature eq "ppr" then
        if (E`A*E`B mod 2 eq 0) or H`ab_is_even then 
            return 1;
        elif (Valuation(E`C, 2) in [1, 2, 3]) and (not H`c_is_even) then 
            error "The conductor exponent at 2 is not known in this case.";
        elif (Valuation(E`C, 2) eq 4) and (not H`c_is_even) then 
            return 0;
        else 
            return 2;
        end if;
    else 
        if (E`C mod 4 eq 0) or H`c_is_even then 
            return 1;
        elif ((Valuation(E`C, 2) eq 1) and (not H`c_is_even)) or ((Valuation(E`A*E`B, 2) in [0, 1, 2, 3]) and (not H`ab_is_even)) then
            error "The conductor exponent at 2 is not known in this case.";
        elif (Valuation(E`A*E`B, 2) eq 4) and (not H`ab_is_even) then
            return 0;
        else
            return 2;
        end if;
    end if;
    return -1;
end intrinsic;

intrinsic ExponentOfTheLevelAt_r(E :: GFE) -> RngIntElt
{Computes the exponent of the level of the newforms at frakr}

    H := E`Assumptions;
    if E`signature eq "ppr" then
        if H`ab_is_divisible_by_r or (Valuation(E`A*E`B, E`r) gt 2) then
            return 1;
        elif (Valuation(E`A*E`B, E`r) eq 2) and (not H`c_is_divisible_by_r) then 
            return 3;
        elif (Valuation(E`A*E`B, E`r) eq 1) and (not H`c_is_divisible_by_r)then 
            return 2 + Numerator((E`r+1)/2);
        elif E`C mod E`r ne 0 then
            if H`gminus_irreducible then
                return 3;
            else
                return 2;
            end if;
        else   
            return 2 + E`r;
        end if;
    else 
        if H`c_is_divisible_by_r or (Valuation(E`C, E`r) ge 2) then 
            return 1;
        elif (Valuation(E`C, E`r) eq 1) and (not H`ab_is_divisible_by_r) then 
            return 3;
        elif E`A*E`B mod E`r ne 0 then 
            if H`gminus_irreducible then 
                return 3;
            else 
                return 2;
            end if;
        else 
            return 2 + E`r;
        end if;
    end if;
end intrinsic;

function RadicalWithout_2r(u, r);
    // **Description:** Computes the product of all primes dividing u that are not 2 nor r

    if u eq 0 then
        return 0;
    end if;

    abs_u := Abs(u);
    if abs_u eq 1 then
        return 1;
    end if;

    dividing_primes_not_2r := [ factor[1] : factor in Factorization(abs_u) | factor[1] notin [2, r]];
    if dividing_primes_not_2r eq [] then 
        return 1;
    else 
        return &* dividing_primes_not_2r;
    end if;
end function;

intrinsic LevelNewforms(E::GFE) -> RngOrdIdl
{Computes the level of the newforms that correspond to a putative solution}

    K := E`fieldK;
    OK := Integers(K);
    Ir := Factorisation(E`r*OK)[1, 1];

    exponent_2 := ExponentOfTheLevelAt_2(E);
    exponent_r := ExponentOfTheLevelAt_r(E);
    if E`signature eq "ppr" then 
        return Ir^exponent_r*((2^exponent_2*RadicalWithout_2r(E`A*E`B, E`r)*RadicalWithout_2r(E`C, E`r)^2)*OK);
    else
        return Ir^exponent_r*((2^exponent_2*RadicalWithout_2r(E`C, E`r)*RadicalWithout_2r(E`A*E`B, E`r)^2)*OK);
    end if;
end intrinsic;


/*
intrinsic DifferentLevels(E::GFE) -> List
{Computes the different levels at which one has to work depending on the assumptions on a solution}

    H := E`Assumptions;

    if H`DoingAssumptions then
        return [* LevelNewforms(E), H *];
    else 
        H1 := Assumptions(true, [true, false], [true, false], false);
        H2 := Assumptions(true, [true, false], [false, true], false);
        H3 := Assumptions(true, [true, false], [false, true], true);
        H4 := Assumptions(true, [false, true], [true, false], false);
        H5 := Assumptions(true, [true, false], [true, false], false);
        H6 := Assumptions(true, [true, false], [true, false], false);
        H7 := Assumptions(true, [true, false], [true, false], false);

    return [* *];
end intrinsic;
*/


intrinsic HeckeConstituents(levelN::RngOrdIdl) -> List
{Computes the Hecke constituents of the considered level}

    K := NumberField(Order(levelN));
    Space_newforms := NewSubspace(HilbertCuspForms(K, levelN));
    print "Computing newforms of level:\n", Factorisation(levelN), "\n\nDimension of the space =", Dimension(Space_newforms);
    t_start := Realtime();
    Hecke_constituents := Eigenforms(Space_newforms);
    print "It took", Realtime(t_start), "seconds to compute the space of newforms.";
    print "There are", #Hecke_constituents, "Hecke constituents to eliminate.";
    print "The degrees of the coefficient fields of the Hecke constituents are", [Degree(BaseField(g)) : g in Hecke_constituents];
    return Hecke_constituents;
end intrinsic;



//////////////////Testing if the residual representation is irreducible////////////////

function MultiplicativeOrder(u, n);
    //**Description:** Computes the multiplicative order of u mod n if u is invertible, and returns 0 otherwise

    _, phi := ResidueClassRing(n);
    if phi(u) eq 0 then 
        return 0;
    else 
        return Order(phi(u));
    end if;
end function;


intrinsic CheckIrreducibility(E::GFE : irred_argument := false) -> BoolElt
{Checks if the criterion of absolute irreducibility given in the paper is satisfied or not}

    if irred_argument then
        return true;
    else 
        H := E`Assumptions;
        if E`signature eq "ppr" then
            if ((Valuation(E`C, 2) ge 4) or H`c_is_even) and IsEven(MultiplicativeOrder(2, E`r)) then 
                return true;
            end if;
            for q in Set(PrimeDivisors(E`C)) do
                if (q ne E`r) and IsEven(MultiplicativeOrder(q, E`r)) then
                    return true;
                end if;
            end for;
        else 
            if ((Valuation(E`A*E`B, 2) ge 4) or (IsEven(E`A*E`B) and H`ab_is_even)) and IsEven(MultiplicativeOrder(2, E`r)) then 
                return true;
            end if;
            for q in Set(PrimeDivisors(E`A*E`B)) do
                if (q ne E`r) and IsEven(MultiplicativeOrder(q, E`r)) then
                    return true;
                end if;
            end for;
        end if;
        print "With this choice of parameters, we cannot prove the absolute irreducibility. \nProvide your own arguments! \n";
        return false;
    end if;
end intrinsic;


intrinsic ReadArgumentIrred() -> BoolElt
{Reads if the user has an alternative argument for proving the absolute irreducibility}

    return ReadYN("Do you have an alternative argument for proving the absolute irreducibility \n of the Galois representation attached to the Frey Jacobian?");
end intrinsic;