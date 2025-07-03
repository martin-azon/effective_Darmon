////////////////// List of functions/intrinsics //////////////////

/*
intrinsic RemoveFirstElement: DONE
function SigmaBetweenPrimes: DONE
TracesFrobsAtConjugates: DONE 

function N_good: DONE
function M_toric: DONE

intrinsic Bounding_ps: TO BE TESTED
intrinsic RefinedBounding_ps: NOT YET DONE

intrinsic Eliminate_g: TO BE TESTED
*/


////////////////////// Some useful functions //////////////////////

intrinsic RemoveFirstElement(L::List) -> List
{Removes the first element of a list}

    return Reverse(Prune(Reverse(L)));
end intrinsic;

function SigmaBetweenPrimes(Q1, Q2, GalGrp);
    // **Description:** Returns the element sigma of the Galois group that maps the ideal Q1 onto Q2

	for sigma in GalGrp do
        if Q2 eq sigma(Q1) then
            return sigma;
        end if;
	end for;
end function;

function TracesFrobsAtConjugates(Crv, Q);
    // **Description:** Computes the set of Traces of Frobenius of the Jacobian of a curve 
    // at the prime ideals in the base field of the curve that are conjugate to Q.
    // **Input:**
    //   - Crv: An hyperelliptic curve defined over a number field.
    //   - Q: A prime ideal living in the ring of integers of such field.

    PolsBase := PolynomialRing(BaseField(Crv));
    Lf := EulerFactor(Crv, Q);
    Lfactors := Factorization(PolsBase ! Reverse(Lf));
    return Set([-Coefficient(f[1],1) : f in Lfactors]); 
end function;


//////////////////////Computing the quantities Ngood, Mtoric//////////////////////

function N_good(TracesCrv_q, Hecke_eigenvals, Sigma, toKg);
    // **Description:** Computes the quantity N_good, used in the elimination process of Hilbert modular forms.
    // **Input:**
    //   - TracesCrv_q: A sequence of integers, representing the traces of Frobenius (a_Q(Jac(C)))) of the Jacobian of a Frey curve at prime ideals Q above q.
    //   - Hecke_eigenvals: A sequence of algebraic numbers, representing the Hecke eigenvalues (a_Q(g)) of a Hilbert modular form g at prime ideals Q above q.
    //   - Sigma: A sequence of automorphisms of the number field K.
    //   - toKg: A map that injects K into Kg, the coefficient field of the Hilbert newform.
    
    prod := 1;  
    for tr in TracesCrv_q do   
        factor := Gcd([Integers() ! AbsoluteNorm(toKg(Sigma[i](tr)) - Hecke_eigenvals[i]) : i in [1..#Sigma]]);
        if factor eq 0 then
            return 0;
        end if;
        prod *:= factor;
    end for;
    return prod;
end function;

function M_toric(Q, Hecke_eigenvals);
    // **Description:** Computes the quantity M_toric, used in the elimination process.
    // **Input:**
    //   - Q: A prime ideal in a the field of definition of a Hilbert newform g.
    //   - Hecke_eigenvals: A sequence of algebraic numbers, representing the Hecke eigenvalues (a_Q1(g)) of a Hilbert modular form g at prime ideals Q1 above q.

    return Gcd([Integers() ! AbsoluteNorm((Norm(Q)+1)^2 - a_q^2) : a_q in Hecke_eigenvals]);
end function;



//////////////////////////Bounding uneliminated primes//////////////////////////

intrinsic Bounding_ps(g::ModFrmHilElt, q::RngIntElt, E::GFE : infinitely_many_to_eliminate := true, uneliminated_ps := {} , initially_eliminated_ps := {2, 3}) -> SetEnum, BoolElt, BoolElt 
{Attempts to bound the set of possible prime exponents p for which there could be an isomorphism between the Galois representations of the Jacobian of the Frey curve attached to a putative solution of the equation, and the Hilbert newform g.}
    // **Input:**
    //   - g: A Hilbert newform.
    //   - q: A rational prime.
    //   - E: A GFE object.
    //   - infinitely_many_to_eliminate: Booelan stating if there are still infinitely many primes to eliminate. The first time the function is executed, it should be set at true.
    //   - uneliminated_ps: Set of primes that have not been eliminated yet. As soon, as infinitely_many_to_eliminate is set to false, uneliminated_ps should be a non-empty finite set of primes.
    //   - initially_eliminated_ps: Set of primes that might have been already eliminated for theoretical reasons (e.g. equation already solved in the literature).
    // **Output:**
    //   - a set corresponding to the ps that have not been eliminated yet.
    //   - a boolean describing if the form g was eliminated using q.
    //   - a boolean describing if the prime q helped to bound the set of uneliminated ps.

    if not infinitely_many_to_eliminate and (uneliminated_ps eq {}) then
        error "If there are only finitely many ps to eliminate, they should appear in the set uneliminated_ps";
    end if;

    K<w> := E`fieldK;
    assert BaseField(Parent(g)) eq K;
    OK := Integers(K);
    GalK := Automorphisms(K);

    levelN := LevelNewforms(E); 
    if AbsoluteNorm(levelN) mod q eq 0 then 
        error "The prime q must not divide the norm of the level";
    end if;

    is_subfield, toKg := IsSubfield(K, BaseField(g));
    if not is_subfield then 
        error "The field of coefficients of g does not contain K.";
    end if;     

    QQs := SetToSequence(Support(q*OK));
    Q1 := QQs[1];
    automs_QQs := [SigmaBetweenPrimes(Q1, Q, GalK) : Q in QQs];


    print "Performing elimination with",#Set(QQs),"prime ideal(s) above", q;

  
    Hecke_eigenvals := [HeckeEigenvalue(g, QQ) : QQ in QQs];
    M_tor := M_toric(Q1, Hecke_eigenvals);
    
    if infinitely_many_to_eliminate then
        remaining_ps_to_eliminate := Set(PrimeDivisors(M_tor));
    else 
        remaining_ps_to_eliminate := {p : p in uneliminated_ps | M_tor mod p eq 0};
    end if;
    assert Type(remaining_ps_to_eliminate) eq SetEnum;

    if E`signature eq "ppr" then
        for ap, c in [0..q-1] do 
            if ([ap, c] ne [0, 0]) and (q notin [2, E`r]) and (E`C*E`A*ap*(E`C*c^E`r - E`A*ap) mod q ne 0) then 
                FreyCrv := FreyCurve(E, ap, 1, c);
                TracesCrv_q := TracesFrobsAtConjugates(FreyCrv, Q1);
                N_gd := N_good(TracesCrv_q, Hecke_eigenvals, automs_QQs, toKg);
                if N_gd eq 0 then
                    print "The form was not eliminated using prime ideals above", q;
                    if infinitely_many_to_eliminate then
                        return {}, false, false;
                    else 
                        return uneliminated_ps, false, false;
                    end if;
                else 
                    if infinitely_many_to_eliminate then
                        remaining_ps_to_eliminate := remaining_ps_to_eliminate join Set(PrimeDivisors(N_gd));
                    else 
                        remaining_ps_to_eliminate := remaining_ps_to_eliminate join {p : p in uneliminated_ps | N_gd mod p eq 0};
                    end if;
                end if;
            end if;
        end for;
    elif E`signature eq "rrp" then
        for a, b in [0..q-1] do
            if ([a, b] ne [0, 0]) and (q notin [2, E`r]) and (E`A*E`B*(E`A*a^E`r + E`B*b^E`r) mod q ne 0) then 
                FreyCrv := FreyCurve(E, a, b, 1);
                TracesCrv_q := TracesFrobsAtConjugates(FreyCrv, Q1);
                N_gd := N_good(TracesCrv_q, Hecke_eigenvals, automs_QQs, toKg);
                if N_gd eq 0 then
                    if infinitely_many_to_eliminate then
                        print "The form was not eliminated using prime ideals above", q;
                        return {}, false, false;
                    else 
                        print "The form was not eliminated using prime ideals above", q;
                        return uneliminated_ps, false, false;
                    end if;
                else 
                    if infinitely_many_to_eliminate then
                        remaining_ps_to_eliminate := remaining_ps_to_eliminate join Set(PrimeDivisors(N_gd));
                    else 
                        remaining_ps_to_eliminate := remaining_ps_to_eliminate join {p : p in uneliminated_ps | N_gd mod p eq 0};
                    end if;
                end if;
            end if;
        end for;
    else 
        error "signature must be either \"ppr\" or \"rrp\" ";
    end if;

    remaining_ps_to_eliminate := remaining_ps_to_eliminate diff initially_eliminated_ps;
    if (q in uneliminated_ps) or (infinitely_many_to_eliminate and (q notin initially_eliminated_ps)) then 
        remaining_ps_to_eliminate := remaining_ps_to_eliminate join {q};
    end if;

    if #remaining_ps_to_eliminate eq 0 then 
        return {}, true, true;
    else 
        print "We still have to eliminate exponents p =", remaining_ps_to_eliminate;
        return remaining_ps_to_eliminate, false, true;
    end if;
end intrinsic;


//intrinsic RefinedBounding_ps TO BE DONE







/////////////////////Eliminating newforms/////////////////////


intrinsic Eliminate_g(g::ModFrmHilElt, E::GFE : first_q := 3, init_eliminated_ps := {2, 3}, maximal_duration := 300, max_amount_useless_qs := 6) -> SetEnum, BoolElt, RngIntElt
{Attempts to eliminate the Hilbert newform g by checking if K is contained in its field of coefficients, or by iteratively applying Bounding_ps with different values of q.}
    // **Input:**
    //   - g: The Hilbert newform we are attempting to eliminate.
    //   - E: The GFE we wish to solve.
    //   - first_q: A prime integer. The first rational prime q used to apply Bounding_ps.
    //   - maximal_duration: An integer. The maximum of seconds the elimination process is allowed to run. 
    //   - max_amount_useless_qs: An integer. The maximum number of consecutive values of q that are allowed to be "useless" (not eliminating any new primes) before the process terminates.
    // **Output:**
    //   - the set of primes such that the pair (p, g) has not been eliminated.
    //   - a boolean describing if the form was eliminated.
    //   - the first prime q such that the bounding_ps worked with g and q.

    forbidden_qs := Set(PrimeDivisors(AbsoluteNorm(Level(Parent(g)))));

    Coef_field := BaseField(g);
    if Coef_field eq Rationals() then 
        print "The form was eliminated because K is not a subfield of Kg.";
        return {}, true, 1; //return 1 as first q because the argument uses the (non) inclusion of number fields
    else 
        is_subfield, toKg := IsSubfield(E`fieldK, Coef_field);
        if not is_subfield then
            print "The form was eliminated because K is not a subfield of Kg.";
            return {}, true, 1;
        else 
            t0 := Realtime();
            while first_q in forbidden_qs do 
                first_q := NextPrime(first_q);
            end while;    
            q := first_q;
            unelim_ps, eliminated_g, bounding_ps_at_q_worked := Bounding_ps(g, q, E : infinitely_many_to_eliminate := true, uneliminated_ps := {}, initially_eliminated_ps := init_eliminated_ps);
            number_useless_q := 0;
            if bounding_ps_at_q_worked then 
                first_q_to_work := q;
                inf_many_to_eliminate := false;
            else 
                inf_many_to_eliminate := true;
            end if;
            while not eliminated_g and (Realtime(t0) lt maximal_duration) and (number_useless_q lt max_amount_useless_qs) do
                if bounding_ps_at_q_worked and inf_many_to_eliminate then 
                    first_q_to_work := q;
                    inf_many_to_eliminate := false;
                end if;
                previous_unelim_ps := unelim_ps;
                q := NextPrime(q);
                if q notin forbidden_qs then 
                    unelim_ps, eliminated_g, bounding_ps_at_q_worked := Bounding_ps(g, q, E : infinitely_many_to_eliminate := inf_many_to_eliminate, uneliminated_ps := unelim_ps, initially_eliminated_ps := init_eliminated_ps);
                end if;
                if ((unelim_ps eq previous_unelim_ps) or not bounding_ps_at_q_worked) and (not inf_many_to_eliminate) then 
                    number_useless_q := number_useless_q + 1;
                end if;
            end while;
            if not bounding_ps_at_q_worked then
                first_q_to_work := 0;
            end if;
            return unelim_ps, eliminated_g, first_q_to_work;
        end if;
    end if;
end intrinsic;