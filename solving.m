////////////////// List of functions/intrinsics //////////////////

/*
intrinsic SolveGFE: NOT YET DONE, TO BE TESTED

intrinsic main: DONE, TO BE TESTED
intrinsic mainRead: DONE, TO BE TESTED
*/

declare verbose test, 5;


//////////// Solving GFEs ////////////

intrinsic SolveGFE(E::GFE : initially_eliminated_ps := {2, 3}) 
{Solving the family of GFEs given by the parameters above}
    
    HC := HeckeConstituents(LevelNewforms(E));
    
    // We initialise variables for storing results.
    remaining_HC := HC;
    uneliminated_ps_for_gs := [];
    first_qs := [];


    // Loop through each Hecke constituent to eliminate it,
    // or at least bound the ps for which we cannot eliminate it. 
    for i in [1..#HC] do
        g := HC[i];
        print "\n\n\n\n### We are working to eliminate the", i, "th Hecke constituent.###";
        Coef_field := BaseField(g);
        t0 := Realtime();
        if Degree(Coef_field) le 24 then
            max_time := 300;
        else 
            max_time := 600;
        end if;
        unelim_ps, eliminated_g, first_q_for_g := Eliminate_g(g, E : init_eliminated_ps := initially_eliminated_ps, maximal_duration := max_time);
        if eliminated_g then
            print "The form was eliminated in", Realtime(t0), "seconds.";
            remaining_HC := RemoveFirstElement(remaining_HC);
            unelim_ps := {1};
            // To avoid Type issues in Magma, we store the set {1} to unelim_ps.
            // Since the form has been eliminated, unelim_ps should be {}, but Magma won't 
            // create a list storing at some spots the empty set and at others some finite sets of integers.
        else 
            print "After", Realtime(t0), "seconds, the form was not eliminated. We move on to the next one!";
        end if;
        if unelim_ps eq {1} then 
            print "unelim_ps = {}";
            // Recall that setting unelim_ps at {1} was just a trick to avoid type issues in Magma
        elif unelim_ps eq {} then
            print "No prime number has been eliminated for this form...";
        else 
            print "unelim_ps =", unelim_ps;
        end if;
        uneliminated_ps_for_gs := Append(uneliminated_ps_for_gs, [unelim_ps]);
        first_qs := Append(first_qs, [first_q_for_g]);
    end for;

    // Process the results to find the primes that were not eliminated for every form.
    not_eliminated_ps := {};
    for i in [1..#HC] do
        not_eliminated_ps := not_eliminated_ps join uneliminated_ps_for_gs[i, 1];
        // We store in a set all the ps for which there is at least one Hecke_constituent that
        // was not eliminated.
    end for;
    not_eliminated_ps := not_eliminated_ps diff {1};
    // We remove from such set 1, which was artificially added above.

    print "\n\n\nWe didn't manage to get rid of the following primes:", not_eliminated_ps;

end intrinsic;


///////////// main intrinsic /////////////

intrinsic Main(E::GFE : irreducibility_argument := false, init_eliminated_ps := {2, 3})
{Main intrinsic solving a GFE for the parameters given as input}

    print "We are working to solve the Generalised Fermat Equation", E;

    if CheckIrreducibility(E : irred_argument := irreducibility_argument) then  
        SolveGFE(E : initially_eliminated_ps := init_eliminated_ps);
    elif ReadArgumentIrred() then
        SolveGFE(E : initially_eliminated_ps := init_eliminated_ps);
    end if;

end intrinsic;

intrinsic TerminalMain() 
{Main intrinsic solving a GFE and reading the parameters from the terminal}

    E := ReadGFE();
    SolveGFE(E);

    if CheckIrreducibility(E) then  
        SolveGFE(E);
    elif ReadArgumentIrred() then
        SolveGFE(E);
    end if;
end intrinsic;