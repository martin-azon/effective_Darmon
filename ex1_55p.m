load "Elimination_functions.m";

// We initialise the field K = Q(w), where w is a root of x^2 + x + 1.
// This is the the totally real subfield of the 5th cyclotomic field.
K<w> := fieldK(5);
OK := Integers(K);
Gal := Automorphisms(K);

I2:=Factorisation(2*OK)[1, 1];
I5:=Factorisation(5*OK)[1, 1];
I7:=Factorisation(7*OK)[1, 1];

levelN := I2*I5*I7^2;

// We compute the space of Hilbert newforms of levelN.
Space_newforms := NewSubspace(HilbertCuspForms(K, levelN));
print "Computing newforms of level:\n", Factorisation(levelN), "\n\nDimension of the space =", Dimension(Space_newforms);
t_start := Realtime();
Hecke_constituents := Eigenforms(Space_newforms);
print "It took", Realtime(t_start), "seconds to compute the space of newforms.";
print "There are ", #Hecke_constituents, "Hecke constituents to eliminate.";
print "The degrees of the coefficient fields of the Hecke constituents are", [Degree(BaseField(g)) : g in Hecke_constituents];

// We initialise variables for storing results.
remaining_HC := Hecke_constituents;
uneliminated_ps_for_gs := [];
first_qs := [];


// Loop through each Hecke constituent to try to eliminate it,
// or at least bound the ps for which we cannot eliminate it. 
for i in [1..#Hecke_constituents] do
    g := Hecke_constituents[i];
    print "\n\n\n\n### We are working to eliminate the", i, "th Hecke constituent.###";
    Coef_field := BaseField(g);
    t0 := Realtime();
    unelim_ps, eliminated_g, first_q_for_g := Eliminate_g(g, "rrp", 5, 1, 7, 1 : tw_coprime_to_r := 1, val_tw_above_r := 1, forbidden_qs := {2, 5, 7}, maximal_duration := 900, max_amount_useless_qs := 5);
    if eliminated_g then
        print "The form was eliminated in", Realtime(t0), "seconds.";
        remaining_HC := Remove_first_elt(remaining_HC);
        unelim_ps := {1};
        // To avoid Type issues in Magma, we store the set {1} to unelim_ps.
        // Since the form has been eliminated, unelim_ps should be {}, but Magma won't 
        // create a list storing at some spots the empty set and at others finite sets of integers.
    else 
        print "After", Realtime(t0), "seconds, the form was not eliminated. We move on to the next one!";
    end if;
    if unelim_ps eq {1} then 
        print "unelim_ps = {}";
        // Recall that setting unelim_ps at {1} was just a trick to avoid type issues in Magma
    else 
        print "unelim_ps =", unelim_ps;
    end if;
    uneliminated_ps_for_gs := Append(uneliminated_ps_for_gs, [unelim_ps]);
    first_qs := Append(first_qs, [first_q_for_g]);
end for;

// Process the results to find the primes that were not eliminated for every form.
not_eliminated_ps := {};
for i in [1..#Hecke_constituents] do
    not_eliminated_ps := not_eliminated_ps join uneliminated_ps_for_gs[i, 1];
    // We store in a set all the ps for which there is at least one Hecke_constituent that
    // was not eliminated.
end for;
not_eliminated_ps := not_eliminated_ps diff {1};
// We remove from such set 1, which was artificially added above.

print "\n\n\nWe didn't manage to get rid of the following primes:", not_eliminated_ps;