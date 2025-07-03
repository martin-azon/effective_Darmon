AttachSpec("spec"); 

//////////// Enter here the parameters of the equation to be solved ////////////

signature := "ppr";                  // Signature of the equation: must be either "ppr" or "rrp".
r := 5;                              // Fixed exponent r: must be a prime number > 3.
A := 7;                              // Coefficient A: must be a non-zero integer free of r-th powers.
B := 1;                              // Coefficient B: must be a non-zero integer free of r-th powers.
C := 3;                              // Coefficient C: must be a non-zero integer free of r-th powers.
                                     // The integers A, B, C must be pairwise coprime. 

DoingAssumptions := true;            // Boolean describing if we do any assumptions on (a, b, c).
                                     // If DoingAssumptions is set to false, all the constants below 
                                     // are irrelevant.
ab_even := true;                     // Boolean describing if we assume a*b to be even.
c_even := false;                     // Boolean describing if we assume c to be even.
ab_div_r := true;                   // Boolean describing if we assume a*b to be divisible by r.
c_div_r := false;                    // Boolean describing if we assume c to be divisible by r.
g_irred := false;                    // Boolean describing if we assume the polynomial g_{r}^{-} to be irreducible over Q_r.

H := Assumptions(DoingAssumptions, [ab_even, c_even], [ab_div_r, c_div_r], g_irred);
E := DefineGFE(signature, r, A, B, C, H);

irred_argument := true;              // Boolean describing if the user has another argument for proving absolute irreducibility
                                     // of the Galois representation attached to the Frey Jacobian, in case the criterion in the paper
                                     // is not satisfied.

initially_eliminated_ps := {2, 3, r};      // Set of ps that have already been eliminated for theoretical reasons
                                     // (e.g. equation already solved in the literature).



//////////////////// Main function ////////////////////

Main(E : irreducibility_argument := irred_argument, init_eliminated_ps := initially_eliminated_ps);

// If you wish to execute this in the terminal and input there your parameters, execute the intrinsic below
//mainRead();




//////////////////// Comments ////////////////////

/* You may modify some further parameters in "solving.m", like the following ones:

maximal_duration : After this amount of seconds, the Eliminate_g intrinsic should stop, whether we have managed to eliminate the newform or not.
max_amount_useless_qs : Upper bound on the number of primes q that do not bring any new information when trying to eliminate the newform g.

*/