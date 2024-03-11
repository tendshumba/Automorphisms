/*

The example for S_6 4A4A3A2A

*/
AttachSpec("../DecompAlgs/DecompAlgs.spec");
AttachSpec("../AxialTools/AxialTools.spec");
Attach("../DecompAlgs/AxialTools.m");
Attach("Automorphisms.m");

// Alter this to the path of where your algebra is stored

path := "../DecompAlgs/library/Monster_1,4_1,32/RationalField()/";

// Preliminary data
A := LoadDecompositionAlgebra(path cat "S6/15+45/6A5A4A4A3A2A_1.json");
// takes about 110 secs

F := BaseRing(A);
n := Dimension(A);
G := MiyamotoGroup(A);
assert GroupName(G) eq "S6";

// If the algebra is Miyamoto closed, then the Miyamoto group is a permutation group on the axes
axes := Axes(A);
assert forall{ <i, g> : i in [1..#axes], g in Generators(G) | axes[i]*g eq axes[Image(g,GSet(G),i)]};

// Computation 13.25 (a) We show that A has a unique Jordan axis.
Jords := JordanAxes(A);
assert #Jords eq 1;
d := Jords[1];
sigma_d := MiyamotoInvolution(d, 1/4: check_fusion := false);

// Computation 13.25 (b) Axes in the 15 orbit have twins
axes_reps := AxisOrbitRepresentatives(A);
assert #axes_reps eq 2;

orbits := [ axes[Setseq(o)] : o in Orbits(G) ];
assert {#x : x in orbits } eq {15, 45};

assert exists(orb_15){o : o in orbits | #o eq 15};
rep_15 := Representative(orb_15);
twins_rep_15 := FindMultiples(rep_15);
// takes about 30 sec

assert #twins_rep_15 eq 2;
exists(c){c : c in twins_rep_15| c ne rep_15};
// Since this is true for the representative, it is true for all. We use group action to get the rest.

orb_15_twins := {@ a*sigma_d : a in orb_15 @};
assert IsEmpty(orb_15 meet orb_15_twins);

// Computation 13.25 (c) Triple cycles (involutions not involved in the original axet) are induced by twinned axes.
Miy_elts := [ MiyamotoElement(A, i): i in [1..#axes] ];

invs_G := [ x : x in ConjugacyClasses(G) | x[1] eq 2 ];
assert {* x[2] : x in invs_G *} eq {* 15^^2, 45*};// So two classes of involutions of size 15.
assert exists(triple){t[3] : t in invs_G | t[3] notin Miy_elts};

assert forall{x : x in [y : y in invs_G | y[3] ne triple] | x[3] in Miy_elts};
// The others are exactly the two classes of involutions coming from axes

Miy_map := MiyamotoActionMap(A);
so, triple_axes := IsInducedFromAxis(A, Matrix(triple@Miy_map));
// takes about 90 secs

assert so;
assert #triple_axes eq 2 and forall{x : x in triple_axes | x notin axes};
assert triple_axes[1]*sigma_d eq triple_axes[2];
// Hence the 15 involutions corresponding to triple cycle are induced by a twined pair of axes.

orb_15_new := {@ A!a : a in Orbit(G@Miy_map, Vector(triple_axes[1])) @};
orb_15_new_twins := {@ a*sigma_d : a in orb_15_new @};
assert forall{ x : x in {orb_15_new, orb_15_new_twins} | #x eq 15 and IsEmpty(x meet axes) };
// So indeed new axes


// Computation 13.25 (d) The axes in the 45 orbit have no twins.
assert exists(orb_45){o : o in orbits | #o eq 45};
rep_45 := Representative(orb_45);
assert #FindMultiples(rep_45) eq 1;
// takes about 25 sec

// Computation 13.25 (e)

// An outer automorphism of S6 switches the single and the triple transpositions.  These are the two classes of involutions of conjugacy class size 15.
// Such an automorphism must therefore switch the original 15 axes to one of the two (twinned) new orbits of size 15.
// We can choose one of the new orbits of size 15.  A map to the other will be the composition of the outer automorphism g and sigma_d.
axes_75 := orb_15 join orb_15_new join orb_45;

G_to_G75 := hom<G -> Sym(75) | [ Sym(75)![Position(axes_75, a*g) : a in axes_75] : g in GeneratorsSequence(G)] >;
G75 := Image(G_to_G75);
assert GroupName(G75) eq "S6"; // So we have S_6 as a permutation group on 75 objects. 

aut_G := AutomorphismGroup(G75);
outs := [aut : aut in Generators(aut_G) | not IsInnerAutomorphism(aut)];
assert  #outs eq 1;
out := outs[1];

// We want to get the action on the 75 axes
// Since the Miyamoto map is a bijection on these 75 axes to the set of all involutions, we can get see our action here
Miy_75 := [ MiyamotoInvolution(axes_75[i], 1/32 : check_fusion := false)@@Miy_map@G_to_G75 : i in [1..75]];

Vaxes := sub< VectorSpace(A) | [ Vector(v) : v in axes_75]>;
out_perm := Sym(75)![Position(Miy_75, Miy_75[i]@out) : i in [1..75]];
out_map := hom< Vaxes -> VectorSpace(A) | [<Vaxes.i, Vaxes.(i^out_perm)> : i in [1..75]]>;
so, out_map := ExtendMapToAlgebraAutomorphism(A, out_map);
// takes 40 secs
assert so;

autG := PermutationGroup<75 | G75, out_perm>;
assert Order(autG) eq 1440;
assert GroupName(autG) eq "S6.C2";

order_4s := [ x[3] : x in ConjugacyClasses(autG) | x[1] eq 4];
assert exists(g){ g : g in order_4s | g notin G75 and g^2 in G75 };
// so an outer automorphism g of order 4 with g^2 in G. 

autG_mat := MatrixGroup<151, F | Image(Miy_map), Matrix([Vector(a)@out_map : a in Basis(A)])>;
assert #(Vector(d)^autG_mat) eq 1;
// So the Jordan axis is indeed fixed by the entire automorphism group autG.
// This justifies our above exclusion of it and the other twin orbits of axes.

all_axes := Jords join orb_15 join orb_15_twins join orb_15_new join orb_15_new_twins join orb_45;
assert #all_axes eq 106;

// The known automorphism group in the paper is G^\circ.  We call this Gc

Gc_mat := MatrixGroup<151, F | autG_mat, sigma_d>;
Gc := PermutationGroup<106 | [ [Position(all_axes, A!(Vector(all_axes[i])*Matrix(x)) ): i in [1..106]]
                                       : x in Generators(Gc_mat)]>;
assert GroupName(Gc) in {"C2*A6.C2^2", "C2*S6.C2"};
// Recall that Aut(S_6) = Aut(A_6) is isomorphic to A_6.C_2^2 so this is C2xAut(A_6).


// Computation 13.26 (a)
U := Eigenspace(d, 0);
assert Dimension(U) eq 121;

// Computation 13.26 (b)
A_1d := Eigenspace(d, 1);
assert Dimension(A_1d) eq 1;

A_quart_d := Eigenspace(d, 1/4);
assert Dimension(A_quart_d) eq 29;


Ualg := Subalgebra(A, orb_45);
// All this time is Magma's internal subalgebra intrinsic
// takes 550 secs
assert Dimension(Ualg) eq 121;
assert forall{a : a in orb_45| a*d eq A!0};

// Hence orb_45 is in A_0(d) and thus Ualg is U = A_0(d)


// Computation 13.28.
W := A_quart_d;

// Computation 13.28 (a)

bool, ext := HasInducedMap(A, W, IdentityHomomorphism(Ualg));
// takes 480 secs
assert bool;
assert Dimension(ext) eq 1 and IsIdentity(ext.1);

// Computation 13.28 (b)
// We check for a basis
assert forall{ w : w in Basis(W) | A!w*A!w ne A!0};













// Extra
/*
// Try doing the proper thing
new_decomps := [];
for t in Jords join orb_15_twins join orb_15_new join orb_15_new_twins do
  S := [ Eigenspace(t, lm) : lm in [1,0,1/4,1/32]];
  Dt := AxialDecomposition(A, S, t);
  Append(~new_decomps, Dt);
end for;
// takes 60 sec

time AA := AddDecompositions(A, new_decomps);
// Seg fault on checking equality of algebras in the AddDecomposition intrinsic
*/
