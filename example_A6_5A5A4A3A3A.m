/*

The example for A_6 5A5A4A3A3A

*/
AttachSpec("../DecompAlgs/DecompAlgs.spec");
AttachSpec("../AxialTools/AxialTools.spec");
Attach("../DecompAlgs/AxialTools.m");
Attach("Automorphisms.m");

// Alter this to the path of where your algebra is stored

path := "../DecompAlgs/library/Monster_1,4_1,32/RationalField()/";


// Preliminary data
A := LoadDecompositionAlgebra(path cat "A6/45/5A5A4A3A3A_sub.json");
F := BaseRing(A);
n := Dimension(A);
G0 := MiyamotoGroup(A);
assert GroupName(G0) eq "A6";

// If the algebra is Miyamoto closed, then the Miyamoto group is a permutation group on the axes
axes := Axes(A);
assert forall{ <i, g> : i in [1..#axes], g in Generators(G0) | axes[i]*g eq axes[Image(g,GSet(G0),i)]};

// Computation 13.1 (a) We show that A has no Jordan axes.
assert #JordanAxes(A) eq 0;

// Computation 13.1 (b) The known axes have no twins.
assert #axes eq 45;
axes_reps := AxisOrbitRepresentatives(A);
assert #axes_reps eq 1;
assert #(FindMultiples(axes_reps[1])) eq 1;


Miy_elts := [MiyamotoElement(A, i): i in [1..#axes]];
// Since there are no twins for this set of axes, there is a bijection between the axes and the Miyamoto involutions. Thus, we can find the action of the outer automorphism via its action on the Miyamoto involutions.

// Computation 13.1 (d) We show that the outer automorphisms of G0 induce algebra automorphisms.

aut := AutomorphismGroup(G0);
assert GroupName(OuterFPGroup(aut)) eq "C2^2";
// Thus the outer automorphism has 2 generators. The first gives S_6, while adding the second gives the full automorphism.

outs := {@ x: x in Generators(aut)| not IsInnerAutomorphism(x) @};
assert #outs eq 2;
outs := [ Sym(#axes)![ Position(Miy_elts, Miy_elts[i]@outs[j]) : i in [1..#axes]] : j in [1,2]];
// Thus it is clear that Aut(G0) is A6.C2^2

// We check that each out is indeed an automorphism of A. 
Vaxes := sub<VectorSpace(A) | [Vector(x) : x in axes]>;
out_maps := [ hom<Vaxes->VectorSpace(A) | [<Vector(axes[i]), Vector(axes[i^outs[j]])> : i in [1..45]]>: j in [1..2]];

out_maps := [ out_map : i in [1..2] | so where so, out_map := ExtendMapToAlgebraAutomorphism(A, out_maps[i])];
assert #out_maps eq 2; // So each map did extend to an algebra automorphism.

// We now find the group S6
poss := [ outs[1], outs[2], outs[1]*outs[2] ];
assert exists(o){out : out in poss | IsIsomorphic(PermutationGroup<45|G0, out>, Sym(6)) };
G := PermutationGroup<45| G0, o>;

// Computation 13.1 (c) We will show that the involutions from G=S_6 are not induced by axes. We could actually combine this with Computation 13.2. 
// We seek the involutions of G outside G0
invs_G_diff_G0 := [ x[3] : x in ConjugacyClasses(G)| x[1] eq 2 and x[3] notin G0];
assert #invs_G_diff_G0 eq 2;
outer_maps := [hom<Vaxes -> VectorSpace(A) | Matrix([ Vector(axes[i^g]) : i in [1.. #axes]])> : g in invs_G_diff_G0];

outer_maps := [ phi : i in [1,2] | so where so, phi := ExtendMapToAlgebraAutomorphism(A, outer_maps[i]) ];
assert #outer_maps eq 2; // So both extended

assert forall{phi : phi in outer_maps | not IsInducedFromAxis(A, phi)};
// takes 30 secs
// Hence the two classes of involutions in G\G0 are not induced by axes.


// Computation 13.2
// We will call the group G^\circ in the paper G_c
G_c := PermutationGroup<45 | G, outs>;
assert GroupName(G_c) eq "S6.C2";

// We want involutions in G_c\ G.
invs_Gc_diff_G := [ x : x in ConjugacyClasses(G_c)| x[1] eq 2 and x[3] notin G];
assert #invs_Gc_diff_G eq 1 and (invs_Gc_diff_G)[1][2] eq 36;
// Thus there is a single class of involutions in G_c\ G of size 36

g := invs_Gc_diff_G[1][3];
g_map := hom<Vaxes -> VectorSpace(A) | Matrix([Vector(axes[i^g]) : i in [1.. #axes]])>;
so, g_map := ExtendMapToAlgebraAutomorphism(A, g_map);
assert so;
assert not IsInducedFromAxis(A, g_map);
// takes 30 secs
// Hence the involutions in G_c\G are not induced by axes. 

// We now set up a decomposition with respect to a set of axes generating 2B algebras pairwise and whose tau involutions generate an elementary abelian group 2^2.
a1 := axes[1];
Y := {@ a1 @};
possibles := [x : x in axes | x*a1 eq A!0 ];

so := true;
while so do
  so := exists(b){b : b in possibles | forall{y : y in Y | IsZero(y*b)}};
  if so then
    Include(~Y, b);
  end if;
end while;

assert #Y eq 3;
a2 := Y[2];
a3 := Y[3];

assert Dimension(Subalgebra(A, Y)) eq 3;
E := sub<G_c | [MiyamotoElement(A, Position(axes, y)) : y in Y]>;
assert GroupName(E) eq "C2^2";
N := Normaliser(G_c, E);
assert GroupName(N) eq "C2*S4";


// Computation 13.3 Details of the decomposition.
YD := {@ Decomposition(y) : y in Y @};
decomp := JointPartDecomposition(YD);

// Note here that the keys of the decomposition are indexed by the tuples <i,j,k> where
// 1\le i,j,k\le 4 with 1:->1,0:->2, 1/4:->3 and 1/32:->4.

// Part (a) U_{(0,0,0)}(Y) is indexed by <2,2,2>;

U := decomp[<2, 2, 2>];
assert Dimension(U) eq 19;

// Part (b) The rest of the componets are as follows:

// Part (b) (i) U_{(1,0,0)}(Y)=<a1>, U_{(0,1,0)}(Y)=<a2> and U_{(0,0,1)(Y)=<a3>
// by the map above, these will be indexed <1,2,2>, <2,1,2> and <2,2,1> respectively.

assert forall{t : t in [<1, 2, 2>, <2, 1, 2>, <2, 2, 1>] |Dimension(decomp[t]) eq 1};

/* Part (b) (ii) U_{(0,1/4,1/4)}(Y), U{(1/4,0,1/4)}(Y) and U_{(1/4,1/4,0)}(Y). These are indexed by
   <2,3,3>, <3,2,3> and <3,3,2>, respectively.*/
assert forall{t : t in [<2, 3, 3>, <3, 2, 3>, <3, 3, 2>]|Dimension(decomp[t]) eq 2};

/* Part (b) (iii) U_{(1/4,0,0)}(Y), U{(0,1/4,0)}(Y) and U_{(0,0, 1/4)}(Y). These are indexed by
   <3,2,2>, <2,3,2> and <2,2,3>, respectively.*/
assert forall{t : t in [<3, 2, 2>, <2, 3, 2> ,<2, 2, 3>]|Dimension(decomp[t]) eq 5};

/* Part (b) (iv) U_{(1/4,1/32,1/32)}(Y),U_{(1/32,1/4,1/32)}(Y) and U_{(1/32,1/32,1/4)(Y),
  which are indexed by <3,4,4>,<4,3,4> and <4,4,3>, respectively.*/
assert forall{t : t in [<3, 4, 4>,<4, 3, 4>, <4, 4, 3>]|Dimension(decomp[t]) eq 6};

/* Part (b) (v) U_{(0,1/32,1/32)}(Y),U_{(1/32,0,1/32)}(Y) and U_{(1/32,1/32,0)(Y),
  which are indexed by <2,4,4>,<4,2,4> and <4,4,2>, respectively.*/

assert forall{t : t in  [<2, 4, 4>,<4, 2, 4>, <4, 4, 2>]|Dimension(decomp[t]) eq 20};


// We turn to determining Aut(U).

Ualg, U_inc := Subalgebra(A, Basis(U));
// takes 130 secs

// Computation 13.4

Ws := [ decomp[t] : t in [<2, 3, 3>, <3, 2, 3>, <3, 3, 2>]];
bool, proj := HasProjection(A, U);
assert bool;

bases := [ [ A | v : v in Basis(W)] : W in Ws];
Us := [ Subalgebra(Ualg, [ Vector(A!a*A!b)@proj@@U_inc : a,b in Basis(W) ]) : W in Ws ];

assert forall{ U_i : U_i in Us | Dimension(U_i) eq 3};

zs := [ z : U_i in Us | so where so, z := HasOne(U_i)];
assert forall{z : z in zs | Frobenius(x, x) eq 4 where x is A!(Algebra(A)!z)};
// Length of each identity element of U_i is 4.


// Computation 13.5
// We show that the zs are precisely the only idempotents of length 4 in U.

// ****************************
//
// WARNING: the following takes ~140 hours = 6 days and requires ~132Gb of RAM
length_four_idemps_U := FindAllIdempotents(A, U: length := 4, extend_field := true );
//
// ****************************

assert forall{z : z in zs | A!(Algebra(A)!z) in length_four_idemps_U};
assert #length_four_idemps_U eq 3;
// So that the zs are everything.


// Computation 13.6 (a) The subalgebra generated by the zs is 4-dimensional.

V := Subalgebra(Ualg, zs);
assert Dimension(V) eq 4;

// Computation 13.6 (b) The 1-eigenspaces of the zs are 2-dim
V_1zs := [ Eigenspace(V!zs[i], 1) : i in [1..3]];
assert forall{ V_1z : V_1z in V_1zs | Dimension(V_1z) eq 2};


// Computation 13.6 (c) Each V_1z contains the corresponding z_i, a common idempotent u of length 2, a unique idempotent u_i of length 2, and 0.

idems_Vis := [ FindAllIdempotents(V, V_1z) : V_1z in V_1zs ];

Aalg := Algebra(A);
assert forall{ idems : idems in idems_Vis | {* Frobenius(A!Aalg!x, A!Aalg!x): x in idems *} eq {* 0, 2^^2, 4 *}};
// So each set of idempotents has idempotents of length 0, 2 (twice) and 4, i.e., 4 idempotents.

common := &meet idems_Vis;
assert #common eq 2;
assert exists(u){ u : u in common | not IsZero(u)};
assert Frobenius(A!Aalg!u, A!Aalg!u) eq 2;

// Hence the sets have two common idempotents, 0 and some nonzero one u.

// Computation 13.6 (d)
uis := [ ui where _ := exists(ui){ ui : ui in idems | ui ne u and Frobenius(A!Aalg!ui, A!Aalg!ui) eq 2} : idems in idems_Vis];

assert forall{ ui : ui in uis | IsZero(ui*u)};
assert forall{ i : i in [1..3] | u + uis[i] eq zs[i] };


// Computation 13.7 (a)

assert Eigenvalues(Ualg!u) eq {<1, 1>, <0, 10>, <1/2, 3>, <1/8, 5>};

// Computation 13.7 (b)

_, _, FL := IdentifyFusionLaw(Ualg!u : eigenvalues := {@1, 0, 1/2, 1/8 @} );

assert IsSymmetric(FL);
FL1 := FL!1;
FL2 := FL!2;
FL3 := FL!3;
FL4 := FL!4;

assert forall{ x : x in [FL1, FL3, FL4] | FL1*x eq {x} } and FL1*FL2 eq {} and forall{ x : x in [FL2,FL3, FL4] | FL2*x eq {x}};
assert FL3*FL3 eq {FL1, FL2, FL3}; // So not Monster type, but almost here
assert FL3*FL4 eq {FL4} and FL4*FL4 eq {FL1, FL2, FL3};


// Computation 13.8

W := Eigenspace(Ualg!u, 1/8);
assert Dimension(W) eq 5;

ad_uis := [ Matrix([Coordinates(W, Vector(Ualg!w*Ualg!ui)) : w in Basis(W)]) : ui in uis];
assert forall{ ad : ad in ad_uis | Eigenvalues(ad) eq {<25/168, 1>, <1/168, 2>, <3/56, 1>, <7/24, 1> }};

// Computation 13.9 Frobenius form is nondegenerate on T_is

T_is := [ Eigenspace(ad, 7/24) : ad in ad_uis];

assert forall{T : T in T_is | Dimension(T) eq 1};

bas_W := BasisMatrix(W);
frobs := [ Frobenius(A!x, A!x) where x is (T.1*bas_W)@U_inc : T in T_is ];
assert forall{ f : f in frobs | f ne 0};

// Computation 13.10

nums := [ root : f in frobs | so where so, root := IsSquare(Numerator(f)/15) ];
denoms := [ root : f in frobs | so where so, root := IsSquare(Denominator(f)) ];
assert # nums eq 3 and #denoms eq 3;
// So the frobenius form is 15 times a square.  We now scale.

tis := [ (denoms[i]/nums[i]*T_is[i].1)*bas_W : i in [1..3]];
assert forall{ t : t in tis | Frobenius(A!(t@U_inc), A!(t@U_inc)) eq 15};

// Do part (b) first
// Computation 13.10 (b) The tis generate U.

assert Subalgebra(Ualg, tis) eq Ualg;

// Computation 13.10 (a)

// Coerce into A
tis := [ A | t@U_inc : t in tis];
assert forall{ i : i in [1..2] | forall{ j : j in [i+1..3] | Abs(Frobenius(tis[i], tis[j])) eq 15/8 }};


// Computation 13.13 
// In the paper, we recycled the symbols W_i, i:=1, 2, 3, but to distinguish with the current components, we will use WW_i so WWs

WWs := [decomp[x] : x in [<3, 4, 4>, <4, 3, 4>, <4, 4, 3>]];
id_U := IdentityHomomorphism(Ualg);

// Computation 13.13 (a) The identity map on U has 1-dim spaces of (scalar) extensions on the WW_i

extensions_WWs := [ phi : i in [1..3] | so where so, phi := HasInducedMap(A, WWs[i], id_U) ];
// takes 200 secs
assert #extensions_WWs eq 3;// so that the identity map extends on each WW_i
assert forall{ ext : ext in extensions_WWs | Dimension(ext) eq 1};
assert forall{ ext : ext in extensions_WWs | IsIdentity(ext.1)};
// Hence the WW_is admit extensions which are scalar multiples of the identity map.

// Computation 13.13 (b). The WWs generate A.

assert Subalgebra(A, &cat[ Basis(W): W in WWs]) eq Aalg; 

// Computation 13.14

// We check for all basis vectors

// Computation 13.14 (a) (u, w_i*w_i) nonzero
forall{ <u,w,i> : u in Basis(U), w in Basis(WWs[i]), i in [1..3] | Frobenius((A!w)*(A!w), A!u) ne 0};
// takes 80 secs

// Computation 13.14 (b) (w_1*w_2, w_3) nonzero
frobs := {* Frobenius((A!w1)*(A!w2), A!w3) : w1 in Basis(WWs[1]), w2 in Basis(WWs[2]), w3 in Basis(WWs[3]) *};

assert #frobs eq 216;  // There are 216 different triples
assert Multiplicity(frobs, 0) eq 1; // This might be slightly different with different choices above
