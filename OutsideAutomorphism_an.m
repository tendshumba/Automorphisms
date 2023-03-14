/*Given an axial algebra A over the rationals whose Miyamoto group is A_n, find an automorphism of order 2 coming from the action 
 of an odd involution. As input, take A and n in that order. We will include a switch which will by default turn off the check at end, 
 but will run it if the extra optional input is set to true.
 */
OuterAut:=function(Alg,n:RunCheck:=false)/*input is the algebra A with Miyamoto group A_n. Specify n also.*/
       A:=Alg;
axes:=Axes(A);
axes:=&join[x:x in axes];
axes:=[A!x:x in axes];
W:=VectorSpace(Rationals(),Dimension(A));
 SS:=SymmetricGroup({(Dimension(A)-#axes)+1..Dimension(A)});/* Here note that by construction (Justin verified), the generating axes ocuppy the last k 
							       positions of the canonical basis, where k is the number of axes.*/
/* G is the corresponding alternating group.*/
G:=Alt(n);
 invs:=[x[3]:x in ConjugacyClasses(G)|x[1] eq 2];
 invs:=[invs[i]^G:i in [1..#invs]]; /*actually we need to iterate over all the conjugacy classes of A_n which are involutions. 
for A_5 providence has it that we have only one.*/
/*	we can can do invs:=&join[x:x in invs];*/
invs:=&join[x:x in invs];

cyc:=Sym(n)!(1,2);
invols:=invs;
actions:= {@<i,Index(invols,(invols[i]^cyc))>:i in [1..#invols]@};
actions:=[x:x in actions|x[1] lt x[2]];/*this gives the conjugation action of cyc on the set  of all axes*/
start:=Dimension(A)-#axes;
outsider:=SS!(actions[1][1]+start, actions[1][2]+start);
outsider*:=&*[SS!(actions[i][1]+start,actions[i][2]+start):i in [2..#actions]];
 outsider;
axes_inds:=[(Dimension(A)-#axes)+1..Dimension(A)];
 unfilled_inds:=[x:x in [1..Dimension(A)]|not x in [(Dimension(A)-#axes)+1..Dimension(A)]];
 mclos:=1 ;
 if #axes eq Dimension(A) then 
	 print "algebra is 1-closed";
 else 
	 mclos+:=1;
 end if;
outside_aut:=ZeroMatrix(Rationals(),Dimension(A),Dimension(A));
found:=[];
for i in axes_inds do 
	outside_aut[i]:=W!(Eltseq(A.(i^outsider)));
	Append(~found,i);
end for;
//while #unfilled_inds gt 0 do 
	for i in axes_inds do 
		for j in axes_inds do 
			if i lt j then 
				prod:=(A.i)*(A.j);
				prod_vec:=W!Eltseq(prod);
				sup:=Support(prod_vec);
			       	if #{x:x in sup|x in unfilled_inds} eq 1 then
					l:=[x:x in sup|x in unfilled_inds][1];
					im:=(A.(i^outsider)*(A.(j^outsider)))-&+[prod_vec[m]*(A!((W!Eltseq(A.m))*outside_aut)):m in sup|m ne l];
					outside_aut[l]:=(W!Eltseq(im))/(prod_vec[l]);
					Append(~found,l);
					unfilled_inds:=[x:x in unfilled_inds|x notin found];
				end if;
			 end if;
		end for;
	end for;
//end while;
	old_found:=found;
	new:=[x:x in found|not x in axes_inds];


	while #unfilled_inds gt 0 do
	       new_found:=[];
	       for i:=new[1] to new[#new] do 
		      for j in axes_inds do
			      prod:=(A.i)*(A.j);
			      prod_vec:=W!Eltseq(prod);
			      sup:=Support(prod_vec);
			      if #{x:x in sup|x in unfilled_inds} eq 1 then 
				      l:=[x:x in sup|x in unfilled_inds][1]; 
				      im:=(A!(W!(Eltseq(A.i))*outside_aut))*(A!((W!(Eltseq(A.j)))*outside_aut))-A!(&+[prod_vec[m]*(W!(Eltseq(A.m))*outside_aut):m in sup|m ne l]);
				      outside_aut[l]:=(W!Eltseq(im))/(prod_vec[l]);
				      Append(~found,l);
				      unfilled_inds:=[x:x in unfilled_inds|x ne l];
			      end if;
		   end for;
	    end for;
	    mclos+:=1;
		    new:=[x:x in found|not x in old_found];
		    old_found:=found;
	end while;

 outside_aut^2 eq Identity(Parent(outside_aut));
 if not RunCheck eq false then 
 forall{x:x in [y:y in CartesianPower( [1..Dimension(A)] ,2)| y[1] le y[2] ]|A!((W!Eltseq((A.(x[1]))*(A.(x[2]))))*outside_aut) eq A!((W!Eltseq(A.(x[1])))*outside_aut)*(A!((W!Eltseq(A.(x[2])))*outside_aut))};/**/
end if;
return outside_aut,mclos;
end function;
