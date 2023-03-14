/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an element x of the permutation group form of the Miyamoto group of an axial algebra, determine if it is     +
+ induced by tau or sigma map of an axis. Return the axis if it exists.                                             +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

IsRealisable:=function(A,elt:one:=A!0,form:=IdentityMatrix(BaseField(A),Dimension(A))) /*Input an axial algebra A and a group element elt from the Miyamoto group.*/ 
/*We have an optional input for the identity if it exists, naturally inputting it will speed up things.*/
	n:=Dimension(A);
	x:=elt;
	aut:=ZeroMatrix(BaseField(A),n,n);
	for i:=1 to n do
		v:=(A`Wmod)!((A`W).i);
		aut[i]:=(A`W)!Eltseq(v*x);
	end for;
	eigs:={x[1]:x in Eigenvalues(aut)};
	if not eigs eq  {-1,1} then 
		return "false";
	elif eigs eq {-1,1} then  
		_,ann:=AnnihilatorOfSpace(A,Basis(Eigenspace(aut,-1))); 
		if one eq A!0 then
			bool,one:=HasIdentityAlg(A);
			if bool eq false then
				idemps:=FindAllIdempotents(A, ann:length:=1, form:=form); 
				if #idemps eq 0 then
					return "false",_;
                		elif #idemps ne 0 then 
					return "true",[A!x:x in idemps];
				end if;
			elif bool eq true then 
				one:=A!one;
				idemps:=FindAllIdempotents(A,sub<A`W|A`W!Eltseq(one)>+ann:length:=1,form:=form,one:=one);
				if #idemps eq 0 then
					return "false",_;
                		elif #idemps ne 0 then 
					return "true",[A!x:x in idemps];
				end if;
			end if;
		elif one ne A!0 then 
			idemps:=FindAllIdempotents(A,sub<A`W|A`W!Eltseq(one)>+ann:length:=1,form:=form,one:=one);
			if #idemps eq 0 then
				return "false",_;
                	elif #idemps ne 0 then 
				return "true",[A!x:x in idemps];
			end if;
		end if;
	end if;
end function; 
