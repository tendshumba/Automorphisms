/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+This is the nuanced zero subalgebra version. Take A as input, and optional parameters one, for the algebra identity, + 
+ as well as Frobenius form "form". Including these if known speeds up thngs considerably.                            +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 

FindAutNuanced:=function(A:one:=A!0, form:=IdentityMatrix(BaseField(A), Dimension(A)))
	axes:=Axes(A);
	reps:=[axes[i][1]:i in [1..#axes]];
	reps:=[A!x:x in reps]; 
	axes:=&join[x:x in axes];
	axes:=[A!x:x in axes];
	identities_lengths:=[(2^2*3)/5,2,(2^2*29)/(5*7),(2^5/11),4, 19/5,(2^5)/7,(3*17)/(2*5)];
	types:=["2A","2B","3A","3C","4A","4B","5A","6A"];
	found:=[];
	count:=0;
	for x in reps do
		a:=x;
		count+:=1;
		W:=Eigenspace(AdMat(a),0);
		for i:=1 to 8 do
			l:=(identities_lengths[i])-1;
			if types[i] eq "4A" then
				W32:=Eigenspace(AdMat(a),1/32);
				RR:=PolynomialRing(BaseField(A),Dimension(W));
				FF:=FieldOfFractions(RR); 
				AFF:=ChangeRing(A,FF);
				uu:=&+[RR.i*AFF!W.i:i in [1..Dimension(W)]];
				extra:=Determinant(AdMatInSubAlg(AFF,W32,uu)-(31/32)*IdentityMatrix(BaseField(A),Dimension(W32)));
				idemps:=FindAllIdempotents(A,W:length:=l,one:=one,form:=form,extra_rels:=[extra]);
			elif types[i] ne "4A" then 
				idemps:=FindAllIdempotents(A,W:length:=l,one:=one,form:=form);
			end if; 
			printf "orbit %o %o nice idempotents found\n", count,types[i];
			if not #idemps eq 0 then 
				AA:=ChangeRing(A,BaseField(Parent(idemps[1])));
				aa:=AA!Eltseq(a);
				for u in idemps do
					uu:=AA!Eltseq(u); 
					Z:=Eigenspace(AdMat(aa+uu),1);
					potential_axes:=FindAllIdempotents(AA,Z:length:=1,one:=AA!Eltseq(one),form:=form);
					for y in potential_axes do
						if HasMonsterFusion(y) and not A!Eltseq(y) in found then
							Append(~found, A!Eltseq(y));
						end if;
					end for;
				end for; 
				printf "axes arising from orbit %o, B of type %o found\n",count,types[i];
			end if; 
		end for; 
	 end for; 
	if #found eq #axes then 
		print "nothing new";
	else
		printf "%o new axes found", #found-#axes;
	end if;
	return found;
end function; 
